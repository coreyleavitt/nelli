#!/usr/bin/env python3
"""RFC-0016 K9e: the mutant generator for the pin-strength measurement.

Enumerates mutation sites in the walker's integer arithmetic and raise arms
(the lowering in `src/nelli/smt/lower_expr.nim`, the raise drains in
`src/nelli/smt/walk_expr.nim`) and applies one mutant to a scratch copy of the
tree. The measurement (`scripts/pin-strength.sh`) asks, per mutant, whether
some pin suite of `tests/0016-pinstrength.suites` fails on it.

A mutant is a scope (a named routine, or one arm of one), a rule and a site.
Its id is a hash of the scope, the rule, the stripped text of the line, that
text's occurrence number within the scope and the match number within the
line -- never a line number or a file -- so an edit elsewhere in a source, or
a scope moving to another module, leaves every id unchanged, and an edit to a mutated line retires that line's ids
(and mints new ones) instead of silently pointing them at other code.

Usage:
  pin-strength-mutants.py list  [ROOT]          # TSV: id kind scope line text
  pin-strength-mutants.py apply ID [ROOT]       # mutate ROOT in place; print
                                                #   the source it edited
  pin-strength-mutants.py show  ID [ROOT]       # print the one-line diff

ROOT defaults to the repository this script lives in. The generator is
deterministic: the same sources give the same list in the same order. Each
scope names the one source it lives in; a scope that moves fails the list
loudly (`scope X not found in F`) until its entry names the new module.
"""
import hashlib
import re
import sys
from pathlib import Path

LOWER = "src/nelli/smt/lower_expr.nim"
WALK = "src/nelli/smt/walk_expr.nim"

# The scopes: (name, source, start regex, end regex or None for "the next
# top-level line"). Every routine here lowers integer arithmetic or a comparison, bounds
# a width, or deposits / drains an arithmetic or range raise.
SCOPES = [
    ("truncDivInt", LOWER, r"^proc truncDivInt\*?\(", None),
    ("arithInt", LOWER, r"^proc arithInt\*?\(", None),
    ("cmpInt", LOWER, r"^proc cmpInt\*?\(", None),
    ("cmpBV", LOWER, r"^template cmpBV\*?\(", None),
    ("divBV", LOWER, r"^template divBV\*?\(", None),
    ("modBV", LOWER, r"^template modBV\*?\(", None),
    ("divisorIsZero", LOWER, r"^proc divisorIsZero\*?\(.*=\s*$", None),
    ("overflowCond", LOWER, r"^proc overflowCond\*?\(.*=\s*$", None),
    ("intBounds", LOWER, r"^proc intBounds\*?\(.*=\s*$", None),
    ("overflowCondInt", LOWER, r"^proc overflowCondInt\*?\(", None),
    ("divLowByMinusOne", LOWER, r"^proc divLowByMinusOne\*?\(", None),
    ("intWindow", LOWER, r"^proc intWindow\*?\(", None),
    ("wrapIntToWidth", LOWER, r"^proc wrapIntToWidth\*?\(", None),
    ("depositSignedOverflow", LOWER, r"^proc depositSignedOverflow\*?\(", None),
    ("lowerArith", LOWER, r"^proc lowerArith\*?\(", None),
    ("lowerCmp", LOWER, r"^proc lowerCmp\*?\(", None),
    ("lowerConvIntRange", LOWER, r"^proc lowerConvIntRange\*?\(", None),
    ("lowerExpr.uNeg", LOWER, r"^    of uNeg:\s*$", r"^    of uNot:\s*$"),
    ("drain.DivByZero", WALK, r"^genRaiseForkDrain\(drainDivByZeroRaises,", None),
    ("drain.Overflow", WALK, r"^genRaiseForkDrain\(drainOverflowRaises,", None),
    ("drain.Range", WALK, r"^genRaiseForkDrain\(drainRangeRaises,", None),
]

# Line rules: (kind, regex, replacement). Applied to the code part of a line
# (its trailing comment removed); each match is one mutant.
ARITH = [
    ("arith:+>-", r"(?<=\S)\s+\+\s+(?=\S)", " - "),
    ("arith:->+", r"(?<=[\w)\]]) - (?=\S)", " + "),
    ("arith:*>+", r"(?<=\S)\s+\*\s+(?=\S)", " + "),
    ("arith:`+`>`-`", r"`\+`", "`-`"),
    ("arith:`-`>`+`", r"`-`", "`+`"),
    ("arith:`*`>`+`", r"`\*`", "`+`"),
]
CMP = [
    ("cmp:<><=", r"(?<=\S)\s+<\s+(?=\S)", " <= "),
    ("cmp:<=><", r"(?<=\S)\s+<=\s+(?=\S)", " < "),
    ("cmp:>>>=", r"(?<=\S)\s+>\s+(?=\S)", " >= "),
    ("cmp:>=>>", r"(?<=\S)\s+>=\s+(?=\S)", " > "),
    ("cmp:==>!=", r"(?<=\S)\s+==\s+(?=\S)", " != "),
]
BV = [
    # strictness
    ("bv:slt>sle", r"\bbvslt\b", "bvsle"), ("bv:sle>slt", r"\bbvsle\b", "bvslt"),
    ("bv:sgt>sge", r"\bbvsgt\b", "bvsge"), ("bv:sge>sgt", r"\bbvsge\b", "bvsgt"),
    ("bv:ult>ule", r"\bbvult\b", "bvule"), ("bv:ugt>uge", r"\bbvugt\b", "bvuge"),
    # signedness
    ("sign:sdiv>udiv", r"\bbvsdiv\b", "bvudiv"), ("sign:udiv>sdiv", r"\bbvudiv\b", "bvsdiv"),
    ("sign:srem>urem", r"\bbvsrem\b", "bvurem"), ("sign:urem>srem", r"\bbvurem\b", "bvsrem"),
    ("sign:slt>ult", r"(?<=, )bvslt\b", "bvult"), ("sign:sge>uge", r"(?<=, )bvsge\b", "bvuge"),
    ("sign:if-s", r"\bif (useSigned|s):", r"if not \1:"),
]
BOUND = [
    ("bound:low+1", r"\blow\((u?int\d*)\)", r"(low(\1) + 1)"),
    ("bound:high-1", r"\bhigh\((u?int\d*)\)", r"(high(\1) - 1)"),
    ("bound:-1>1", r"(mkBitVec\[\d+\]\(|mkZ3IntLit\()-1\)", r"\g<1>1)"),
    ("bound:shl-1", r"\(1'i64 shl (w|width|tgtWidth)\) - 1", r"(1'i64 shl \1) - 2"),
]
LOGIC = [
    ("logic:or>and", r"(?<=\S) or (?=\S)", " and "),
    ("logic:drop-not", r"\bnot (?=(add|sub|mul)No(Over|Under)flow\()", ""),
]
DEFECT = [
    ("defect:DivByZero>Overflow", r'"DivByZeroDefect"', '"OverflowDefect"'),
    ("defect:Overflow>DivByZero", r'"OverflowDefect"', '"DivByZeroDefect"'),
    ("defect:Range>Overflow", r'"RangeDefect"', '"OverflowDefect"'),
]
LINE_RULES = ARITH + CMP + BV + BOUND + LOGIC + DEFECT

# Which rule families each scope gets (others are noise there: a `<` in a
# Nim-side interval guard of a discharger, say, is not an encoding).
FAMILIES = {
    "truncDivInt": ARITH + CMP + LOGIC,
    "arithInt": ARITH,
    "cmpInt": CMP,
    "cmpBV": BV,
    "divBV": BV,
    "modBV": BV,
    "divisorIsZero": CMP,
    "overflowCond": LOGIC + ARITH,
    "intBounds": BOUND,
    "overflowCondInt": ARITH + CMP + LOGIC,
    "divLowByMinusOne": BOUND + LOGIC,
    "intWindow": BOUND + ARITH,
    "wrapIntToWidth": ARITH + CMP + LOGIC,
    "depositSignedOverflow": [],
    "lowerArith": ARITH,
    "lowerCmp": BV,
    "lowerConvIntRange": BOUND + CMP,
    "lowerExpr.uNeg": [],
    "drain.DivByZero": DEFECT,
    "drain.Overflow": DEFECT,
    "drain.Range": DEFECT,
}

# The walker's integer families are spelled once per width (8, 16, 32, 64)
# in these scopes; the outer widths stand for the family, so a line naming a
# middle width is not mutated (it would double the count for one shape).
WIDTH_REPLICATED = {"overflowCond", "divBV", "modBV", "cmpBV", "divLowByMinusOne",
                    "divisorIsZero", "intBounds"}
MIDDLE_WIDTH = re.compile(r"bv16|bv32|\[16\]|\[32\]|int16|int32|^of 16:|^of 32:")

# Only these lines of a scope take the line rules (the rest of the scope is
# dispatch on kinds, where an operator is not an encoding).
LINE_FILTER = {
    "lowerConvIntRange": re.compile(r"mkZ3IntLit\(lo\)|shl w\) - 1|high\(int64\)\)"),
}

# Statement rules (dropped forks), per scope.
#  drop:deposit       a raise condition is never deposited: its
#                     `sync<Sink>Cond(c)` (the sink's one store, the walk's
#                     `LowerSinks` field) becomes `discard c`
#  drop:branch        an `if`/`elif` guard of a raise, a check or a wrap never
#                     holds (`false and ...`); the guard is read up to its `:`
#                     and must have no top-level `or`
#  drop:force-return  an early-return guard before a fork always returns
DROP_ADD_SCOPES = {"lowerArith", "depositSignedOverflow", "lowerConvIntRange"}
DROP_BRANCH = {
    "lowerArith": re.compile(r"op in \{bDiv, bMod\} and a\.kind notin|op in \{bAdd, bSub, bMul\}"
                             r"|signedOp and|lowAns\.kind == dkDefect|unsignedDiv|r\.ziWidth in"),
    "lowerExpr.uNeg": re.compile(r"[sS]igned"),
    "lowerConvIntRange": re.compile(r"conds\.len > 0"),
}
FORCE_RETURN_SCOPES = {"wrapIntToWidth", "depositSignedOverflow"}


def code_part(line):
    """The line without its trailing comment (a `#` outside a string)."""
    out, q = [], False
    for i, ch in enumerate(line):
        if ch == '"' and (i == 0 or line[i - 1] != "\\"):
            q = not q
        if ch == "#" and not q:
            break
        out.append(ch)
    return "".join(out).rstrip()


def find_scope(name, start, end, lines, src):
    """(first, past-last) line index of scope `name` in the source `src`."""
    rx = re.compile(start)
    starts = [i for i, l in enumerate(lines) if rx.search(l)]
    # A forward declaration has no body: take the last definition.
    if not starts:
        raise SystemExit(f"pin-strength-mutants: scope {name} not found in {src}")
    s = starts[-1]
    e = s + 1
    if end:
        erx = re.compile(end)
        while e < len(lines) and not erx.search(lines[e]):
            e += 1
    else:
        while e < len(lines):
            l = lines[e]
            if l and not l[0].isspace() and not l.startswith("#"):
                break
            e += 1
    return s, e


def mutant_id(scope, kind, text, occ, k):
    h = hashlib.sha256(f"{scope}|{kind}|{text}|{occ}|{k}".encode()).hexdigest()[:10]
    return f"m{h}"


def enumerate_mutants(sources):
    """[(id, kind, scope, source, line_index, {line_index: new_line})] in
    scope order, then line order. `sources` maps a source path (relative to
    the root) to its lines."""
    out = []
    src = None

    def add(scope, kind, stripped, occ, k, i, edits):
        out.append((mutant_id(scope, kind, stripped, occ, k), kind, scope, src, i, edits))

    for scope, src, start, end in SCOPES:
        lines = sources[src]
        s, e = find_scope(scope, start, end, lines, src)
        seen = {}
        for i in range(s, e):
            raw = lines[i]
            stripped = raw.strip()
            if not stripped or stripped.startswith("#"):
                continue
            code = code_part(raw)
            if not code.strip():
                continue
            occ = seen.get(stripped, 0)
            seen[stripped] = occ + 1
            tail = raw[len(code):]
            ind = code[: len(code) - len(code.lstrip())]
            body = code.strip()
            # header lines (the signature) are not mutated
            if i == s and scope != "lowerExpr.uNeg" and not scope.startswith("drain."):
                continue
            if scope in WIDTH_REPLICATED and MIDDLE_WIDTH.search(body):
                continue
            # a `doAssert` is the routine's own precondition, not an encoding
            if body.startswith("doAssert"):
                continue
            if scope not in LINE_FILTER or LINE_FILTER[scope].search(body):
                for kind, rx, rep in FAMILIES[scope]:
                    for k, m in enumerate(re.finditer(rx, code)):
                        new = code[:m.start()] + m.expand(rep) + code[m.end():]
                        if new != code:
                            add(scope, kind, stripped, occ, k, i, {i: new + tail})
            if scope in DROP_ADD_SCOPES:
                m = re.fullmatch(r"sync\w+Cond\((.+)\)", body)
                if m:
                    edits = {i: f"{ind}discard ({m.group(1)})" + tail}
                    add(scope, "drop:deposit", stripped, occ, 0, i, edits)
            if scope in DROP_BRANCH:
                m = re.match(r"(if|elif) ", body)
                if m:
                    one = re.match(r"(?:if|elif) (.+?):\s+\S", body)
                    cond, j, closed = body, i, True
                    if one:  # a one-line `if c: e`: the guard is `c`
                        cond = one.group(1)
                    else:
                        while not code_part(lines[j]).rstrip().endswith(":") and j + 1 < e:
                            j += 1
                            cond += " " + code_part(lines[j]).strip()
                        closed = code_part(lines[j]).rstrip().endswith(":")
                    if " or " not in cond and closed and DROP_BRANCH[scope].search(cond):
                        new = ind + m.group(1) + " false and " + body[len(m.group(0)):]
                        add(scope, "drop:branch", stripped, occ, 0, i, {i: new + tail})
            if scope in FORCE_RETURN_SCOPES:
                m = re.fullmatch(r"if (.+):", body)
                nxt = next((code_part(lines[j]).strip() for j in range(i + 1, e)
                            if code_part(lines[j]).strip()), "")
                if m and nxt.startswith("return"):
                    add(scope, "drop:force-return", stripped, occ, 0, i, {i: f"{ind}if true:" + tail})
    ids = [o[0] for o in out]
    if len(ids) != len(set(ids)):
        dup = sorted({x for x in ids if ids.count(x) > 1})
        raise SystemExit(f"pin-strength-mutants: id collision {dup}")
    return out


def load(root):
    """Each scope's source, read once: {relative path: lines}."""
    return {src: (Path(root) / src).read_text().split("\n")
            for src in dict.fromkeys(src for _, src, _, _ in SCOPES)}


def main(argv):
    if len(argv) < 2 or argv[1] not in ("list", "apply", "show"):
        print(__doc__, file=sys.stderr)
        return 2
    cmd = argv[1]
    default_root = Path(__file__).resolve().parent.parent
    if cmd == "list":
        root = argv[2] if len(argv) > 2 else default_root
        sources = load(root)
        for mid, kind, scope, src, i, edits in enumerate_mutants(sources):
            print(f"{mid}\t{kind}\t{scope}\t{i + 1}\t{sources[src][i].strip()[:100]}")
        return 0
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    want = argv[2]
    root = argv[3] if len(argv) > 3 else default_root
    sources = load(root)
    for mid, kind, scope, src, i, edits in enumerate_mutants(sources):
        if mid == want:
            lines = sources[src]
            if cmd == "show":
                print(f"{src}:{i + 1} [{scope}] {kind}")
                for j in sorted(edits):
                    print(f"- {lines[j].strip()}\n+ {edits[j].strip()}")
                return 0
            for j, new in edits.items():
                lines[j] = new
            (Path(root) / src).write_text("\n".join(lines))
            print(src)
            return 0
    print(f"pin-strength-mutants: no mutant {want} under {root}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
