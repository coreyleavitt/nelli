#!/usr/bin/env python3
"""RFC-0005 S8bt (item 5): generate src/nelli/smt/pcre_ucd.nim from PCRE
8.45's own Unicode tables (pcre_ucd.c, pcre_tables.c, ucp.h), so the walker's
UTF-mode property sets and case folding are PCRE's, not hand-written.

Usage: scripts/gen-pcre-ucd.py <pcre-8.45 source dir> > src/nelli/smt/pcre_ucd.nim

For each property name pcre_compile.c accepts (`utt`), the code points
OP_PROP matches (pcre_exec.c's semantics, per type: PT_ANY, PT_LAMP, PT_GC,
PT_PC, PT_SC, PT_ALNUM, PT_SPACE, PT_PXSPACE, PT_WORD, PT_UCNC), as ranges;
`other_case` (UCD_OTHERCASE) and the caseless sets (UCD_CASESET).
"""
import re
import sys

src = sys.argv[1]


def read(name):
    with open(f"{src}/{name}", encoding="latin-1") as f:
        return f.read()


ucd = read("pcre_ucd.c")
tables = read("pcre_tables.c")
ucph = read("ucp.h")


def array_body(text, name):
    # The last definition (pcre_ucd.c starts with empty stand-ins).
    i = text.rindex(name)
    i = text.index("{", i)
    j = text.index("};", i)
    return text[i + 1:j]


def ints(body):
    body = re.sub(r"/\*.*?\*/", "", body, flags=re.S)
    return [int(x, 0) for x in re.findall(r"-?0x[0-9a-fA-F]+|-?\d+", body)]


# ucp.h enums: general categories, particular categories, scripts.
def enum_names(after):
    i = ucph.index(after)
    i = ucph.index("enum {", i)
    j = ucph.index("};", i)
    body = re.sub(r"/\*.*?\*/", "", ucph[i:j], flags=re.S)
    return re.findall(r"ucp_(\w+)", body)


gen = enum_names("These are the general character categories")
part = enum_names("These are the particular character categories")
scripts = enum_names("These are the script identifications")

records_raw = ints(array_body(ucd, "PRIV(ucd_records)[] ="))
records = [tuple(records_raw[k:k + 5]) for k in range(0, len(records_raw), 5)]
stage1 = ints(array_body(ucd, "PRIV(ucd_stage1)[] ="))
stage2 = ints(array_body(ucd, "PRIV(ucd_stage2)[] ="))
cl_body = array_body(ucd, "PRIV(ucd_caseless_sets)[] =")
cl_body = cl_body.replace("NOTACHAR", "-1")
caseless = ints(cl_body)

gentype_body = array_body(tables, "PRIV(ucp_gentype)[] =")
gentype = [gen.index(x) for x in re.findall(r"ucp_(\w+)", re.sub(r"/\*.*?\*/", "", gentype_body, flags=re.S))]

MAXCP = 0x10FFFF


def rec(c):
    return records[stage2[stage1[c >> 7] * 128 + (c & 127)]]


chartype = [0] * (MAXCP + 1)
script = [0] * (MAXCP + 1)
other = [0] * (MAXCP + 1)
caseset = [0] * (MAXCP + 1)
for c in range(MAXCP + 1):
    r = rec(c)
    script[c], chartype[c], _, caseset[c], other[c] = r

HSPACE = {0x09, 0x20, 0xa0, 0x1680, 0x180e, 0x2000, 0x2001, 0x2002, 0x2003,
          0x2004, 0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x202f,
          0x205f, 0x3000}
VSPACE = {0x0a, 0x0b, 0x0c, 0x0d, 0x85, 0x2028, 0x2029}


def member(ptype, value):
    L, N, Z = gen.index("L"), gen.index("N"), gen.index("Z")
    lamp = {part.index("Lu"), part.index("Ll"), part.index("Lt")}
    if ptype == "PT_ANY":
        return lambda c: True
    if ptype == "PT_LAMP":
        return lambda c: chartype[c] in lamp
    if ptype == "PT_GC":
        v = gen.index(value)
        return lambda c: gentype[chartype[c]] == v
    if ptype == "PT_PC":
        v = part.index(value)
        return lambda c: chartype[c] == v
    if ptype == "PT_SC":
        v = scripts.index(value)
        return lambda c: script[c] == v
    if ptype == "PT_ALNUM":
        return lambda c: gentype[chartype[c]] in (L, N)
    if ptype in ("PT_SPACE", "PT_PXSPACE"):
        return lambda c: c in HSPACE or c in VSPACE or gentype[chartype[c]] == Z
    if ptype == "PT_WORD":
        return lambda c: gentype[chartype[c]] in (L, N) or c == 0x5f
    if ptype == "PT_UCNC":
        return lambda c: c in (0x24, 0x40, 0x60) or 0xa0 <= c <= 0xd7ff or c >= 0xe000
    raise SystemExit("unknown type " + ptype)


# utt: names in order, with their (type, value).
names_body = tables[tables.index("PRIV(utt_names)[] ="):]
names_body = names_body[:names_body.index(";")]
names = [m.replace("L_AMPERSAND", "L&") for m in re.findall(r"STRING_(\w+)0", names_body)]
utt_body = re.sub(r"/\*.*?\*/", "", array_body(tables, "PRIV(utt)[] ="), flags=re.S)
utt = re.findall(r"\{\s*\d+,\s*(PT_\w+),\s*(?:ucp_)?(\w+)\s*\}", utt_body)
assert len(utt) == len(names), (len(utt), len(names))


def ranges(pred):
    out = []
    lo = None
    for c in range(MAXCP + 2):
        inside = c <= MAXCP and pred(c)
        if inside and lo is None:
            lo = c
        elif not inside and lo is not None:
            out.append((lo, c - 1))
            lo = None
    return out


# Other cases: runs (lo, hi, delta) of code points whose `other_case`
# offset is the same non-zero delta.
oc_runs = []
for c in range(MAXCP + 1):
    d = other[c]
    if d == 0:
        continue
    if oc_runs and oc_runs[-1][1] == c - 1 and oc_runs[-1][2] == d:
        oc_runs[-1][1] = c
    else:
        oc_runs.append([c, c, d])
# Caseless sets: each set (from its offset in ucd_caseless_sets), and the
# code points whose `caseset` names it.
sets = {}
k = 1
while k < len(caseless):
    m = k
    members = []
    while caseless[m] != -1:
        members.append(caseless[m])
        m += 1
    sets[k] = members
    k = m + 1
set_idx = {off: i for i, off in enumerate(sorted(sets))}
caseset_of = [(c, set_idx[caseset[c]]) for c in range(MAXCP + 1) if caseset[c] != 0]

print("## RFC-0005 S8bt (item 5). GENERATED by scripts/gen-pcre-ucd.py from")
print("## PCRE 8.45's pcre_ucd.c, pcre_tables.c and ucp.h -- do not edit.")
print("##")
print("## `ucdProps`: per property name pcre_compile.c accepts (`\\p{..}`), the")
print("## code points OP_PROP matches (pcre_exec.c's semantics per property")
print("## type), as ranges; then `[:graph:]`, `[:print:]`, `[:punct:]`, the")
print("## special properties (*UCP) compiles those POSIX classes to.")
print("## `ucdOtherCase`: UCD_OTHERCASE as runs (lo, hi, delta): `c + delta`")
print("## for `c` in `lo .. hi` (else `c` itself). `ucdCaseSets`: the caseless")
print("## sets (`ucd_caseless_sets`, in table order); `ucdCaseSetOf`: per code")
print("## point with UCD_CASESET non-zero, its set's index.")
print()
print("const ucdProps*: seq[(string, seq[(int32, int32)])] = @[")
for name, (ptype, value) in zip(names, utt):
    rs = ranges(member(ptype, value))
    body = ", ".join(f"(0x{a:X}'i32, 0x{b:X}'i32)" for a, b in rs)
    print(f'  ("{name}", @[{body}]),')
# The POSIX classes (*UCP) compiles to special properties (pcre_xclass.c).
C, P, S = gen.index("C"), gen.index("P"), gen.index("S")
Zl, Zp, Cf = part.index("Zl"), part.index("Zp"), part.index("Cf")
specials = [
    ("[:graph:]", lambda c: gentype[chartype[c]] != gen.index("Z") and
        (gentype[chartype[c]] != C or (chartype[c] == Cf and c != 0x061c and
         c != 0x180e and not (0x2066 <= c <= 0x2069)))),
    ("[:print:]", lambda c: chartype[c] not in (Zl, Zp) and
        (gentype[chartype[c]] != C or (chartype[c] == Cf and c != 0x061c and
         not (0x2066 <= c <= 0x2069)))),
    ("[:punct:]", lambda c: gentype[chartype[c]] == P or
        (c < 128 and gentype[chartype[c]] == S)),
]
for name, pred in specials:
    rs = ranges(pred)
    body = ", ".join(f"(0x{a:X}'i32, 0x{b:X}'i32)" for a, b in rs)
    print(f'  ("{name}", @[{body}]),')
print("]")
print()
print("const ucdOtherCase*: seq[(int32, int32, int32)] = @[")
for lo, hi, d in oc_runs:
    print(f"  (0x{lo:X}'i32, 0x{hi:X}'i32, {d}'i32),")
print("]")
print()
print("const ucdCaseSets*: seq[seq[int32]] = @[")
for off in sorted(sets):
    print("  @[" + ", ".join(f"0x{c:X}'i32" for c in sets[off]) + "],")
print("]")
print()
print("const ucdCaseSetOf*: seq[(int32, int32)] = @[")
for c, i in caseset_of:
    print(f"  (0x{c:X}'i32, {i}'i32),")
print("]")
