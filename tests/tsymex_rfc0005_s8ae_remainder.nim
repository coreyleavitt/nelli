## RFC-0005 (soundness channels) slice S8ae -- S8v's remainder.
##
## `checkCapped`'s step 1c checks a query that step 1 found UNSAT under the
## `maxSeqLen` caps with no sequence theory, plus `seqRangeFacts`: facts
## each valid in the theory. It checks them first without the caps (an
## UNSAT is the query's own), then with them (an UNSAT is the cap's: a
## decline, with no sequence-theory search, RFC-0005 S8r / S8v).
##
## (1) A query refuted only by the theory's relations between two of its
##     functions, such as `str.indexof(s, ":", 0) > 200 and not
##     str.contains(s, ":")`, was a cap decline: theory-free, the `indexof`
##     range fact lets `> 200` through only past the cap, so step 1c's
##     capped check was UNSAT. Before S8r step 2's unsat core decided it.
##     The facts now link the functions (`indexof >= 0` implies `contains`,
##     and so on), so the uncapped fact check refutes it: `sxUnsat`.
##     Running step 2 again behind step 1c under a small `rlimit` was
##     measured and rejected (the RFC's S8ae note): its core names the cap
##     on the `startsWith` and slice shapes below anyway, and `rlimit` does
##     not bound it on a query SAT only past the cap (`s.len > 210 and
##     s[205] == 'x'`: 49 s and 1.2 GB under 200k units on Z3 5.1).
## (2) `str.at`, `str.substr`, `str.to_code` and `str.to_int` had no
##     facts, and a string equal to another term had no length link, so a
##     cap conflict through them was SAT theory-free and reached step 2.
##     `str.len(a ++ b)` needs no fact: Z3's rewriter folds it to
##     `len(a) + len(b)` with the theory off too.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc slen(ctx: Z3Context; s: Z3String): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, s.raw))

proc sidx(ctx: Z3Context; s, t: Z3String; i: Z3Int): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_index(ctx.raw, s.raw, t.raw, i.raw))

proc byteDomain(ctx: Z3Context; s: Z3String): Z3Bool =
  ## As the walker builds it (`allocateSym`'s `itString` arm).
  matches(s, star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff"))))

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]; caps: seq[Z3Bool] = @[]):
    Z3Status =
  ## The query as step 1c poses it: no sequence theory, with the facts
  ## (built from the query alone, as `checkCapped` does), and the caps.
  let s = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): s.add f
  for c in caps: s.add c
  s.check()

proc capAt(ctx: Z3Context; xs: varargs[Z3String]): seq[Z3Bool] =
  for x in xs: result.add slen(ctx, x) <= mkInt(ctx, 128)

proc freeConsts(ctx: Z3Context; f: Z3Bool): seq[Z3AnyAst] =
  ## The uninterpreted constants of `f`, each once.
  var seen: seq[int]
  var stack = @[toAnyAst(f)]
  while stack.len > 0:
    let t = stack.pop()
    if getAstKind(t) != akApp: continue
    let args = unpackApp(t).args
    if args.len == 0 and getSortKind(t) in {skInt, skSeq} and
       not Z3_is_string(ctx.raw, t.raw):
      let id = astId(ctx, t.raw)
      if id notin seen:
        seen.add id
        result.add t
    for a in args: stack.add a

proc holdsOnSmallDomain(ctx: Z3Context; f: Z3Bool): string =
  ## "" when `f` evaluates to `true` (Z3's own rewriter on ground terms)
  ## for every string over {"a", "\xff"} of length <= 3 and every integer
  ## in -1..4 substituted for its constants; else the first instance that
  ## does not.
  var strs = @[""]
  var frontier = @[""]
  for _ in 1 .. 3:
    var next: seq[string]
    for w in frontier:
      for c in ["a", "\xff"]: next.add w & c
    strs.add next
    frontier = next
  let vars = freeConsts(ctx, f)
  if vars.len == 0: return ""
  var froms, tos: seq[RawZ3Ast]
  for v in vars:
    froms.add v.raw
    tos.add v.raw
  proc go(k: int): string =
    if k == vars.len:
      let g = ctx.checkErr Z3_simplify(ctx.raw, ctx.checkErr Z3_substitute(
        ctx.raw, f.raw, cuint(froms.len),
        cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
        cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
      let txt = $Z3_ast_to_string(ctx.raw, g)
      return (if txt == "true": "" else: txt)
    if getSortKind(vars[k]) == skInt:
      for n in -1 .. 4:
        tos[k] = mkInt(ctx, n).raw
        let r = go(k + 1)
        if r.len > 0: return r
    else:
      for w in strs:
        tos[k] = mkString(ctx, w).raw
        let r = go(k + 1)
        if r.len > 0: return r
    ""
  go(0)

proc invalidFacts(ctx: Z3Context; roots: seq[Z3Bool];
                  domain: seq[Z3Bool] = @[]): tuple[n: int, bad: seq[string]] =
  ## Each fact `seqRangeFacts` emits for `roots` must hold in every model
  ## of the query, so a theory-free UNSAT stays the query's own. Two checks,
  ## both against the linked Z3's own semantics. Its negation, beside the
  ## byte-domain roots `domain` (a fact may rest on them: `str.to_code`'s
  ## 255), is never SAT with the theory: Z3 proves most UNSAT, and on free
  ## operands leaves some (a prefix's first index, a piece's index bounds)
  ## unknown within the budget. And it evaluates to `true` on every small
  ## ground instance (`holdsOnSmallDomain`; the byte domain holds there by
  ## construction).
  ## `n` is the number of facts, `bad` each one failing a check.
  let facts = seqRangeFacts(ctx, roots)
  result.n = facts.len
  for f in facts:
    let r = querySolver(ctx, domain & @[not f], 5_000_000'u).check()
    let cex = holdsOnSmallDomain(ctx, f)
    if r == zsSat or cex.len > 0:
      result.bad.add $f & " -> " & $r & ", ground: " & cex

# ---- (1) relational facts: UNSAT through two functions is the query's own --

proc colonPastCap(s: string) =
  if s.find(':') > 200 and ':' notin s:
    symexTarget("s8ae_find_notin")

proc prefixFoundLate(s: string) =
  if s.startsWith("abc") and s.find("abc") > 150:
    symexTarget("s8ae_prefix_find")

proc pieceFoundLate(s: string) =
  if s.len > 3 and s[1..2] == "ab" and s.find("ab") > 150:
    symexTarget("s8ae_piece_find")

proc byteNotContained(s: string) =
  if s.len > 150 and s[140] == ':' and ':' notin s:
    symexTarget("s8ae_byte_notin")

proc colonFoundEarly(s: string) =
  if s.find(':') > 5 and ':' in s:
    symexTarget("s8ae_found_early")

proc concatLong(s, t: string) =
  if (s & t).len > 300:
    symexTarget("s8ae_concat_long")

suite "S8ae (1): UNSAT through the theory's relations is decided":

  test "find > 200 and notin: sxUnsat, not a maxSeqLen decline":
    let r = symexFind(colonPastCap, tLabel("s8ae_find_notin"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "startsWith and a late find of the prefix: sxUnsat":
    let r = symexFind(prefixFoundLate, tLabel("s8ae_prefix_find"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a slice equal to the needle and a late find of it: sxUnsat":
    let r = symexFind(pieceFoundLate, tLabel("s8ae_piece_find"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a byte equal to the needle and notin: sxUnsat":
    # `s[140]` is past the 128 cap: the cap refutes it too, so before this
    # slice it was a decline.
    let r = symexFind(byteNotContained, tLabel("s8ae_byte_notin"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "companion: find > 5 and in is still sxSat":
    let r = symexFind(colonFoundEarly, tLabel("s8ae_found_early"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "companion: a real >128-byte witness stays a maxSeqLen decline":
    let r = symexFind(concatLong, tLabel("s8ae_concat_long"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var capped = false
    for e in r.errors:
      if e.kind == beSolverUndef and "maxSeqLen" in e.msg: capped = true
    check capped

  test "the example query is UNSAT theory-free with the facts, no cap":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let colon = mkString(ctx, ":")
    let roots = @[sidx(ctx, s, colon, mkInt(ctx, 0)) > mkInt(ctx, 200),
                  not contains(s, colon)]
    check stepOneC(ctx, roots) == zsUnsat

  test "each relational fact is valid in the sequence theory":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = mkStringVar(ctx, "t")
    let i = mkIntVar(ctx, "i")
    let j = mkIntVar(ctx, "j")
    let n = mkIntVar(ctx, "n")
    let b = mkBoolVar(ctx, "b")
    let roots = @[
      b == contains(s, t), b == startsWith(s, t), b == endsWith(s, t),
      sidx(ctx, s, t, j) >= mkInt(ctx, -5),
      at(s, i) == t, substr(s, i, n) == t]
    # contains / prefixof / suffixof length bounds (3); index: found ->
    # contains, contains -> found from 0, prefix -> 0 (3); prefix / suffix
    # -> contains (2); at and substr pieces: contains, index (4).
    let (count, bad) = invalidFacts(ctx, roots)
    checkpoint bad.join("; ")
    check count >= 12
    check bad.len == 0

# ---- (2) range facts for at / substr / to_code / to_int / ++ ----------------

suite "S8ae (2): a cap conflict through the other functions is seen":

  test "str.++: x == s & t and len(x) > 300 under the caps on s and t":
    # `str.len(s ++ t)` itself the rewriter folds to `len(s) + len(t)`;
    # a string EQUAL to a concatenation reached no length.
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = mkStringVar(ctx, "t")
    let x = mkStringVar(ctx, "x")
    let roots = @[x == s & t, slen(ctx, x) > mkInt(ctx, 300)]
    check stepOneC(ctx, roots, capAt(ctx, s, t)) == zsUnsat
    check stepOneC(ctx, roots) == zsSat

  test "str.at: s[200] == \"x\" under the 128 cap":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let roots = @[byteDomain(ctx, s), at(s, mkInt(ctx, 200)) == mkString(ctx, "x")]
    check stepOneC(ctx, roots, capAt(ctx, s)) == zsUnsat
    check stepOneC(ctx, roots) == zsSat
    let near = @[byteDomain(ctx, s), at(s, mkInt(ctx, 20)) == mkString(ctx, "x")]
    check stepOneC(ctx, near, capAt(ctx, s)) == zsSat

  test "str.substr: s[150 ..< 153] == \"abc\" under the 128 cap":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let roots = @[substr(s, mkInt(ctx, 150), mkInt(ctx, 3)) == mkString(ctx, "abc")]
    check stepOneC(ctx, roots, capAt(ctx, s)) == zsUnsat
    check stepOneC(ctx, roots) == zsSat

  test "str.to_code: a byte past the cap has no code; a byte is <= 255":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let far = @[byteDomain(ctx, s), toCode(at(s, mkInt(ctx, 200))) >= mkInt(ctx, 0)]
    check stepOneC(ctx, far, capAt(ctx, s)) == zsUnsat
    check stepOneC(ctx, far) == zsSat
    # The byte domain bounds the code: the query's own UNSAT, no cap.
    let i = mkIntVar(ctx, "i")
    check stepOneC(ctx, @[byteDomain(ctx, s),
                          toCode(at(s, i)) > mkInt(ctx, 255)]) == zsUnsat
    # Companion: with no byte-domain root, no upper bound is claimed.
    let u = mkStringVar(ctx, "u")
    check stepOneC(ctx, @[toCode(at(u, i)) == mkInt(ctx, 300)]) == zsSat
    check stepOneC(ctx, @[toCode(at(u, i)) < mkInt(ctx, -1)]) == zsUnsat

  test "str.to_int is at least -1":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    check stepOneC(ctx, @[toInt(s) < mkInt(ctx, -1)]) == zsUnsat
    check stepOneC(ctx, @[toInt(s) == mkInt(ctx, -1)]) == zsSat

  test "each range fact is valid in the sequence theory":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = mkStringVar(ctx, "t")
    let u = mkStringVar(ctx, "u")
    let i = mkIntVar(ctx, "i")
    let n = mkIntVar(ctx, "n")
    let roots = @[
      byteDomain(ctx, s),
      toCode(at(s, i)) >= mkInt(ctx, -7),     # at, to_code (with 255)
      toCode(u) >= mkInt(ctx, -7),            # to_code, no byte bound
      substr(s, i, n) == u,                   # substr, equality
      toInt(t) >= mkInt(ctx, -7),             # to_int
      slen(ctx, s & t) >= mkInt(ctx, 0)]      # len, folded over ++
    let (count, bad) = invalidFacts(ctx, roots, @[byteDomain(ctx, s)])
    checkpoint bad.join("; ")
    check count >= 9
    check bad.len == 0

  test "end to end: (s & t).len > 300 declines from step 1c":
    # Under a `seqQueryRLimit` too small for step 2's search, a step 2
    # decline would say its UNSAT "was not decided"; step 1c's does not.
    proc tight(): SymexSettings =
      result = defaultSymexSettings()
      result.budget.seqQueryRLimit = 200_000
    let r = symexFind(concatLong, tLabel("s8ae_concat_long"), tight())
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var capped = false
    for e in r.errors:
      if e.kind == beSolverUndef and "maxSeqLen" in e.msg:
        capped = true
        check "was not decided" notin e.msg
    check capped

suite "S8ae: walker version floor":
  test "symexWalkerVersion >= 174":
    check parseInt(symexWalkerVersion) >= 174
