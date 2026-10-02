## RFC-0005 (soundness channels) slice S8v -- S8r's termination remainder.
##
## `checkCapped`'s step 1c asks whether the caps refute the query with no
## sequence theory (`querySolver`'s `seqTheory = false`). With the theory
## off every string function is uninterpreted, so the theory-free query
## also admitted `str.len(x) = -3` and `str.indexof(s, ":", 0) = -7`. When
## the cap's conflict runs through such a value, step 1c is SAT and step 2
## runs the sequence theory under the cap's assumption literal. On Z3
## 4.13.4 (the symex-mingw leg's build) that is a string search: S8r's
## range-checked `>1000`-byte search (below, `tsymex_rfc0005_s8r_theoryfree`
## (2)) spent 58 s and 1.2 GB in it.
##
## Step 1c now adds `seqRangeFacts`: for each such term, the range the
## sequence theory gives it. Each fact holds in every model of the theory
## (pinned below against the theory itself), so the facts never refute a
## real model.
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

proc slast(ctx: Z3Context; s, t: Z3String): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_last_index(ctx.raw, s.raw, t.raw))

proc freeConsts(ctx: Z3Context; f: Z3Bool): seq[Z3AnyAst] =
  var seen: seq[int]
  var stack = @[toAnyAst(f)]
  while stack.len > 0:
    let tm = stack.pop()
    if getAstKind(tm) != akApp: continue
    let args = unpackApp(tm).args
    if args.len == 0 and getSortKind(tm) in {skInt, skSeq} and
       not Z3_is_string(ctx.raw, tm.raw):
      let id = astId(ctx, tm.raw)
      if id notin seen:
        seen.add id
        result.add tm
    for a in args: stack.add a

proc holdsOnSmallDomain(ctx: Z3Context; f: Z3Bool): string =
  ## RFC-0005 S8aw: S8ai's ground half of the links' bar (as
  ## `tsymex_rfc0005_s8ai_semantic.nim`'s helper of the same name): "" when
  ## `f` is `true` under Z3's rewriter on every string over {"a", "\xff"}
  ## of length <= 3 and integer in -1..4 substituted for its constants.
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
      for v in -1 .. 4:
        tos[k] = mkInt(ctx, v).raw
        let r = go(k + 1)
        if r.len > 0: return r
    else:
      for w in strs:
        tos[k] = mkString(ctx, w).raw
        let r = go(k + 1)
        if r.len > 0: return r
    ""
  go(0)

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]): Z3Solver =
  ## The query as step 1c poses it, less the caps: no sequence theory, with
  ## the range facts.
  result = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): result.add f

# ---- (1) the cap refutation of the `indexof` form is theory-free ------------
#
# The walker's query for `findColonRanged`'s RangeDefect (S8r (2)), dumped
# from the walk: the scan lowers to `str.indexof(s, ":", 0)`, the found arm
# is `idx != -1 and idx < len(s)`, and the RangeDefect is `idx` outside
# `0..1000`. With the theory, only a string longer than 1001 bytes
# satisfies it. Theory-free, `idx = -7` did, whatever the cap, so step 1c
# was SAT and step 2 ran.

proc indexofQuery(ctx: Z3Context): tuple[roots: seq[Z3Bool], cap: Z3Bool] =
  let s = mkStringVar(ctx, "s")
  let idx = sidx(ctx, s, mkString(ctx, ":"), mkInt(ctx, 0))
  let byteRe = star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff")))
  result.roots = @[
    matches(s, byteRe),
    mkInt(ctx, 0) < slen(ctx, s),
    not ((idx == mkInt(ctx, -1)) or (idx >= slen(ctx, s))),
    not ((idx >= mkInt(ctx, 0)) and (idx <= mkInt(ctx, 1000)))]
  result.cap = slen(ctx, s) <= mkInt(ctx, 128)

suite "S8v: step 1c carries the sequence functions' ranges":

  test "the indexof query under the 128 cap is UNSAT theory-free (step 1c)":
    let ctx = newContext()
    let (roots, cap) = indexofQuery(ctx)
    let s = stepOneC(ctx, roots & @[cap])
    check s.check() == zsUnsat

  test "companion: without the cap the facts leave it SAT":
    # The query is satisfiable (a 1002-byte string, `:` at 1001): the
    # facts must not refute it.
    let ctx = newContext()
    let (roots, _) = indexofQuery(ctx)
    check stepOneC(ctx, roots).check() == zsSat

  test "companion: the empty needle at len(s) is not refuted":
    # `str.indexof(s, "", len(s)) = len(s)`: the bound is `<= len(s)` less
    # the needle's length, not `< len(s)`.
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let r = sidx(ctx, s, mkString(ctx, ""), slen(ctx, s))
    check stepOneC(ctx, @[r == slen(ctx, s)]).check() == zsSat

  test "each range fact is valid in the sequence theory; each link is true":
    # A fact is sound iff it is TRUE of the theory (then a theory-free UNSAT
    # stays the query's own). Two bars, by kind (RFC-0005 S8aw):
    #   - a RANGE fact (one function's range, what each term emits alone)
    #     is held to the strict one: Z3 refutes its negation WITH the
    #     theory. Each is a one-function bound Z3 decides at once, so the
    #     strict bar costs nothing and catches a wrong bound at the source;
    #   - a LINK (a fact over two functions, what the terms emit only
    #     together: here S8aw's join, `indexof >= 0 -> indexof <= last`) is
    #     held to S8ai's bar: its negation is never SAT, and it is true on
    #     every small ground instance. Z3 does not decide the
    #     `str.indexof`/`seq.last_indexof` combination (S8aq, S8aw: twelve
    #     forms, up to 10M units), so the strict bar would reject a true
    #     fact for the solver's incompleteness, not for unsoundness. Its
    #     truth is enumerated exhaustively in
    #     `tsymex_rfc0005_s8aw_remainder.nim`, as are S8ai's own links.
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = mkStringVar(ctx, "t")
    let i = mkIntVar(ctx, "i")
    let terms = @[slen(ctx, s) >= mkInt(ctx, 0),
                  sidx(ctx, s, t, i) >= mkInt(ctx, -2),
                  slast(ctx, s, t) >= mkInt(ctx, -2)]
    var ranges: seq[string]
    for term in terms:
      for f in seqRangeFacts(ctx, @[term]):
        ranges.add $f
    let facts = seqRangeFacts(ctx, terms)
    check ranges.len >= 3
    var links = 0
    for f in facts:
      checkpoint $f
      if $f in ranges:
        check querySolver(ctx, [not f], 1_000_000'u).check() == zsUnsat
      else:
        inc links
        check querySolver(ctx, [not f], 1_000_000'u).check() != zsSat
        check holdsOnSmallDomain(ctx, f).len == 0
    check links == 1

# ---- (2) end to end: S8r's range-checked search -----------------------------
#
# Same verdict as S8r (2), the recorded `maxSeqLen` decline; now decided by
# step 1c. Under a `seqQueryRLimit` too small for step 2's search, a step 2
# decline would say its UNSAT "was not decided"; step 1c's does not.

proc findColonRanged(s: string, offset: int): range[0..1000] =
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return i
    i = i + 1
  return i

proc callerRanged(s: string) =
  let p = findColonRanged(s, 0)
  if p > 1000:
    symexTarget("s8v_impossible")

suite "S8v: the range-checked search declines without step 2":

  test "the >1000-byte witness is a maxSeqLen decline from step 1c":
    proc tight(): SymexSettings =
      result = defaultSymexSettings()
      result.budget.seqQueryRLimit = 200_000
    let r = symexFind(callerRanged, tLabel("s8v_impossible"), tight())
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var capped = false
    for e in r.errors:
      check e.severity != sevError or e.kind == beSolverUndef
      if e.kind == beSolverUndef and "maxSeqLen" in e.msg:
        capped = true
        check "was not decided" notin e.msg
    check capped

# ---- (3) an UNSAT the facts alone give is the query's own --------------------
#
# The loop scan's closed form clamps at `s.len`, so `i > s.len` is UNSAT
# with the theory; theory-free it needs `str.indexof`'s upper bound. With
# the facts asserted only beside the caps, step 1c's UNSAT read as the
# cap's and this came back a `maxSeqLen` decline on Z3 4.13.4 (the
# symex-mingw leg; `tsymex_q1_scanlift` Q1-1b and the other scan-lift UNSAT
# companions). The facts are now checked without the caps first.

proc scanPastLen(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i > s.len:
    symexTarget("s8v_past_len")

suite "S8v: the facts' own refutation is UNSAT, not a cap decline":

  test "a scan index past s.len is sxUnsat":
    let r = symexFind(scanPastLen, tLabel("s8v_past_len"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

suite "S8v: walker version floor":
  test "symexWalkerVersion >= 173":
    check parseInt(symexWalkerVersion) >= 173
