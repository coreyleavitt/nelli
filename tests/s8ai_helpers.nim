## Shared by `tsymex_rfc0005_s8ai_semantic` and its `_b`, by `include`.
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

const decls = """
(declare-const s String) (declare-const t String) (declare-const u String)
(declare-const x String) (declare-const y String) (declare-const z String)
(declare-const a String) (declare-const b String) (declare-const r String)
(declare-const n Int) (declare-const i Int) (declare-const j Int)
"""

proc q(ctx: Z3Context; src: string): seq[Z3Bool] =
  ## The assertions of `src`, over the constants of `decls` (the same ASTs
  ## `mkStringVar` / `mkIntVar` build for those names).
  parseSmt2String(ctx, decls & src)

proc slen(ctx: Z3Context; s: Z3String): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, s.raw))

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]; caps: seq[Z3Bool] = @[]):
    Z3Status =
  ## The query as step 1c poses it: no sequence theory, with the facts
  ## (built from the query alone, as `checkCapped` does), and the caps.
  let s = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): s.add f
  for c in caps: s.add c
  s.check()

proc capAt(ctx: Z3Context; names: varargs[string]): seq[Z3Bool] =
  for nm in names: result.add slen(ctx, mkStringVar(ctx, nm)) <= mkInt(ctx, 128)

proc freeConsts(ctx: Z3Context; f: Z3Bool): seq[Z3AnyAst] =
  ## The uninterpreted Int / sequence constants of `f`, each once.
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

proc factFlaw(ctx: Z3Context; f: Z3Bool; domain: seq[Z3Bool] = @[]): string =
  ## "" when `f` passes both validity checks against the linked Z3's own
  ## semantics: its negation (beside the byte-domain roots `domain`) is
  ## never SAT with the sequence theory, and it is `true` on every small
  ## ground instance (`holdsOnSmallDomain`). Otherwise what failed.
  let r = querySolver(ctx, domain & @[not f], 1_000_000'u).check()
  let cex = holdsOnSmallDomain(ctx, f)
  if r == zsSat or cex.len > 0:
    return $f & " -> " & $r & ", ground: " & cex
  ""

proc invalidFacts(ctx: Z3Context; roots: seq[Z3Bool];
                  domain: seq[Z3Bool] = @[]): tuple[n: int, bad: seq[string]] =
  ## Each fact `seqRangeFacts` emits for `roots` must hold in every model
  ## of the query, so a theory-free UNSAT stays the query's own.
  let facts = seqRangeFacts(ctx, roots)
  result.n = facts.len
  for f in facts:
    let flaw = factFlaw(ctx, f, domain)
    if flaw.len > 0: result.bad.add flaw
