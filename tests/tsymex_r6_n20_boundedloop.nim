## N20 (RFC-chapulin-hardening bucket-2, walker v121) — k-unroll decline
## misclassification.
##
## Ledger text: "k-unroll fallback reports beBudgetExhausted even when
## assumed iterations fit under maxLoopUnwind (structural; the closed forms
## exist to route around it)."
##
## REPRODUCED (`isWhile`'s walker arm, `runtime.nim`): the plain while-loop
## k-unroll never checks feasibility of the continue-branch's accumulated
## path condition per iteration — it structurally forks BOTH the continue
## and exit branches at every one of `maxLoopUnwind` iterations regardless
## of whether the continue branch is provably infeasible under the
## accumulated `pc`. So `active.len > 0` after the unwind loop fires even
## for a loop whose trip count a `symexAssume` call has ALREADY bounded well
## under `maxLoopUnwind` — reproduced concretely below with
## `symexAssume(n < 3)` against the default `maxLoopUnwind = 5`.
##
## DIAGNOSIS: this is a STRUCTURAL limitation, not a soundness bug — the
## verdict (`r.status`) stays CORRECT either way (this engine's
## classified-degrade discipline, Invariant 3, never trades soundness for
## precision). The genuine fix — a per-iteration `trySolve`/`s.check()` call
## on the continue-branch's path condition, pruning it when provably UNSAT —
## would multiply Z3 calls by `maxLoopUnwind × active-path-count` for EVERY
## plain while-loop in EVERY run. Traced this engine's OWN solver-call
## discipline to confirm that would be a genuine departure, not an
## extension: `trySolve` calls are deliberately deferred to path-TERMINAL
## points only (the final witness/target check, `routeRaise`'s defect
## routing) — no other walk arm (including `isIndex`'s own defect fork,
## `forkDefect`) calls the solver MID-WALK; every fork, everywhere, builds
## Z3 terms and defers solving to the end. Per-iteration pruning inside
## `isWhile` would be the FIRST such call in this engine, and the closed-
## form scan recognizers (Q1/B0/B3/B4/B6) exist SPECIFICALLY to give
## recognized shapes a cheap, quantifier-free, solver-free EXACT encoding
## instead — this engine's chosen alternative to per-iteration solving.
##
## FIX SHIPPED (classification, not the solver-check route): a NEW
## `SymexErrorKind`, `beBudgetExhaustedAssumedBound` (types.nim; see its own
## extensive doc comment for the full mechanism), reported INSTEAD OF the
## plain `beBudgetExhausted` when a parse-time, purely LEXICAL, zero-Z3-call
## check (`collectAssumedLoopBound`/`collectAssumedBoundVars`,
## dsl_parser.nim — mirrors the established `collectIntOffsetParams`-style
## proc-scoped pre-pass idiom) finds that the while-loop's guard references
## a variable ALSO constrained by a preceding `symexAssume` in the same proc
## body. STATUS/SOUNDNESS BEHAVIOR IS IDENTICAL either way — both kinds
## `sevError` -> `sxUnknown`-taint the SAME paths the SAME way; only the
## diagnostic MESSAGE and KIND differ, letting a caller/auditor distinguish
## "an assumed bound exists but the k-unroll structurally can't use it"
## from "no assumed bound exists at all, genuinely unbounded."
##
## SEEDED FOR A FUTURE ROUND (not shipped here — see the diagnosis above):
## a per-iteration solver-check design, e.g. `isWhile`'s continue-branch
## `trySolve`-checked before adding to `nextActive`, gated by a NEW
## resource-budget setting (mirroring `maxVariantConstructorForks`'s own
## structural-budget-before-solver-work precedent) so it never fires
## unconditionally on every loop — a genuine engine-architecture round, not
## a bucket-2 slice item.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc boundedLoopSat(n: int) =
  symexAssume(n >= 0 and n < 3)
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if acc == n:
    symexTarget("bounded_hit")

proc unboundedLoop(n: int) =
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if acc > 100:
    symexTarget("unbounded_never")

proc magnitudeUselessAssumeLoop(n: int) =
  ## Item 5 (round-6 fix round 3, documented tradeoff): `collectAssumedLoopBound`
  ## is a purely LEXICAL name-match — it has no notion of the assumed bound's
  ## MAGNITUDE relative to `maxLoopUnwind`. `n < 1_000_000` against the
  ## default `maxLoopUnwind = 5` is, in practice, no bound at all for this
  ## loop's k-unroll — the guard is still trivially satisfiable at depth 5 —
  ## yet the guard variable `n` textually appears in a preceding
  ## `symexAssume`, so `wHasAssumedBound` is still set and the walker still
  ## reports `beBudgetExhaustedAssumedBound`, not the plain kind. This is the
  ## documented misfire mode (types.nim's `beBudgetExhaustedAssumedBound` doc,
  ## "a variable-name match, not a provable-bound derivation") captured as
  ## EXPECTED behavior, not a bug to fix.
  symexAssume(n >= 0 and n < 1_000_000)
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if acc > 100:
    symexTarget("magnitude_useless_never")

suite "N20 — k-unroll decline misclassification":
  test "an assumed-bounded loop (n < 3, maxLoopUnwind = 5) still proves sxSat":
    ## The STATUS is correct regardless of the classification bug — the
    ## target is genuinely reachable within the explored depth.
    let r = symexFind(boundedLoopSat, tLabel("bounded_hit"))
    check r.status == sxSat
    let n = r.witness[0]
    check n >= 0 and n < 3

  test "the exhaustion classification distinguishes assumed-bounded from genuinely unbounded":
    let r = symexFind(boundedLoopSat, tLabel("bounded_hit"))
    check r.status == sxSat
    # The k-unroll's own structural exhaustion still fires (that mechanism
    # is unchanged — this slice reclassifies it, does not remove it), but it
    # reports the ASSUMED-BOUND-aware kind, not the plain one.
    var sawAssumedBoundKind = false
    var sawPlainKind = false
    for e in r.errors:
      if e.kind == beBudgetExhaustedAssumedBound: sawAssumedBoundKind = true
      if e.kind == beBudgetExhausted: sawPlainKind = true
    check sawAssumedBoundKind
    check not sawPlainKind

  test "a genuinely unbounded loop keeps the OLD plain classification (no regression)":
    let r = symexFind(unboundedLoop, tLabel("unbounded_never"))
    check r.status == sxUnknown
    var sawPlainKind = false
    var sawAssumedBoundKind = false
    for e in r.errors:
      if e.kind == beBudgetExhausted: sawPlainKind = true
      if e.kind == beBudgetExhaustedAssumedBound: sawAssumedBoundKind = true
    check sawPlainKind
    check not sawAssumedBoundKind

  test "documented tradeoff: a magnitude-useless assume (n < 1_000_000 vs maxLoopUnwind = 5) still gets the assumed-bound kind":
    ## Pins the misfire mode this round's item 5 documents rather than fixes:
    ## the lexical heuristic cannot tell "assumed bound tight enough to
    ## matter" from "assumed bound present but practically unbounded for
    ## this unroll depth." Status stays sxUnknown either way (Invariant 3);
    ## only the diagnostic kind is affected, and it stays the assumed-bound
    ## one here even though the assumption does nothing to shrink the
    ## explored trip-count space.
    let r = symexFind(magnitudeUselessAssumeLoop, tLabel("magnitude_useless_never"))
    check r.status == sxUnknown
    var sawAssumedBoundKind = false
    var sawPlainKind = false
    for e in r.errors:
      if e.kind == beBudgetExhaustedAssumedBound: sawAssumedBoundKind = true
      if e.kind == beBudgetExhausted: sawPlainKind = true
    check sawAssumedBoundKind
    check not sawPlainKind

  test "walker version floor >= 121 (N20 classification)":
    check parseInt(symexWalkerVersion) >= 121
