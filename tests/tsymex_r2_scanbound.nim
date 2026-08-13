## RFC-chapulin-hardening Q1 hardening — findings R2 (CRITICAL) and R6
## (MEDIUM) against `tryRecognizeScanIdiom` (dsl_parser.nim).
##
## R2: the recognizer matched
##   while <i> < <bound> and <s>[<i>] != <lit>: inc <i>
## and rewrote it to a closed form that evaluates `<bound>` ONCE at loop
## entry -- but the only check on `<bound>` was a TYPE check (`itInt`), never
## a LOOP-INVARIANCE check. `while i < (n - i) and s[i] != 'z': inc i` has a
## REAL guard of `2*i < n` (bound tightens every iteration as `i` grows), but
## was mis-lifted against a FIXED `bound = n` (the value of `n - i` at loop
## entry, where `i == 0`) -- a silently wrong verdict/witness class bug: the
## closed form can report an `i` the real loop can never reach.
##
## Fix: after extracting `iNode` (the counter) and `boundNode` (the `<`
## guard's RHS), the recognizer now rejects the match if `boundNode`'s
## subtree refers to `iNode` at all (`refersToSym`) -- the loop's body shape
## is already constrained to `inc <i>` / `<i> = <i> + 1` (i.e. `i` is the
## ONLY mutated variable), so non-reference to `i` is both necessary and
## sufficient for `boundNode` to be loop-invariant. On rejection the caller
## falls through to the ordinary `mkWhile`/`mkGuardedWhile` k-unroll path --
## sound, just less precise (`sxUnknown` for trip counts beyond
## `maxLoopUnwind`, default 5).
##
## R6: "same variable as `i`" was matched by comparing `.strVal` (the printed
## name) at three sites -- the guard's `s[i]` index, the body's incremented
## variable, and (new, R2) `boundNode`'s reference check. Two DIFFERENT
## symbols that happen to print the same base name (e.g. a gensym'd
## template-injected `i` shadowing an outer loop `i`) would false-match.
## Fix: `sameSym(a, b: NimNode): bool` compares TRUE SYMBOL IDENTITY via the
## stdlib `macros.==(NimNode, NimNode)` (magic `EqNimrodNode`) -- empirically
## confirmed (ad hoc probe against this Nim version, 2.2.10) that two
## references to the SAME binding compare `true`, and two distinct
## same-named bindings in disjoint scopes compare `false`. All three sites
## (plus R2's `refersToSym`) now route through `sameSym`/`refersToSym`
## instead of `.strVal` comparison.
##
## R6 scope note: a genuine same-name-different-symbol NEAR MISS is not
## constructible as a straight-line SUT for THIS recognizer specifically --
## the recognized body shape is constrained to EXACTLY `inc <i>` (a bare
## statement), so a body that shadows `i` via its own `var i = ...`
## declaration is a DIFFERENT body shape (`bodyMatched` already false via the
## existing shape checks, independent of `sameSym`/`.strVal`). R6 is verified
## by (a) the `sameSym` identity probe (see the dsl_parser.nim doc comment
## for the empirical result) and (b) the genuinely-same-symbol case (the
## ordinary hand-written loop) staying green below and in
## tests/tsymex_q1_scanlift.nim's Q1-1/Q1-2 -- proving the tightened checks
## did not regress the common case.
##
## Bumps `symexWalkerVersion` 61->62: R2 makes the recognizer REJECT a
## previously (incorrectly) ACCEPTED mis-lift, changing the verdict for any
## SUT matching this exact near-miss shape. See canonicalize.nim for the
## full changelog entry.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# R2 -- loop-counter-dependent bound must NOT be lifted to a closed form.
# ---------------------------------------------------------------------------

# The real guard is `i < (n - i)`, i.e. `2*i < n`: as `i` grows the bound
# TIGHTENS, so the real loop can advance `i` to at most `ceil(n/2)` before
# the bound stops it. The closed-form rewrite, however, evaluates `n - i`
# ONCE at loop entry (where `i == 0`), so it lifts against a FIXED `bound =
# n` -- it will happily return a first-'z' position that lies BEYOND the real
# `ceil(n/2)` ceiling, an `i` the real program can never produce.
#
# Isolating the bug requires a target reachable ONLY under the mis-lift and
# genuinely UNREACHABLE in the real program. Pin `n == 6` (so `ceil(n/2) ==
# 3`: the real loop's `i` can only ever be 0, 1, 2, or 3) and query `i == 4`:
#   * Real program (n == 6): the guard at `i == 3` is `3 < (6 - 3)` = `3 < 3`
#     = false, so the loop exits at `i == 3`; `i == 4` is unreachable for ANY
#     input string. (`i` can only be SMALLER if a 'z' appears earlier.)
#   * PRE-FIX mis-lift: `bound = n = 6`; the closed form is `i := (p = find(s,
#     'z', 0); if p == -1 or p >= 6: 6 else p)`, so a string with its first
#     'z' at index 4 (4 < 6) yields `i == 4` -- a FABRICATED `sxSat` for a
#     state the real loop can never reach.
# Crucially `n == 6` is pinned in the target, so the degenerate `n <= 0`
# "loop never runs, i stays 0" family (which WOULD make some `i`-vs-`n`
# targets legitimately reachable) is excluded -- the ONLY way to `i == 4`
# here is the mis-lift.
#
# The leading `if s.len < 8: return` is a CONFOUND GUARD, not part of the
# idiom: with `n == 6` the loop only ever reads `s[0..3]`, so pinning
# `s.len >= 8` guarantees none of those reads is out of bounds. Without it,
# the POST-fix (un-lifted) path exposes the raw `s[i]` to SND-4's
# `IndexError` modeling for an unconstrained short string, and the label
# query surfaces that reachable `IndexDefect` as `sxRaised` -- still `!=
# sxSat` (the load-bearing soundness property holds) but it muddies the
# precise verdict. (Pre-fix the lift replaces `s[i]` with a closed-form
# `find`, which models its own bounds, so the confound only appears once the
# fix stops lifting.) With the guard, the post-fix verdict is a clean,
# definitive `sxUnsat`.
proc sutScanBoundDependsOnI(s: string, n: int) =
  if s.len < 8: return
  var i = 0
  while i < (n - i) and s[i] != 'z':
    inc i
  if n == 6 and i == 4:
    symexTarget("impossible")

suite "symex RFC-chapulin-hardening R2 -- loop-counter-dependent bound rejected":

  test "R2-1: while i < (n - i) and s[i] != 'z': inc i -- bound depends on i, must NOT closed-form lift":
    let r = symexFind(sutScanBoundDependsOnI, tLabel("impossible"))
    # Pre-fix (bug present): the recognizer wrongly accepts this shape and
    # lifts it to a closed form pinned at the loop-ENTRY bound (`n == 6`),
    # letting the solver pick an `s` with its first 'z' at index 4 to satisfy
    # `i == 4` -- a FABRICATED `sxSat` for a state (i == 4, n == 6) the real
    # loop (which exits at `i == 3` under the tightening `2*i < n` bound) can
    # never reach. That is the silent wrong-verdict/witness R2 fixes.
    #
    # Post-fix: `refersToSym(boundNode, iNode)` finds `i` inside `n - i` and
    # rejects the match outright, so this loop falls through to the ordinary
    # k-unroll (`mkGuardedWhile`/`mkWhile`) path. The loop is unrolled with
    # `n` still SYMBOLIC (the target's `n == 6` is a query-time predicate, not
    # a walk-time constraint), so paths still active after `maxLoopUnwind`
    # taint the result `uncertain` -> the honest `sxUnknown` degrade (a finite
    # unroll structurally can't decide a symbolic trip count -- exactly the
    # decidability boundary Q1's lift was built to cross for the INVARIANT-
    # bound case, and correctly declines to cross here). The load-bearing
    # assertion is `!= sxSat`: NO fabricated witness for the mis-lift's
    # impossible `(i == 4, n == 6)` state. `sxUnknown` is the precise,
    # observed post-fix verdict (contrast the PRE-fix `sxSat`).
    check r.status != sxSat
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# Positive control -- the genuinely-same-symbol, loop-invariant-bound case
# (the ordinary hand-written scan idiom) must STILL lift to closed form.
# Mirrors tsymex_q1_scanlift.nim's Q1-1 tracer; re-asserted here as a direct
# regression guard co-located with the R2/R6 tightening.
# ---------------------------------------------------------------------------

proc sutScanBoundLoopInvariant(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i == 3:
    symexTarget("hit")

suite "symex RFC-chapulin-hardening R2/R6 -- positive control (ordinary idiom still lifts)":

  test "R2/R6-pos: while i < s.len and s[i] != ':' : inc i ; i==3 -> sxSat (sameSym/refersToSym did not regress the common case)":
    let r = symexFind(sutScanBoundLoopInvariant, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len >= 3

suite "symex RFC-chapulin-hardening R2 -- version pin":

  test "walker version floor >= 62 (R2 introduced at 62)":
    check parseInt(symexWalkerVersion) >= 62
