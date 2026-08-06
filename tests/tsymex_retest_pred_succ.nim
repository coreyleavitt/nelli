## Chapulin 0.1.0 re-test triage — catalog #pred (`pred`/`succ` had no DSL
## case), walker v64. `a ..< b` lowers via a template to `a .. pred(b)`, so
## `pred` sits on the hot path of every `..<` slice/range a SUT writes —
## chapulin's `parseTftpUri` (`rest[1 ..< closeBracket]`) failed to COMPILE
## under symexFind for this reason alone. v64 adds the arithmetic
## passthrough: `pred(x[, k])` → `x - k`, `succ(x[, k])` → `x + k` for
## int-classified operands (the same intercept shape as the A7 `ord`
## identity). The UNSAT tests are load-bearing: a stub that fabricated an
## unconstrained result would report them sxSat.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

proc succHit(x: int) =
  if succ(x) == 5:
    symexTarget("succ-hit")

proc predHit(x: int) =
  if pred(x, 3) == 10:
    symexTarget("pred-step-hit")

proc predImpossible(x: int) =
  ## `pred(x) == x` is never true for int arithmetic. The `x > 100` bound
  ## keeps `pred`'s R16-4 OverflowDefect fork unsatisfiable (pred(int.low)
  ## REALLY raises in Nim — an unbounded x legitimately reports sxRaised,
  ## verified while landing v64), so the label verdict is a pure UNSAT pin.
  if x > 100:
    if pred(x) == x:
      symexTarget("impossible-pred")

proc dotdotLessSlice(s: string) =
  ## The chapulin shape: a `..<` string slice whose bound is an expression —
  ## compiles and walks (previously could abort at macro expansion when the
  ## template pre-expanded to `pred`).
  if s.len >= 3:
    discard s[1 ..< s.len - 1]

suite "symex re-test #pred — pred/succ arithmetic passthrough":

  test "succ(x) == 5 is SAT with witness x == 4":
    let r = symexFind(succHit, tLabel("succ-hit"))
    check r.status == sxSat
    check r.witness[0] == 4

  test "pred(x, 3) == 10 is SAT with witness x == 13 (explicit step)":
    let r = symexFind(predHit, tLabel("pred-step-hit"))
    check r.status == sxSat
    check r.witness[0] == 13

  test "pred(x) == x is UNSAT (soundness)":
    let r = symexFind(predImpossible, tLabel("impossible-pred"))
    check r.status == sxUnsat

  test "`..<` string slice with expression bound compiles and walks (no IndexError path)":
    let r = symexFind(dotdotLessSlice, tIndexError())
    check r.status in {sxUnsat, sxUnknown}

suite "symex re-test #pred — walker version pin":

  test "walker version floor >= 64 (pred/succ passthrough)":
    check parseInt(symexWalkerVersion) >= 64
