## Round-5 dev item — `discard <expr>` is WALKED, not dropped.
##
## Pre-v68 truth (chapulin round-4 finding, CRITICAL): the `nnkDiscardStmt`
## arm lowered any discarded expression other than an allowlisted handful
## (the exception-query intrinsics, then parseInt/parseBiggestInt) to
## `mkBlock(@[])` — so `discard f(x)` never searched `f`'s defect paths and
## the surrounding proof read vacuously narrow: `sxUnsat` with the defect
## entirely invisible (Invariant 3 unsoundness for the call-and-discard
## idiom). v68: EVERY discarded expression is bound to a synthetic sink
## `let`, so its raise/defect forks thread identically to a bound use; the
## value is unused. The UNSAT pins are load-bearing: a guarded form must
## still PROVE, and an arm that kept dropping would satisfy them vacuously.

import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

proc halve(x: int): int = 100 div x

proc discardedCallUnguarded(x: int) =
  ## The chapulin masking shape: the ONLY use of `halve` is discarded.
  discard halve(x)

proc discardedCallGuarded(x: int) =
  if x != 0:
    discard halve(x)

suite "symex round-5 — discarded expressions are walked":

  test "discarded call: the callee's DivByZeroDefect is FOUND":
    let r = symexFind(discardedCallUnguarded, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

  test "guarded discarded call: no defect path (sxUnsat)":
    let r = symexFind(discardedCallGuarded, tRaisedExn("DivByZeroDefect"))
    check r.status == sxUnsat

proc discardedIndexUnguarded(data: seq[int], i: int) =
  ## Non-call discarded expression: the inline IndexDefect fork must thread.
  discard data[i]

proc discardedIndexGuarded(data: seq[int], i: int) =
  if i >= 0 and i < data.len:
    discard data[i]

suite "symex round-5 — discarded non-call expressions":

  test "discarded `data[i]`: the IndexDefect is FOUND":
    let r = symexFind(discardedIndexUnguarded, tIndexError())
    check r.status == sxRaised

  test "guarded discarded `data[i]`: no defect path (sxUnsat)":
    let r = symexFind(discardedIndexGuarded, tIndexError())
    check r.status == sxUnsat

suite "symex round-5 discard — walker version pin":

  test "walker version floor >= 68 (discard totality)":
    check parseInt(symexWalkerVersion) >= 68
