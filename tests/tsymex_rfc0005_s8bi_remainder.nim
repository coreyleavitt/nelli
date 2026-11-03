## RFC-0005 (soundness channels) slice S8bi -- S8bb's remainder, part A:
## the soundness and crash items S8bb reported and did not fix.
##
## Item 1: every node that can raise counts as a raise site in
## `rhsHasInlineDefectFork`. A call through a closure, a `map`/`filter`
## over a closure, a borrowed arithmetic operator and a regex call were
## carriers only (their operands could raise, they could not), so in a
## `while` guard -- where `parseAtomicOperand` hoists nothing and the
## predicate is the only protection -- D1c's flat fast path lowered them
## whether or not the short circuit reached them: `b >= 0 and f(b)` forked
## `f`'s raise for `b < 0`, a false `sxSat`.
##
## Item 2: each raise carries only the facts of what was evaluated before
## it. A closure call's exit facts (its body did not raise) were appended
## to every raise of the expression, also those evaluated before the call:
## in `while ord(s[i]) + f(x) > 0` the `IndexDefect` was forked only with
## `x <= 5`, a false `sxUnsat`. And an operand left inline (`s[i]`) was
## evaluated after a later operand's hoisted `let`s.
##
## Item 3: `newSeq[T](n)`, `newSeq(s, n)`, `newSeqOfCap[T](n)` and
## `newSeqUninit[T](n)` aborted the compile ("node has no type").
##
## Item 4: `k in {..}` / `k notin {..}` over a set literal was
## `feUnsupportedExprKind` (nnkCurly).
##
## Item 5: every recursive Z3 definition carries a decreasing fuel bound
## (Z3 unfolds one without spending `rlimit`); a source scan pins it.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8bi_remainder_b`, `tsymex_rfc0005_s8bi_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 76 s).

import std/[unittest, strutils, re, sequtils, os, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc onlyLengthDecline(errs: seq[SymexErrorInfo]): bool =
  ## RFC-0005 batch 5. Every error is S8bc's length decline
  ## (`parseNewSeqLen`): a length above 2^20 is not modelled, scoped.
  if errs.len == 0: return false
  for e in errs:
    if e.kind != feUnsupportedOp or "length above 1048576" notin e.msg:
      return false
  true

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

# ---- item 1: raise sites behind a while guard's short circuit ---------------

type M = distinct int
proc `div`(a, b: M): M {.borrow.}
proc `==`(a, b: M): bool {.borrow.}

proc wClosureRaise(b: int) =
  let f = proc (x: int): bool =
    if x < 0: raise newException(ValueError, "neg")
    x > 3
  try:
    while b >= 0 and f(b): break
  except ValueError:
    symexTarget("bi_w_closure_raise")

proc wClosureReached(b: int) =
  # The control: past the short circuit the raise is reachable.
  let f = proc (x: int): bool =
    if x < 0: raise newException(ValueError, "neg")
    x > 3
  try:
    while b <= 0 and f(b): break
  except ValueError:
    symexTarget("bi_w_closure_reached")

proc wClosureDiv(b: int) =
  let f = proc (x: int): int = 10 div x
  try:
    while b == 0 or f(b) > 1: break
  except DivByZeroDefect:
    symexTarget("bi_w_closure_div")

proc wHof(b: int) =
  try:
    while b == 0 or @[1, 2].map(proc (x: int): int = x div b).len > 1: break
  except DivByZeroDefect:
    symexTarget("bi_w_hof")

proc wBorrow(b: M) =
  try:
    while b == M(0) or (M(10) div b) == M(5): break
  except DivByZeroDefect:
    symexTarget("bi_w_borrow")

proc wUnknownRegex(s: string) =
  # `(*UTF8)` leaves the pattern's validity undecided (a decline); behind
  # the short circuit Nim never runs it when `s.len <= 3`.
  var k = 0
  while s.len > 3 and s.match(re"(*UTF8)a"):
    inc k
    break
  if s.len == 1 and k == 0:
    symexTarget("bi_w_unknown_regex")

proc wValueRegex(s: string; p: string) =
  var k = 0
  try:
    while s.len > 3 and s.match(re(p)):
      inc k
      break
  except RegexError: discard
  if s.len == 1 and k == 0:
    symexTarget("bi_w_value_regex")

proc wRejectedThenDiv(s: string; b: int) =
  # The rejected pattern raises before the division is evaluated.
  try:
    while s.match(re"(ab") or 10 div b > 1: break
  except DivByZeroDefect:
    symexTarget("bi_w_rejected_then_div")
  except RegexError: discard

proc ifUnknownRegex(s: string) =
  if s.len > 3 and s.match(re"(*UTF8)a"):
    discard
  elif s.len == 1:
    symexTarget("bi_if_unknown_regex")

# ---- item 2: facts of later evaluations stay off earlier raises -------------

proc exitGuardIdx(s: string; i, x: int) =
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while ord(s[i]) + f(x) > 0: break
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_guard_idx")
  except ValueError: discard

proc exitGuardDiv(i, x: int) =
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while 10 div i + f(x) > 0: break
  except DivByZeroDefect:
    if x > 5: symexTarget("bi_exit_guard_div")
  except ValueError, OverflowDefect: discard

proc exitGuardSurvivor(i, x: int) =
  # The closure's own exit fact (its division did not trap) on an earlier
  # raise.
  let f = proc (k: int): int = 10 div k
  try:
    while 10 div i + f(x) > 0: break
  except DivByZeroDefect:
    if i == 0 and x == 0: symexTarget("bi_exit_guard_surv")
  except OverflowDefect: discard

proc exitGuardAfter(s: string; i, x: int) =
  # The control: a raise AFTER the call does carry its exit facts.
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while f(x) + ord(s[i]) > 0: break
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_guard_after")
  except ValueError: discard

proc exitGuardBetween(s: string; i, j, x: int) =
  # Two inline raises around the call: the first lacks the call's facts,
  # the second has them.
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while ord(s[i]) + f(x) + 10 div j > 0: break
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_between_idx")
  except DivByZeroDefect:
    if x > 5: symexTarget("bi_exit_between_div")
  except ValueError, OverflowDefect: discard

proc atomicIdxOrder(s: string; i, x: int) =
  # `s[i]` stays inline (CR-17(a)) while `chr(f(x))` is hoisted.
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    if s[i] == chr(f(x)): discard
  except IndexDefect:
    if x > 5: symexTarget("bi_atomic_idx_order")
  except ValueError, RangeDefect: discard

proc exitIfGuard(s: string; i, x: int) =
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    if s[i] == 'a' and f(x) > 0: discard
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_if_guard")
  except ValueError: discard

proc nsShortCircuitB(n: int) =
  var k = 0
  try:
    while n >= 0 and n <= 1000 and newSeq[int](n).len > 2:
      inc k
      break
  except RangeDefect:
    symexTarget("bi_ns_short_circuit_b")

proc nsShortCircuit(n: int) =
  # A raise site under a while guard's short circuit (item 1's predicate).
  var k = 0
  try:
    while n >= 0 and newSeq[int](n).len > 2:
      inc k
      break
  except RangeDefect:
    symexTarget("bi_ns_short_circuit")

suite "S8bi: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 210

suite "S8bi (1): raise sites behind a while guard's short circuit":
  test "a closure's raise is not forked when the short circuit skips it":
    check verdict(wClosureRaise, "bi_w_closure_raise").status == sxUnsat
  test "control: past the short circuit it is reachable":
    check verdict(wClosureReached, "bi_w_closure_reached").status == sxSat
  test "a closure's division behind `or`":
    check verdict(wClosureDiv, "bi_w_closure_div").status == sxUnsat
  test "a map over a closure behind `or`":
    check verdict(wHof, "bi_w_hof").status == sxUnsat
  test "a borrowed division behind `or`":
    check verdict(wBorrow, "bi_w_borrow").status == sxUnsat
  test "an undecided pattern behind `and` does not taint the skipping path":
    let r = verdict(wUnknownRegex, "bi_w_unknown_regex")
    check r.status == sxSat
  test "a non-literal Regex behind `and` does not taint the skipping path":
    let r = verdict(wValueRegex, "bi_w_value_regex")
    check r.status == sxSat
  test "control: a rejected pattern raises before the division":
    check verdict(wRejectedThenDiv, "bi_w_rejected_then_div").status == sxUnsat
  test "an undecided pattern behind `and` in an if guard":
    check verdict(ifUnknownRegex, "bi_if_unknown_regex").status == sxSat
  test "newSeq's RangeDefect behind `and`":
    # RFC-0005 batch 5: unbounded, the n > 2^20 path declines (S8bc's
    # guard, now on every seq constructor), so the verdict is honest
    # sxUnknown; bounded, the S8bi pin stands.
    let r = verdict(nsShortCircuit, "bi_ns_short_circuit")
    check r.status == sxUnknown
    check onlyLengthDecline(r.errors)
    check verdict(nsShortCircuitB, "bi_ns_short_circuit_b").status == sxUnsat

suite "S8bi (2): a raise carries only what was evaluated before it":
  test "an index raise before a closure call (while guard)":
    check verdict(exitGuardIdx, "bi_exit_guard_idx").status == sxSat
  test "a division raise before a closure call (while guard)":
    check verdict(exitGuardDiv, "bi_exit_guard_div").status == sxSat
  test "the closure's own trap fact is not on an earlier raise":
    check verdict(exitGuardSurvivor, "bi_exit_guard_surv").status == sxSat
  test "control: a raise after the call carries its facts":
    check verdict(exitGuardAfter, "bi_exit_guard_after").status == sxUnsat
  test "a raise before the call lacks its facts; one after has them":
    check verdict(exitGuardBetween, "bi_exit_between_idx").status == sxSat
    check verdict(exitGuardBetween, "bi_exit_between_div").status == sxUnsat
  test "an inline index is evaluated before a hoisted later operand":
    check verdict(atomicIdxOrder, "bi_atomic_idx_order").status == sxSat
  test "control: an if guard's index before the call":
    check verdict(exitIfGuard, "bi_exit_if_guard").status == sxSat
