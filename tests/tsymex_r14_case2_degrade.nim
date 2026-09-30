## RFC-chapulin-hardening R14 — pins the KNOWN SOUND LIMITATION of
## `mkShortCircuitWhile`'s "Case 2" shape (dsl_parser.nim): a top-level `and`
## guard whose LHS `A` itself required hoisting a preamble (a nested
## short-circuit / an ordinary hoisting artifact like `(a div b) > i`, per
## CR-1b's `nnkStmtListExpr` handling), e.g.
##   while (a div b) > i and s[i] != 'z':
## Splitting only the outer `and` here would leave `A`'s own preamble as
## stale as the bug R14 fixes in the first place, so the clean and-split
## (Case 1) does not apply — see `mkShortCircuitWhile`'s doc comment,
## "Case 2" branches.
##
## What the walker actually does with this shape (both branches in
## `mkShortCircuitWhile`, `dsl_parser.nim`):
##  * body has NO `continue` -> falls back to the pre-R14 do-while rotation
##    (`mkRotatedGuardWhile`), which is sound whenever there is no `continue`
##    to skip its trailing refresh -> a REAL verdict, not a degrade.
##  * body DOES contain `continue` -> the rotation would be unsafe (the exact
##    hazard R14 eliminates for the clean-split case) and there is no clean
##    and-split available for this nested shape -> SOUND-DEGRADE to
##    `sxUnknown` (Invariant 3: never a false verdict).
##
## RFC-0005 S8w: the second bullet no longer holds. With `continue`
## present the body is wrapped in a labelled block whose `continue`s become
## `break`s out of it (`mkRotatedContinueWhile`), so the rotation's trailing
## refresh runs on every iteration and the shape gets its real verdict
## (`sxSat`). The first test below is re-pinned to that verdict and its
## witness replayed.
##
## This suite pins BOTH halves so a future edit can't silently swap the
## degrade for an unsound false verdict, and can't silently over-degrade the
## continue-free companion that should still get a real answer.
##
## Every test in this file is checked on BOTH the `c` and `cpp` backends
## (`scripts/dt-bounded.sh c|cpp`) per project convention.

import std/unittest
import nelli/symex

# ---------------------------------------------------------------------------
# Case 2, continue present: sound-degrade to sxUnknown.
# ---------------------------------------------------------------------------

proc caseTwoContinue(a, b: int, s: string) =
  ## Same shape as R14-1's `fCont` (`tsymex_r14_continue_guard.nim`), but the
  ## loop bound comes from `a div b` (forcing the guard's LHS to hoist a
  ## preamble -> Case 2) instead of `s.len` (Case 1's clean and-split).
  var i = 0
  while (a div b) > i and s[i] != 'z':
    inc i
    continue
  if i == 3:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Case 2, continue-free companion: rotation fallback still gives the real
# verdict (sxSat — the same reachable-i==3 shape as R14-1, just reached via
# `mkRotatedGuardWhile` instead of the and-split).
# ---------------------------------------------------------------------------

proc caseTwoNoContinue(a, b: int, s: string) =
  var i = 0
  while (a div b) > i and s[i] != 'z':
    inc i
  if i == 3:
    symexTarget("hit")

suite "symex R14 Case-2 — sound limitation of the nested-hoisting and-guard shape":

  test "Case-2 + continue: (a div b) > i and s[i] != 'z' guard gets its real sxSat verdict (RFC-0005 S8w)":
    let r = symexFind(caseTwoContinue, tLabel("hit"))
    check r.status == sxSat
    if r.status == sxSat:
      let (a, b, s) = r.witness
      check b != 0 and (a div b) >= 3
      check s.len >= 3
      check 'z' notin s[0 .. 2]
      check (a div b) == 3 or (s.len > 3 and s[3] == 'z')

  test "Case-2, continue-free companion: same guard shape without continue still gets the real sxSat verdict via the rotation fallback":
    let r = symexFind(caseTwoNoContinue, tLabel("hit"))
    check r.status == sxSat
    check r.witness[2].len >= 3
    check 'z' notin r.witness[2][0 .. 2]
