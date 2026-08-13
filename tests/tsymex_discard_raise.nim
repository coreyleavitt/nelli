## `discard parseInt(s)` must still model the ValueError raise. The pre-existing
## nnkDiscardStmt arm dropped any discarded non-exn-intrinsic expression to a
## no-op, so a discarded RAISING call (parseInt on bad input) lost its raise —
## yielding a FALSE POSITIVE: code AFTER the discard looked reachable via input
## that actually raises at runtime (Invariant 3 violation). The fix binds a
## discarded `parseInt` to a synthetic sink `let` so the walker threads the
## ValueError raise fork (value unused). Each witness is validated against REAL
## Nim `parseInt` — the ground truth.
##
## Additive (a discard that previously dropped now models its raise); no
## walker-version bump (nothing that produced a SOUND cached verdict changes —
## the affected programs were unsound false-positives before).
import std/[unittest, strutils]
import nelli/symex

proc nimV(s: string): string =
  ## Ground truth: what Nim's parseInt actually does with `s`.
  try: "=" & $parseInt(s) except ValueError: "RAISES"

# Discarded parseInt on a symbolic string: "after" is reached ONLY when
# parseInt(s) does NOT raise (i.e. s is a valid int).
proc sutDiscardThenAfter(s: string) =
  discard parseInt(s)
  symexTarget("after")

# The customer's validate-and-discard idiom.
proc sutValidateIdiom(s: string) =
  var caught = false
  try: discard parseInt(s)
  except ValueError: caught = true
  if caught:
    symexTarget("caught")

# Regression: a concrete VALID discard must not spuriously raise.
proc sutDiscardValid(n: int) =
  discard parseInt("512")
  if n == 5:
    symexTarget("ok")

suite "symex: discard parseInt models the ValueError raise":
  test "D1: discarded parseInt RAISES for non-numeric input (sxRaised)":
    let r = symexFind(sutDiscardThenAfter, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check nimV(r.raisedWitness[0]) == "RAISES"     # SOUND: the witness truly raises

  test "D2: SOUND — `after` reachable only via a genuinely-parseable string":
    let r = symexFind(sutDiscardThenAfter, tLabel("after"))
    check r.status == sxSat
    check nimV(r.witness[0]) != "RAISES"           # no false positive via garbage

  test "D3: validate-idiom — caught path reachable, witness non-numeric":
    let r = symexFind(sutValidateIdiom, tLabel("caught"))
    check r.status == sxSat
    check nimV(r.witness[0]) == "RAISES"

  test "D4: regression — concrete valid discard does not raise; `ok` reachable":
    let r = symexFind(sutDiscardValid, tLabel("ok"))
    check r.status == sxSat
    check r.witness[0] == 5
