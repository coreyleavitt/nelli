## Phase 15 — Cluster E, cycle E8: `getCurrentException()` /
## `getCurrentExceptionMsg()`.
##
## The two Nim stdlib intrinsics that query the in-flight exception from
## inside an `except` handler body. Both are valid ONLY while
## `w.frame.inFlightExn.isSome` (i.e. inside a matched handler body); an
## out-of-handler call emits a classified `eeNotInHandler` (sevError) →
## `sxUnknown`, never a panic.
##
##   - `getCurrentExceptionMsg()` returns the in-flight exn's message string
##     (or "" for a zero-arg `raise newException(T)` whose msg is none).
##   - `getCurrentException()` returns an opaque `svUninterpRef` keyed by the
##     in-flight type (`sortName == "Exn_" & typeId`, `typeTag == typeId`);
##     fields are not modeled (extraction emits an `eeUninterpRefExtraction`
##     sevHint).
##
## E8 is ADDITIVE under walker version "7" (no bump). It depends on E3/E5
## already setting `w.frame.inFlightExn` for the duration of the handler body.
import std/unittest
import proptest/symex
import proptest/smt/[dsl, runtime]

# --- 1. getCurrentExceptionMsg() returns the in-flight message --------------
# The handler reads the in-flight msg ("hello") and compares it to the param
# `s`; the `hit` marker is reachable iff `s == "hello"`, so the param witness
# is constrained to "hello" — proving the intrinsic yields the raised message.
proc msgInHandler(s: string) =
  try:
    raise newException(ValueError, "hello")
  except ValueError:
    if getCurrentExceptionMsg() == s:
      symexTarget("hit")

# --- 2. getCurrentException() returns an svUninterpRef tagged with typeId ----
proc exnInHandler(x: int): int =
  try:
    raise newException(ValueError, "boom")
  except ValueError:
    discard getCurrentException()
    symexTarget("got")
    result = -1

# --- 3. getCurrentExceptionMsg() OUTSIDE any handler -> classified error -----
proc msgOutsideHandler(x: int): int =
  result = x
  if getCurrentExceptionMsg() == "":
    symexTarget("never")

# --- 4. zero-arg raise (no msg) -> getCurrentExceptionMsg() yields "" --------
# Nim's no-message raise form is an object construction with no `msg:` field
# (`newException` itself requires a message). The parser sees an nnkObjConstr
# with no `msg` ExprColonExpr -> `ExnRecord.msg == none` -> the intrinsic's
# `msg.get("")` fallback yields "".
proc msgNoMessage(s: string) =
  try:
    raise (ref ValueError)()
  except ValueError:
    if getCurrentExceptionMsg() == s:
      symexTarget("hit")

suite "symex Phase 15 E8 — getCurrentException / getCurrentExceptionMsg":
  test "E8: getCurrentExceptionMsg returns the in-flight msg":
    let r = symexFind(msgInHandler, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "E8: getCurrentException returns svUninterpRef tagged with typeId":
    lastGetCurrentExnRef = (sortName: "", typeTag: "")
    let r = symexFind(exnInHandler, tLabel("got"))
    check r.status == sxSat
    check lastGetCurrentExnRef.sortName == "Exn_ValueError"
    check lastGetCurrentExnRef.typeTag == "ValueError"

  test "E8: getCurrentExceptionMsg outside handler -> eeNotInHandler (sxUnknown)":
    let r = symexFind(msgOutsideHandler, tLabel("never"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    var sawNotInHandler = false
    for e in r.errors:
      if e.kind == eeNotInHandler:
        check e.severity == sevError
        sawNotInHandler = true
    check sawNotInHandler

  test "E8: zero-arg raise -> getCurrentExceptionMsg yields empty string":
    let r = symexFind(msgNoMessage, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == ""
