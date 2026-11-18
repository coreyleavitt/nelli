## RFC-0016 INT-69: the axis differential judges a row whose modelled answer
## is undefined behaviour. A program holding such a row (`Snippet.undefined`:
## the definedness rows `read/uninitialised` and `call/opaqueBody`, and the
## foreign-routine pragma rows, INT-68) is decided as the model says: a
## `sxSat` untrusted ONLY because its witness reads that behaviour. It is
## the row's exact answer when the witness hits natively, and the harness
## counts it so (`pinJudge`'s `undefined`), recording it as `pinUndefined`
## does (`pvDeclined` by the kind) with the native hit.
##
## Red at 2206eb51: `pinExactImpl` has no `undefined` argument, and the axis
## differential counted both rows declined (they were blocked from the
## stream). Found by K8b's defined axis suite (INT-56).
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc i69Abs(x: cint): cint {.importc: "abs", header: "<stdlib.h>".}

proc i69Noinit(a, b: int8) =
  let t = int(a)
  var acc = 0
  var x {.noinit.}: int
  acc = acc + (x * 0 + t)
  if acc == 7: symexTarget("hit")

proc i69Opaque(a, b: int8) =
  let t = int(a)
  var acc = 0
  acc = acc + t
  if acc == -7: symexTarget("hit")
  discard i69Abs(cint(t))

proc i69OpaqueValue(a, b: int8) =
  # the witness rests on the foreign value the walk chose: native may differ
  let t = int(a)
  if int(i69Abs(cint(t))) == 7 and t != 7 and t != -7: symexTarget("hit")

template judged(fn: untyped; key: CellKey; ub: set[UbKind]): untyped =
  pinExactImpl(fn, claimed(symexFind(fn, tLabel("hit"), pinSettingsConst),
                           "symexFind"),
               key, tLabel("hit"), exhaustive(toSeq(low(int8) .. high(int8))),
               "tsymex_0016_int69_undefinedaxis.nim",
               ub)

suite "INT-69: an undefined answer that native reproduces is the row's":
  when not defined(cpp):
    # a cpp build's `{.noinit.}` local is not left indeterminate the way
    # the scrubbed-stack pin (`tsymex_0016_k10aa_axis`) needs; c only
    test "a `{.noinit.}` read before a write (`ubIndeterminateRead`)":
      let r = judged(i69Noinit, cellKey(axDefinedness, "read/uninitialised"),
                     {UbKind(ubIndeterminateRead)})
      check r.status == sxSat
      check not r.trusted
      check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds
  test "an opaque foreign body (`ubTailUnverified`)":
    let r = judged(i69Opaque, cellKey(axDefinedness, "call/opaqueBody"),
                   {UbKind(ubTailUnverified)})
    check r.status == sxSat
    check not r.trusted

  test "RED: with no undefined kind named, the same verdict is refused":
    expect PinFailure:
      discard judged(i69Opaque, cellKey(axDefinedness, "call/opaqueBody"), {})

  test "RED: a kind the verdict does not carry is refused":
    expect PinFailure:
      discard judged(i69Opaque, cellKey(axDefinedness, "call/opaqueBody"),
                     {UbKind(ubIndeterminateRead)})

  test "RED: a witness resting on the opaque value that misses natively is refused":
    let r = symexFind(i69OpaqueValue, tLabel("hit"), pinSettingsConst)
    check not r.trusted
    if r.status == sxSat:
      expect PinFailure:
        discard judged(i69OpaqueValue, cellKey(axDefinedness, "call/opaqueBody"),
                       {UbKind(ubTailUnverified)})
