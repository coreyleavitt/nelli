## RFC-0016 INT-60 (RED, open): `len` of an array (magic `LengthArray`, a
## modelled exact row) declines when its value is an operand of arithmetic.
## `len([int(a), 2]) + int(a) == 6` is sat (`a = 4`), but the walk reports
## "the compiler magic `len` ({.magic: \"LengthArray\".}) has no symbolic
## model" (`feUnsupportedOp`) and returns an untrusted `sxUnknown`. The same
## `len` in a comparison (`len([int(a), 2]) == 2 and a == 4`) is exact, and so
## is the row's pin (`tsymex_0016_k4a_dispatch` `sLenArr`, `arr.len == 3`):
## the decline is the arithmetic operand position, literal or `let`-bound.
##
## K8b's magic axis suite found it (INT-56): the `LengthArray` fragment
## (`len([t, u, 1])` added to the accumulator), alone in a program
## (`per` = 1), declined under every relation it took.
## Not registered in the nimble test task while it is red.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

proc i60Lit(a, b: int8) =
  if len([int(a), 2]) + int(a) == 6: symexTarget("hit")

proc i60Let(a, b: int8) =
  let t = int(a)
  let arr = [t, int(b), 1]
  if arr.len + t == 3: symexTarget("hit")

proc i60Cmp(a, b: int8) =
  if len([int(a), 2]) == 2 and a == 4: symexTarget("hit")

suite "INT-60 (red): `len` of an array as an arithmetic operand declines":
  test "control: `len` of an array in a comparison is exact (sat)":
    let r = symexFind(i60Cmp, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
  test "a literal array: `len([int(a), 2]) + int(a) == 6` is exact (sat)":
    let r = symexFind(i60Lit, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
  test "a let-bound array: `arr.len + t == 3` is exact (sat)":
    let r = symexFind(i60Let, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
