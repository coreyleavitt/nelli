## RFC-0016 INT-60: `len` of an array (magic `LengthArray`, a modelled
## exact row) as an operand of arithmetic. `len([int(a), 2]) + int(a) == 6`
## is sat (`a = 4`), and so is `arr.len + t == 3` over a `let`-bound array.
##
## Red at 39efd92b: the walk reported "the compiler magic `len`
## ({.magic: \"LengthArray\".}) has no symbolic model" (`feUnsupportedOp`)
## and returned an untrusted `sxUnknown`. The call-form `len` arm reached a
## model only for seqs, tables and sets, so an array fell through to the
## magic's stub-body decline. An array's length is its type's element
## count, and it now folds to that literal as `low` and `high` do. The
## comparison control (`len([int(a), 2]) == 2 and a == 4`) was exact before.
##
## K8b's magic axis suite found it (INT-56): the `LengthArray` fragment
## (`len([t, u, 1])` added to the accumulator), alone in a program
## (`per` = 1), declined under every relation it took.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc i60Lit(a, b: int8) =
  if len([int(a), 2]) + int(a) == 6: symexTarget("hit")

proc i60Let(a, b: int8) =
  let t = int(a)
  let arr = [t, int(b), 1]
  if arr.len + t == 3: symexTarget("hit")

proc i60Cmp(a, b: int8) =
  if len([int(a), 2]) == 2 and a == 4: symexTarget("hit")

suite "INT-60: `len` of an array as an arithmetic operand is exact":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "walker 417: the version floor":
    check parseInt(symexWalkerVersion) >= 417
  test "control: `len` of an array in a comparison is exact (sat)":
    let r = symexFind(i60Cmp, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
  test "a literal array: `len([int(a), 2]) + int(a) == 6` is exact (sat)":
    let r = pinExact(i60Lit, cellKey(axMagic, "LengthArray"), tLabel("hit"), all)
    check r.status == sxSat
  test "a let-bound array: `arr.len + t == 3` is exact (sat)":
    let r = pinExact(i60Let, cellKey(axMagic, "LengthArray"), tLabel("hit"), all)
    check r.status == sxSat
