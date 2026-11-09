## RFC-0016 PRC-07 slice B (range target). This file builds with BOTH
## `--fieldChecks:off` and `--rangeChecks:off` (its `.nim.cfg`), on the c
## backend and on cpp.
##
## Native, read from the generated C of the pinned toolchain (c backend): a
## `range[0..9]` arm field is stored as its base integer, and reading it is a
## plain load of those bytes. Nim emits no check on the read, and with
## `rangeChecks` off none on a store either, so a wrong-branch read of a
## range-typed field returns the raw value of the foreign bytes (300 below),
## with no decline: the walker holds no range fact for it in this build
## (`bitsPlace`, `rangeUnchecked`). With `rangeChecks` on, an out-of-range
## value is something the walker's later arithmetic and indexing facts assume
## cannot exist, so that read stays declined (`tsymex_0016_fieldoff`, the
## `sutRangeOverwrite` pin).
import std/unittest
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type
  Kw = enum kwa, kwb
  Wr = object
    case k: Kw
    of kwa: x: int32
    of kwb: r: range[0'i32 .. 9'i32]

const fk = cellKey(axBuild, "fieldChecks=off")

when not defined(cpp):
  proc sutRangeFromInt(v: int32) =
    let o = Wr(k: kwa, x: v)
    if o.r == 300'i32: symexTarget("hit")

  proc sutRangeOverwrite(v: int32) =
    var o = Wr(k: kwb, r: 5'i32)
    o.x = v
    if o.r == 300'i32: symexTarget("hit")

  proc sutRangeDisc(v: int32) =
    var o = Wr(k: kwa, x: v)
    o.k = kwb
    if o.r == 300'i32: symexTarget("hit")

  suite "PRC-07 slice B: a range field of foreign bytes is the raw value":
    test "a wrong-branch read of a range field returns the raw bytes":
      let r = pinExact(sutRangeFromInt, fk, domain = sampled(
        [300'i32, 5, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 300
      check not r.errors.named(feUnsupportedOp)

    test "a range field overwritten with foreign bytes reads them back":
      let r = pinExact(sutRangeOverwrite, fk, domain = sampled(
        [300'i32, 5, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 300
      check not r.errors.named(feUnsupportedOp)

    test "a discriminator write into the range arm carries the raw bytes":
      let r = pinExact(sutRangeDisc, fk, domain = sampled(
        [300'i32, 5, 0, 1, -1]))
      check r.status == sxSat
      check r.trusted
      check r.witness[0] == 300
      check not r.errors.named(feUncheckedDiscBytes)
else:
  # cpp: reading the inactive member is `ubInactiveVariantField`; nothing of
  # this file's c-backend claim applies, and the file must still build there.
  suite "PRC-07 slice B: range target (cpp)":
    test "the file builds on cpp":
      check true
