## RFC-0005 S8bb item 5 -- the captures overloads' written elements
## against the concrete `std/re`, for `((a)|b)+`, a repeated group.
## The check is `s8bb_capvalues_check.nim`; there is one pattern per suite
## for the per-backend runtime budget (RFC-0005 S8bb item 8).
import std/[unittest, strutils, times]
import s8bb_capvalues_check

suite "S8bb (5): the captures overloads' writes, against std/re -- ((a)|b)+":

  test "the Z3 value of each written element is std/re's":
    let t0 = epochTime()
    let r = capValues("((a)|b)+")
    echo "  capture Z3 values: ", r.checked, " cases, ",
         formatFloat(epochTime() - t0, ffDecimal, 1), " s"
    checkpoint $r.bad
    check r.bad.len == 0
    check r.declined == 0
    check r.checked >= 257
