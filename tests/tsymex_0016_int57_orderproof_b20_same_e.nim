## RFC-0016 INT-57, obligation (B) (the order over two magnitudes is Nim's
## byte order) at key size 20, the two same-sign pairs (both non-negative,
## both negative), part e of 5: the pairs whose first operand has 17
## to 20 digits. Split from `tsymex_0016_int57_orderproof_b20_same` (about 260 s run on c in
## one suite) so each part stays well inside the corpus's 240 s wall-clock
## watchdog on the Windows legs; the parts together hold every pair of digit
## counts, `a` to `e`. `tsymex_0016_int57_orderproof_small` describes the whole
## proof; the mixed-sign pairs are in `tsymex_0016_int57_orderproof_b20_mixed`.
import std/[unittest, strutils, times]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, symval, string_lower_support, runtime_strings]
import int57_orderproof_common

suite "INT-57 (B): the order over two magnitudes (key size 20, same signs, first operand 17-20 digits)":
  test "key size 20, first operand 17-20 digits, every second operand, same signs":
    proveOrder(20, samePairs, 17 .. 20)

suite "INT-57: walker version":
  test "symexWalkerVersion >= 431":
    check parseInt(symexWalkerVersion) >= 431
