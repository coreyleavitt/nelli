## RFC-0016 INT-57, obligation (B) (the order over two magnitudes is Nim's
## byte order) at key size 19, the two same-sign pairs (both non-negative,
## both negative). Split from `tsymex_0016_int57_orderproof_small` (which
## describes the whole proof) to keep each suite under the per-test limit;
## the mixed-sign pairs are in `tsymex_0016_int57_orderproof_b19_mixed`.
import std/[unittest, strutils, times]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, symval, string_lower_support, runtime_strings]
import int57_orderproof_common

suite "INT-57 (B): the order over two magnitudes (key size 19, same signs)":
  test "the key size is one renderCmp uses":
    check 19 in keySizes()
  test "key size 19, every pair of digit counts, same signs":
    proveOrder(19, samePairs)

suite "INT-57: walker version":
  test "symexWalkerVersion >= 431":
    check parseInt(symexWalkerVersion) >= 431
