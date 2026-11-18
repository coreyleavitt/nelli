## RFC-0016 INT-57, obligation (S) (reading digits from the left) at key
## size 19, split from `tsymex_0016_int57_orderproof_small` (which
## describes the whole proof) to keep each suite under the per-test limit.
import std/[unittest, strutils, times]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, symval, string_lower_support, runtime_strings]
import int57_orderproof_common

suite "INT-57 (S): reading digits from the left (key size 19)":
  test "the key sizes are those renderCmp uses":
    check 19 in keySizes()
  for L in [19]:
    test "key size " & $L & ", every step":
      proveSteps(L)

suite "INT-57: walker version":
  test "symexWalkerVersion >= 431":
    check parseInt(symexWalkerVersion) >= 431
