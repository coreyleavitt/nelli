## RFC-0005 S8ct: the sort's row B19, exactly -- a 4096-int frame in an
## unbounded recursion behind a global.
##
## Split out of `tsymex_rfc0005_s8ct_deepterm` (batch 11): this one row took 86 s
## of deepterm's 186 s on the Windows leg, against a 240 s kill. The deep-term
## pins stay there; `arrayAccessTooWide`'s decline is pinned there too.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

var gG: int

proc recurB19(n: int): int =
  ## The sort's row B19, exactly: a 4096-int frame in an unbounded recursion.
  var pad: array[4096, int]
  pad[n and 7] = n
  recurB19(n + 1) + pad[n and 7]

proc sutB19(k: int) =
  if gG == 0:
    discard recurB19(k)
  symexTarget("t")

suite "S8ct: row B19's exact SUT":
  test "it ends, with a confirmed raise or a named decline":
    # It walked for seven minutes before the bound, and ended the process
    # before S8ct. Natively, input `high(int)` raises OverflowDefect at
    # `n + 1`, and input 0 overflows the stack.
    let r = symexFind(sutB19, tLabel("t"))
    for e in r.errors: checkpoint $e.kind & ": " & e.msg
    if r.status == sxRaised:
      check r.soundness.replay == rsConfirmed
    else:
      check r.status == sxUnknown
      var named = false
      for e in r.errors:
        if "termWalkMaxDepth" in e.msg: named = true
      check named

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 262
