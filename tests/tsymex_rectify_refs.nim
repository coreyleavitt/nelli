## Rectify #136 — ref T / ptr T / closures with captures.
##
## Phase-5+ rectification scope: ref-typed params lower as if they
## were the underlying value type (single-allocation, no aliasing
## tracking). This handles the common case where a SUT consumes a
## ref but doesn't construct multiple aliases. Full aliasing model
## (uninterpreted sort + heap array per ref type) is a follow-up if
## a consumer needs it.
import std/unittest
import proptest/symex

type Counter = ref object
  count: int

proc atZero(c: Counter) =
  if c.count == 0:
    symexTarget("zero")

suite "symex refs #136":
  test "ref-typed param accessed by field":
    let r = symexFind(atZero, tLabel("zero"))
    check r.status == sxSat
