## RFC-0016 K7c -- the cap halts of the variant and heap arms, pinned.
##
## The arm helpers (`walkVariantConstructSymArm`, `walkHeapArm`) now return
## `Survivors`, so a cap they cut on is reported through the sanctioned
## constructors, never as a truncated `seq[Path]`. This file cuts a real run
## on each of those caps through `symexFind` and pins it with `pinCap`: the
## verdict is not trusted, and an error of the cap site's kind and message is
## recorded. A cut run is never a clean `sxUnsat`.
##
## No verdict moves (no walker bump): these runs were `sxUnknown` before the
## conversion too; the pins make the cap sites evidenced in the universe
## (`capkind:ckVariantForks`, `capkind:ckVariantFieldAllocs`,
## `capkind:ckHeapDepth`), where they were allowlisted as unpinned.
import std/unittest
import nelli/symex
import nelli/smt/types
import ./s8cu_helpers

# ---- ckVariantForks: 10 feasible tags, budget 8 ------------------------------

type
  K7cWideTag = enum kw0, kw1, kw2, kw3, kw4, kw5, kw6, kw7, kw8, kw9
  K7cWideObj = object
    tag: int
    case kind: K7cWideTag
    of kw0: a0: int
    of kw1: a1: int
    of kw2: a2: int
    of kw3: a3: int
    of kw4: a4: int
    of kw5: a5: int
    of kw6: a6: int
    of kw7: a7: int
    of kw8: a8: int
    of kw9: a9: int

proc k7cForks(b: byte, n: int) =
  let op = if b == 1'u8: kw0 else: kw1
  let p = K7cWideObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("k7c_forks")

# ---- ckVariantFieldAllocs: 8 tags x 64 fields > 64 ---------------------------

type
  K7cFTag = enum kf0, kf1, kf2, kf3, kf4, kf5, kf6, kf7
  K7cFieldsObj = object
    tag: int
    case kind: K7cFTag
    of kf0: a00, a01, a02, a03, a04, a05, a06, a07: int
    of kf1: a10, a11, a12, a13, a14, a15, a16, a17: int
    of kf2: a20, a21, a22, a23, a24, a25, a26, a27: int
    of kf3: a30, a31, a32, a33, a34, a35, a36, a37: int
    of kf4: a40, a41, a42, a43, a44, a45, a46, a47: int
    of kf5: a50, a51, a52, a53, a54, a55, a56, a57: int
    of kf6: a60, a61, a62, a63, a64, a65, a66, a67: int
    of kf7: a70, a71, a72, a73, a74, a75, a76, a77: int

proc k7cFieldAllocs(b: byte, n: int) =
  let op = if b == 1'u8: kf0 else: kf1
  let p = K7cFieldsObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("k7c_fields")

# ---- an in-budget construction: not cut --------------------------------------

type
  K7cOp = enum ko0, ko1
  K7cSmall = object
    tag: int
    case opcode: K7cOp
    of ko0: rq: int
    of ko1: wq: int

proc k7cInBudget(b: byte, n: int) =
  let op = if b == 1'u8: ko0 else: ko1
  let p = K7cSmall(opcode: op, tag: n)
  if p.tag == 5:
    symexTarget("k7c_small")

# ---- ckHeapDepth: two dereferences, budget 2 ---------------------------------

type K7cNode = ref object
  val: int
  next: K7cNode

proc k7cHeap(node: K7cNode) =
  if node != nil:
    let n1 = node.next
    if n1 != nil:
      if n1.val == 5:
        symexTarget("k7c_heap")

const depthTwo = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxHeapDepth = 2

suite "RFC-0016 K7c -- a converted cap halt is a cut, not a clean unsat":

  test "variant constructor fork budget (ckVariantForks)":
    let r = symexFind(k7cForks, tLabel("k7c_forks"))
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(k7cForks, "ckVariantForks", tLabel("k7c_forks"))

  test "variant constructor field-allocation budget (ckVariantFieldAllocs)":
    let r = symexFind(k7cFieldAllocs, tLabel("k7c_fields"))
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(k7cFieldAllocs, "ckVariantFieldAllocs", tLabel("k7c_fields"))

  test "heap dereference depth budget (ckHeapDepth)":
    let r = symexFind(k7cHeap, tLabel("k7c_heap"), depthTwo)
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(k7cHeap, "ckHeapDepth", tLabel("k7c_heap"), depthTwo)

  test "the same heap SUT within its budget is reached":
    check symexFind(k7cHeap, tLabel("k7c_heap")).status == sxSat

  test "RED: pinCap fails on a run that these caps did not cut":
    expect PinFailure:
      pinCap(k7cInBudget, "ckVariantForks", tLabel("k7c_small"))
    expect PinFailure:
      pinCap(k7cInBudget, "ckVariantFieldAllocs", tLabel("k7c_small"))
    expect PinFailure:
      pinCap(k7cHeap, "ckHeapDepth", tLabel("k7c_heap"))
