## Round-5, sello issue 3 — `negBV on non-BV SymVal` for `-int32(bFlag)`.
## The bool→int32 conversion yields a SymVal kind the unary-minus lowering
## has no case for; fires standalone (classified, both 4990026 and v0.3.2).
## `-int32(b)` is the literal ref10 mask-construction idiom, so this is the
## first shape a Curve25519 port tries to verify. The if/else spelling
## (`if b: -1'i32 else: 0'i32`) proves clean and is pinned as the control.
import std/[unittest, strutils, sequtils]
import proptest/symex
import proptest/smt/canonicalize
import proptest/smt/types

proc negConvAssert(bFlag: bool) =
  ## The mask lemma itself: -int32(b) is always 0 or -1.
  let mask = -int32(bFlag)
  symexAssert(mask == 0'i32 or mask == -1'i32)

proc negConvSat(bFlag: bool) =
  ## Non-vacuous SAT: the -1 arm is reachable (witness bFlag = true).
  if -int32(bFlag) == -1'i32:
    symexTarget("all-ones-mask")

proc negConvUnsat(bFlag: bool) =
  ## Soundness: -int32(b) can never be 1.
  if -int32(bFlag) == 1'i32:
    symexTarget("impossible-value")

proc ifElseControl(bFlag: bool) =
  ## The workaround spelling that already proves — pinned against regression.
  let mask = if bFlag: -1'i32 else: 0'i32
  symexAssert(mask == 0'i32 or mask == -1'i32)

suite "symex round-5 sello#3 — unary minus over bool->int32 conversion":

  test "mask lemma -int32(b) in {0,-1} proves (sxUnsat)":
    let r = symexFind(negConvAssert, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "all-ones arm reachable (non-vacuous SAT)":
    let r = symexFind(negConvSat, tLabel("all-ones-mask"))
    check r.status == sxSat

  test "-int32(b) == 1 is UNSAT (soundness)":
    let r = symexFind(negConvUnsat, tLabel("impossible-value"))
    check r.status == sxUnsat

  test "if/else mask control still proves (regression guard)":
    let r = symexFind(ifElseControl, tAssertionViolation())
    check r.status == sxUnsat
