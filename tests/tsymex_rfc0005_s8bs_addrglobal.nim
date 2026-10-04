## RFC-0005 (soundness channels) slice S8bs -- an address cell aliased
## through a global ptr across a frame boundary.
##
## S8bg found it: `gpb = addr b; setXG(pb[].x, k)` where `setXG` writes its
## `var` formal and then `gpb[].x = 5`. Nim passes `pb[].x` by address, so
## the callee's two writes land on one location in its order (`b.x == 5`).
## The walker copied the actual in and out, and the write-back of the stale
## `v = k` landed over the write through the global: "ac" was `sxUnsat` and
## "ac_dead" `sxSat`, with no decline.
##
## Every expectation below is Nim's (the "nim" test runs each SUT natively
## under a capture frame and checks which labels it hits).
##
## This file: the exhibit and the family of routes to the alias. Its
## siblings: `_byref` (paths by name, heap lvalues by reference, inheritance
## conversions), `_iterparams` (other by-address parameters, inlined
## iterators) and `_byvalue` (by-value parameters Nim passes by address or
## shares).
include "s8bs_suts.nim"

suite "S8bs: an address cell reached through a global ptr":

  test "nim":
    let h = nativeHits(sutAddrCellByRef, ks)
    check "ac" in h
    check "ac_dead" notin h

  test "the S8bg exhibit":
    clean(sutAddrCellByRef, "ac", sxSat)
    clean(sutAddrCellByRef, "ac_dead", sxUnsat)

  test "nim: the family":
    let ks2 = [-1, 0, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    let h = nativeHits(sutAliasBefore, ks2) + nativeHits(sutByName, ks2) +
            nativeHits(sutByNameBefore, ks2) + nativeHits(sutScalar, ks2) +
            nativeHits(sutReadOnly, ks2) + nativeHits(sutReadOnlyByName, ks2) +
            nativeHits(sutTwoDeep, ks2) + nativeHits(sutPtrParam, ks2) +
            nativeHits(sutPtrParamByName, ks2) + nativeHits(sutHeapField, ks2) +
            nativeHits(sutCapture, ks2) + nativeHits(sutProcValue, ks2) +
            nativeHits(sutGlobalRef, ks2) + nativeHits(sutElem, ks2)
    for l in ["bf", "bn", "bnb", "sc", "ro", "rn", "td", "pp", "ppn", "hf",
              "cp", "pv", "gr", "el"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "the write through the alias before `v = k`":
    clean(sutAliasBefore, "bf", sxSat)
    clean(sutAliasBefore, "bf_dead", sxUnsat)
  test "the actual by name":
    clean(sutByName, "bn", sxSat)
    clean(sutByName, "bn_dead", sxUnsat)
    clean(sutByNameBefore, "bnb", sxSat)
    clean(sutByNameBefore, "bnb_dead", sxUnsat)
  test "a scalar address cell":
    clean(sutScalar, "sc", sxSat)
    clean(sutScalar, "sc_dead", sxUnsat)
  test "a callee that only reads through the alias":
    clean(sutReadOnly, "ro", sxSat)
    clean(sutReadOnly, "ro_dead", sxUnsat)
    clean(sutReadOnlyByName, "rn", sxSat)
    clean(sutReadOnlyByName, "rn_dead", sxUnsat)
  test "two levels deep":
    clean(sutTwoDeep, "td", sxSat)
    clean(sutTwoDeep, "td_dead", sxUnsat)
  test "a separate ptr parameter":
    clean(sutPtrParam, "pp", sxSat)
    clean(sutPtrParam, "pp_dead", sxUnsat)
    clean(sutPtrParamByName, "ppn", sxSat)
    clean(sutPtrParamByName, "ppn_dead", sxUnsat)
  test "a heap object's field":
    clean(sutHeapField, "hf", sxSat)
    clean(sutHeapField, "hf_dead", sxUnsat)
  test "a closure capture":
    clean(sutCapture, "cp", sxSat)
    clean(sutCapture, "cp_dead", sxUnsat)
  test "a proc-value call":
    # RFC-0005 S8bh declined it (the body reaches a heap cell of the
    # type). RFC-0005 S8ca: `pb[].x` is passed by reference.
    clean(sutProcValue, "pv", sxSat)
    clean(sutProcValue, "pv_dead", sxUnsat)
  test "a global ref":
    clean(sutGlobalRef, "gr", sxSat)
    clean(sutGlobalRef, "gr_dead", sxUnsat)
  test "an element address":
    clean(sutElem, "el", sxSat)
    clean(sutElem, "el_dead", sxUnsat)
