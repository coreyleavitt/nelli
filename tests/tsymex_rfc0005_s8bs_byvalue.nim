## RFC-0005 (soundness channels) slice S8bs -- a by-value argument Nim
## passes by address (an inheritable object, one larger than three words)
## or whose memory the copy shares (a seq, a string), read by a callee
## that writes the variable through an address-taken alias.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
include "s8bs_suts.nim"

suite "S8bs: by-value parameters":

  test "nim: by-value parameters":
    let ks5 = [-1, 0, 5, 29, 30, 31, 32, 33, 34, 35, 36]
    let h = nativeHits(sutSeqByValue, ks5) +
            nativeHits(sutSeqWholeByValue, ks5) +
            nativeHits(sutStrByValue, ks5) + nativeHits(sutBigByValue, ks5) +
            nativeHits(sutBigFieldByValue, ks5) +
            nativeHits(sutSmallByValue, ks5) +
            nativeHits(sutInheritableByValue, ks5) +
            nativeHits(sutNestedSameFrame, ks5)
    for l in ["sv", "sw", "sr", "bg", "bh", "sm", "ib", "ns"]:
      checkpoint l & " " & $(l in h) & " " & $((l & "_dead") in h)
      check l in h
      check (l & "_dead") notin h
  test "by-value parameters":
    clean(sutSeqByValue, "sv", sxSat)
    clean(sutSeqByValue, "sv_dead", sxUnsat)
    # A copy of a seq or string whose address is taken shares its elements
    # but not an assignment of the whole: declined (reported in the RFC).
    declines(sutSeqWholeByValue, "sw",
             "a by-value argument shares the memory of")
    declines(sutSeqWholeByValue, "sw_dead",
             "a by-value argument shares the memory of")
    declines(sutStrByValue, "sr", "a by-value argument shares the memory of")
    declines(sutStrByValue, "sr_dead",
             "a by-value argument shares the memory of")
    clean(sutBigByValue, "bg", sxSat)
    clean(sutBigByValue, "bg_dead", sxUnsat)
    clean(sutBigFieldByValue, "bh", sxSat)
    clean(sutBigFieldByValue, "bh_dead", sxUnsat)
    clean(sutSmallByValue, "sm", sxSat)
    clean(sutSmallByValue, "sm_dead", sxUnsat)
    clean(sutInheritableByValue, "ib", sxSat)
    clean(sutInheritableByValue, "ib_dead", sxUnsat)
    clean(sutNestedSameFrame, "ns", sxSat)
    clean(sutNestedSameFrame, "ns_dead", sxUnsat)

suite "S8bs: walker version":
  test "symexWalkerVersion >= 222":
    check parseInt(symexWalkerVersion) >= 222
