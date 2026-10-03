## RFC-0005 (soundness channels) slice S8bs -- the copy-in/copy-out audit
## beyond `var` actuals: `openArray`, `sink` and `mitems`, and an inlined
## iterator's parameters, which Nim's inline expansion binds to the
## caller's locations rather than copying.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
include "s8bs_suts.nim"

suite "S8bs: other by-address parameters and iterators":

  test "nim: other by-address parameters":
    let ks4 = [-1, 0, 5, 24, 25, 26, 27, 28]
    let h = nativeHits(sutVarOpenArray, ks4) +
            nativeHits(sutOpenArrayRead, ks4) + nativeHits(sutSink, ks4) +
            nativeHits(sutIterVar, ks4) + nativeHits(sutMitems, ks4)
    for l in ["oa", "or", "sk", "iv", "mi"]:
      checkpoint l & " " & $(l in h) & " " & $((l & "_dead") in h)
      check l in h
      check (l & "_dead") notin h
  test "other by-address parameters":
    # RFC-0005 S8bu: an openArray is a view of its seq (a `var` one the seq
    # passed by address).
    clean(sutVarOpenArray, "oa", sxSat)
    clean(sutVarOpenArray, "oa_dead", sxUnsat)
    clean(sutOpenArrayRead, "or", sxSat)
    clean(sutOpenArrayRead, "or_dead", sxUnsat)
    clean(sutSink, "sk", sxSat)
    clean(sutSink, "sk_dead", sxUnsat)
    clean(sutIterVar, "iv", sxSat)
    clean(sutIterVar, "iv_dead", sxUnsat)
    # `mitems` expands to a pragma statement the walk does not support.
    declines(sutMitems, "mi", "nnkPragma")
    declines(sutMitems, "mi_dead", "nnkPragma")
  test "nim: an inlined iterator's parameters":
    let ks6 = [-1, 0, 5, 40, 41, 42, 43, 44, 45]
    let h = nativeHits(sutIterVarSeq, ks6) + nativeHits(sutIterVarInt, ks6) +
            nativeHits(sutIterValAlias, ks6) +
            nativeHits(sutIterValIndex, ks6) +
            nativeHits(sutIterVarIndex, ks6) + nativeHits(sutIterValBody, ks6)
    for l in ["it", "ii", "ip", "ix", "iy", "ib2"]:
      checkpoint l & " " & $(l in h) & " " & $((l & "_dead") in h)
      check l in h
      check (l & "_dead") notin h
  test "an inlined iterator's parameters":
    clean(sutIterVarSeq, "it", sxSat)
    clean(sutIterVarSeq, "it_dead", sxUnsat)
    clean(sutIterVarInt, "ii", sxSat)
    clean(sutIterVarInt, "ii_dead", sxUnsat)
    clean(sutIterValAlias, "ip", sxSat)
    clean(sutIterValAlias, "ip_dead", sxUnsat)
    clean(sutIterValIndex, "ix", sxSat)
    clean(sutIterValIndex, "ix_dead", sxUnsat)
    clean(sutIterVarIndex, "iy", sxSat)
    clean(sutIterVarIndex, "iy_dead", sxUnsat)
    clean(sutIterValBody, "ib2", sxSat)
    clean(sutIterValBody, "ib2_dead", sxUnsat)
