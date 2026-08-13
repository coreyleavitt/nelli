import std/[unittest, options, strutils]
import nelli
import nelli/[int128, datasource, choice]

# The bytes-as-DataSource path: external mutators (AFL, libFuzzer, replay
# from a crash file) supply a raw byte buffer, the DataSource decodes
# typed draws on the fly. Each draw consumes a fixed-width prefix from
# the buffer; bytes exhaustion raises Overrun, which the engine treats
# as Rejection — exactly what we want for malformed fuzzer inputs.

suite "newReplaySourceFromBytes: integer draws":
  test "drawInteger reads 8 bytes and maps onto the constraint range":
    # 8 bytes BE → uint64 → modulo (range+1) → offset from min.
    # Buffer: 0x0000000000000005 → raw u64 = 5, range [0, 9] → value = 5.
    var ds = newReplaySourceFromBytes(@[byte(0), 0, 0, 0, 0, 0, 0, 5])
    let v = ds.drawInteger(toInt128(0), toInt128(9), toInt128(0))
    check v == toInt128(5)

  test "two integer draws consume 16 bytes; second draw reads later prefix":
    var ds = newReplaySourceFromBytes(@[byte(0), 0, 0, 0, 0, 0, 0, 3,
                                        byte(0), 0, 0, 0, 0, 0, 0, 7])
    let a = ds.drawInteger(toInt128(0), toInt128(100), toInt128(0))
    let b = ds.drawInteger(toInt128(0), toInt128(100), toInt128(0))
    check a == toInt128(3)
    check b == toInt128(7)

  test "exhausted bytes raise Overrun on next draw":
    var ds = newReplaySourceFromBytes(@[byte(0), 0, 0, 0, 0, 0, 0, 1])
    discard ds.drawInteger(toInt128(0), toInt128(10), toInt128(0))
    expect Overrun:
      discard ds.drawInteger(toInt128(0), toInt128(10), toInt128(0))

  test "drawBoolean reads one byte; threshold gate is byte / 255":
    # `(b / 255) < p`. byte 0 → 0 < 0.5 → true; byte 255 → 1.0 < 0.5 → false.
    # Matches the RNG-mode convention (low rolls are "yes") so generation
    # and bytes-mode have the same monotonicity.
    var ds = newReplaySourceFromBytes(@[byte(0), byte(255)])
    check ds.drawBoolean(0.5) == true
    check ds.drawBoolean(0.5) == false
    expect Overrun:
      discard ds.drawBoolean(0.5)

suite "fuzzOnce: bytes → value → property":
  test "ok path: byte buffer drives a successful evaluation":
    # 8 bytes encoding the integer 5, mapped onto integers(0, 9).
    let r = fuzzOnce(integers(0, 9),
                    proc(x: int) = (ensure x < 100),
                    @[byte(0), 0, 0, 0, 0, 0, 0, 5])
    check r.outcome == foOk
    check r.value.get == 5

  test "falsified path: bytes drive a counterexample, message carries":
    let r = fuzzOnce(integers(0, 9),
                    proc(x: int) = (ensure x < 5),
                    @[byte(0), 0, 0, 0, 0, 0, 0, 8])  # 8 fails the ensure
    check r.outcome == foFalsified
    check r.value.get == 8
    check "ensure failed" in r.message

  test "rejected path: insufficient bytes → foRejected":
    let r = fuzzOnce(integers(0, 9),
                    proc(x: int) = (ensure true),
                    @[byte(1), 2, 3])  # only 3 bytes; need 8
    check r.outcome == foRejected
    check r.value.isNone
