## Phase 6d (docs/fuzz/FUZZ_PLAN.md): corpus interop. import/exportCorpusDir move byte inputs
## through AFL/libFuzzer-style one-file-per-input directories; exportCrashes replays a report's
## IR-mode crashes back to their concrete bytes for repro. Pure file I/O — no subprocess. (The
## per-worker path isolation rides on externalTarget's unique pid+counter run dirs; the worker
## pool itself is a named follow-up.)
##
## RFC-fuzzer-nextgen U3: byte-mode fuzzing (`fuzzWithBytes`/`fmBytes`, a parallel weak
## admission path with none of the frontier/crash-dedup/scheduling machinery) is gone —
## IR is the one mutation kernel. `importCorpusDirAsIR` below is the surviving route an
## external AFL/libFuzzer byte corpus takes IN: decode each entry through the strategy's
## byte-mode `DataSource` into an IR choice sequence usable as `FuzzSettings.initialIRCorpus`.

import std/[unittest, os, sets]
import nelli

proc bytesOf(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  for i in 0 ..< s.len: result[i] = byte(s[i])

proc asSet(xs: seq[seq[byte]]): HashSet[string] =
  for x in xs:
    var s = newString(x.len)
    for i in 0 ..< x.len: s[i] = char(x[i])
    result.incl s

proc byteStrat(): Strategy[seq[byte]] =
  lists(integers(0, 255), 1, 4).map(proc(xs: seq[int]): seq[byte] =
    result = newSeq[byte](xs.len)
    for i, v in xs: result[i] = byte(v))

proc alwaysCrash(): Target[seq[byte]] =
  Target[seq[byte]](run: proc(x: seq[byte]): Observation[seq[byte]] =
    Observation[seq[byte]](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                           message: "boom"))

suite "fuzz: corpus interop (Phase 6d)":
  test "export then import round-trips a byte corpus":
    let dir = getTempDir() / "ptinterop_corpus"
    removeDir(dir)
    let inputs = @[bytesOf("alpha"), bytesOf(""), bytesOf("\x00\x01\xfe\xff")]
    exportCorpusDir(dir, inputs)
    check asSet(importCorpusDir(dir)) == asSet(inputs)
    removeDir(dir)

  test "importCorpusDir on a missing directory yields nothing":
    check importCorpusDir(getTempDir() / "ptinterop_nope_xyz").len == 0

  test "exportCrashes writes recoverable crashing bytes":
    var frontier = newCoverageFrontier()
    let rep = fuzz(byteStrat(), alwaysCrash(), frontier,
                   FuzzSettings(maxIterations: 6, seed: 1, keepAllCrashes: true))
    check rep.irCrashes.len >= 1
    let dir = getTempDir() / "ptinterop_crashes"
    removeDir(dir)
    exportCrashes(dir, rep, byteStrat())
    let back = importCorpusDir(dir)
    check back.len == rep.irCrashes.len            # one file per replayable crash
    for b in back: check b.len >= 1                # each is the concrete delivered input
    removeDir(dir)

suite "fuzz: byte corpus -> IR seed interop (RFC-fuzzer-nextgen U3)":
  proc beU64(n: uint64): seq[byte] =
    result = newSeq[byte](8)
    for i in 0 ..< 8:
      result[7 - i] = byte((n shr (8 * i)) and 0xff'u64)

  test "importCorpusDirAsIR decodes a byte corpus into replayable IR seeds":
    let dir = getTempDir() / "ptinterop_ir_seeds"
    removeDir(dir)
    exportCorpusDir(dir, @[beU64(5'u64), beU64(7'u64)])
    let seeds = importCorpusDirAsIR(integers(0, 9), dir)
    check seeds.len == 2
    var got: seq[int]
    for choices in seeds:
      let v = replayInput(integers(0, 9), choices)
      check v.isSome
      got.add v.get
    check 5 in got
    check 7 in got
    removeDir(dir)

  test "a byte entry too short for the strategy is dropped, not propagated":
    let dir = getTempDir() / "ptinterop_ir_seeds_short"
    removeDir(dir)
    exportCorpusDir(dir, @[beU64(3'u64), @[byte(1), 2]])  # second: only 2 bytes, need 8
    let seeds = importCorpusDirAsIR(integers(0, 9), dir)
    check seeds.len == 1
    check replayInput(integers(0, 9), seeds[0]) == some(3)
    removeDir(dir)

  test "imported seeds work as real FuzzSettings.initialIRCorpus seeds":
    let dir = getTempDir() / "ptinterop_ir_seeds_e2e"
    removeDir(dir)
    exportCorpusDir(dir, @[beU64(42'u64)])
    let seeds = importCorpusDirAsIR(integers(0, 1000), dir)
    check seeds.len == 1
    var frontier = newCoverageFrontier()
    let rep = fuzz(integers(0, 1000), inProcessTarget(proc(x: int) = discard),
                   frontier, FuzzSettings(maxIterations: 1, seed: 1, initialIRCorpus: seeds))
    check rep.droppedSeeds == 0
    check rep.corpus.irEntries.len >= 1
    removeDir(dir)
