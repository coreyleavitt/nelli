## Phase 6d (docs/fuzz/FUZZ_PLAN.md): corpus interop. import/exportCorpusDir move byte inputs
## through AFL/libFuzzer-style one-file-per-input directories; exportCrashes replays a report's
## IR-mode crashes back to their concrete bytes for repro. Pure file I/O — no subprocess. (The
## per-worker path isolation rides on externalTarget's unique pid+counter run dirs; the worker
## pool itself is a named follow-up.)

import std/[unittest, os, sets]
import proptest

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
