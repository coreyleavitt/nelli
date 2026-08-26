## RFC-fuzzer-nextgen E2a (C1): the POSIX persistent worker — argv dispatch,
## genuine fork+exec self-re-exec, and the versioned framed pipe round-trip.
##
## POSIX-only (guarded by `when defined(posix)`, mirroring
## `tests/tfuzzexternal.nim`). Unlike `tfuzzexternal.nim` this needs no C
## compiler: the "external" process here is a fresh fork+exec of THIS SAME
## compiled test binary, launched in `--nelli-worker=<id>` mode
## (`fuzzworker.nim`'s `spawnWorkerProcess`).
##
## The central assertion is the RECONSTRUCTION SENTINEL (RFC round-3
## feasibility fix, DoD #3): a plain COW `fork()` WITHOUT `exec()` would
## satisfy a weaker test (the child is a distinct address space either way),
## so the pin has to discriminate "genuinely re-ran construction in a fresh
## process" from "inherited the parent's already-constructed state". See the
## `sentinelStrategy`/`sentinelProp` pair below for how.

import std/[unittest, options, strutils]
import nelli
import nelli/[datasource, rng, serialize]

# `std/unittest` treats EVERY argv parameter as a test-name/suite-name glob
# filter (`ensureInitialized`, unittest.nim) — so a re-exec'd worker child,
# launched with `--nelli-worker=<id>` on argv (the RFC's explicit "argv
# call-site ID, not an env var" dispatch), would otherwise have unittest
# silently filter OUT every `test:` block (nothing matches that glob),
# meaning the worker-mode branch embedded in a test body never runs. This
# is a real, non-obvious systems obstacle E2a hits precisely because worker
# dispatch reuses the SAME compiled test binary as its own worker process.
# Disabling unittest's own param filtering (our library's test suites never
# rely on it — `dt.sh` never passes filter args) is the fix.
disableParamFiltering()

when defined(posix):
  import std/posix

  # --- the reconstruction sentinel --------------------------------------------
  #
  # `rebuildCounter` is a process-local global, incremented once per
  # EVALUATION of `sentinelStrategy(...)` (not once per process — a fresh
  # process starts it at its compile-time initial value, 0, regardless of
  # what value the PARENT process's own copy holds).
  #
  # The parent's own front-door `fuzz(...)` call (below) evaluates
  # `sentinelStrategy` exactly once as its own argument — matching
  # `tfuzzmacro.nim`'s existing C5 pin ("the macro's own immediate call
  # constructed once") — so by the time the parent spawns a worker,
  # `rebuildCounter == 1` IN THE PARENT'S MEMORY.
  #
  # A REAL fork+exec child starts with its OWN fresh `rebuildCounter == 0`
  # (exec replaces the address space entirely — nothing is inherited). When
  # the worker loop services its one input, it re-runs
  # `sentinelStrategy(...)` from scratch (E1's `runWorkerReentry`
  # contract) — `rebuildCounter` becomes exactly `1` in the CHILD's memory.
  #
  # A NAIVE COW `fork()` WITHOUT `exec()` — the shortcut the DoD explicitly
  # forbids — would instead COPY the parent's memory at fork time
  # (`rebuildCounter` already `1`, inherited); one more construction call
  # would push it to `2`. So "the child reports exactly 1, not 2" is the
  # discriminator: it can ONLY happen if the child's `rebuildCounter` began
  # this run at 0 — i.e., a genuinely fresh process, not an inherited one.
  #
  # `sentinelProp` always "crashes" (an unconditional `doAssert false`) and
  # embeds `rebuildCounter` in the message — piggy-backing DoD #3's sentinel
  # on the SAME crash-message wire field DoD #4 needs anyway, so the
  # reconstruction proof rides the real result-frame payload, not a
  # test-only side channel.
  var rebuildCounter = 0
  proc sentinelStrategy(lo, hi: int): Strategy[int] =
    inc rebuildCounter
    integers(lo, hi)

  proc sentinelProp(n: int) {.cover.} =
    doAssert false, "rebuildCounter=" & $rebuildCounter

  suite "fuzz: POSIX persistent worker (RFC-fuzzer-nextgen E2a C1)":
    test "a real fork+exec'd worker round-trips one framed input and proves genuine reconstruction":
      rebuildCounter = 0
      # The parent's own front door: registers the worker entry for this
      # call site AND constructs `sentinelStrategy` once in the PARENT.
      discard fuzz(sentinelStrategy(-50, 50), sentinelProp,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      check rebuildCounter == 1   # parent's own construction, per tfuzzmacro.nim's C5 pin

      # Build a valid choice-sequence input for `integers(-50, 50)`.
      var ds = newDataSource(initSplitMix64(0xC0FFEE'u64))
      discard integers(-50, 50).generate(ds)
      let choices = ds.recorded

      # Spawn a REAL fork+exec'd worker (self-re-exec of this binary) AFTER
      # the parent's own construction already ran — the ordering the
      # sentinel depends on.
      let (pid, inFd, outFd) = spawnWorkerProcess(id, "")
      writeFrame(inFd, toBytes(choices))

      let frameOpt = readFrame(outFd)
      check frameOpt.isSome
      let obs = decodeObservationLite[void](frameOpt.get)

      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check obs.verdict == vInteresting
      check obs.crash.isSome
      check obs.crash.get.kind == ckException
      # The reconstruction sentinel: the CHILD's rebuilt strategy reports
      # rebuildCounter == 1 (a fresh process's first-ever construction) —
      # NOT 2 (what an inherited-from-parent COW fork would report).
      check "rebuildCounter=1" in obs.crash.get.message

    test "readFrame rejects a truncated frame":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      # Write a header claiming a 100-byte payload but supply none, then
      # close — the reader must raise FrameError, not hang or silently
      # return an empty/zeroed frame.
      var hdr: seq[byte]
      hdr.putU32(0x464C454E'u32)
      hdr.putU32(1'u32)
      hdr.putU32(100'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      discard close(pipeFds[1])
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0])

    test "readFrame rejects a bad-magic frame":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      var hdr: seq[byte]
      hdr.putU32(0xDEADBEEF'u32)
      hdr.putU32(1'u32)
      hdr.putU32(0'u32)
      var checksum: seq[byte]
      checksum.putU32(0'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      discard posix.write(pipeFds[1], addr checksum[0], checksum.len)
      discard close(pipeFds[1])
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0])

    test "readFrame rejects an unsupported version":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      var hdr: seq[byte]
      hdr.putU32(0x464C454E'u32)
      hdr.putU32(99'u32)
      hdr.putU32(0'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      discard close(pipeFds[1])
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0])

    test "readFrame rejects a length prefix over the max frame size, without attempting the read":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      var hdr: seq[byte]
      hdr.putU32(0x464C454E'u32)
      hdr.putU32(1'u32)
      hdr.putU32(uint32(nelliMaxFrameBytes) + 1'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      # Deliberately do NOT close the write end and do NOT supply the
      # (impossibly large) payload: if `readFrame` tried to read that many
      # bytes it would block forever. The bound must fire on the length
      # prefix alone, before any further read.
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0]); discard close(pipeFds[1])

    test "writeFrame/readFrame round-trip a small payload exactly":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      let payload = @[1'u8, 2'u8, 3'u8, 255'u8, 0'u8]
      writeFrame(pipeFds[1], payload)
      let got = readFrame(pipeFds[0])
      check got.isSome
      check got.get == payload
      discard close(pipeFds[0]); discard close(pipeFds[1])
