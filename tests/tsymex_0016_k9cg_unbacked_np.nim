## RFC-0016 K9c-g. The `seq[seq[int]]` unbacked-element probes
## (`k9cg_probes.nim`) over `newSeq[seq[int]](k)` (N) and a parameter (P):
## each is exact or a classified decline, never `weInternalWalkerFault`.
## Split from `tsymex_0016_k9cg_unbacked.nim` so each file fits the bounded
## runner's default cap.
##
## The termination pin. The costliest probe of the set is `sFilterItN`: a
## `filterIt` over a `newSeq` whose element reads decline, unrolled to
## `maxLoopUnwind` over a length the solver does not fix, then a tail walk.
## It spent 1.69M walk units plus 4.70M tail units when measured
## (2026-11-17), against a `walkRLimit` of 1e9. The pin bounds the run's
## total at 50M units, so a decline path that starts re-walking or retrying
## shows up here as a number, not as a killed suite.
import std/[os, strutils]
import ./k9cg_probes

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", seqNames, "NP")

suite "K9c-g unbacked element paths (seq[seq[int]], newSeq and parameter)":
  test "seq[seq[int]] newSeq and parameter paths never record weInternalWalkerFault":
    checkProbes("s", seqNames, "NP")

  test "the costliest unbacked probe (filterIt over newSeq) ends within 50M units":
    let log = getTempDir() / "k9cg_filterit_units.log"
    removeFile(log)
    putEnv("NELLI_WALK_UNITS_LOG", log)
    defer:
      delEnv("NELLI_WALK_UNITS_LOG")
      removeFile(log)
    let r = symexFind(sFilterItN, tLabel("t"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(seNestedSeqUnsupported)
    check not r.errors.named(weInternalWalkerFault)
    var total = 0
    var walks = 0
    for line in readFile(log).splitLines:
      let f = line.split('\t')
      if f.len >= 2:
        total += parseInt(f[0])
        inc walks
    checkpoint "walks: " & $walks & ", units: " & $total
    check walks >= 1
    check total < 50_000_000
