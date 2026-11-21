## RFC-0016 K9c-g. The `seq[seq[int]]` unbacked-element probes
## (`k9cg_probes.nim`) over a parameter (P): each is exact or a classified
## decline, never `weInternalWalkerFault`. Part c of 4 (and `_p_filterit`) of what was
## `tsymex_0016_k9cg_unbacked_p`: the probes `seqNames[18 ..< 27]` (LenOfElem to
## Assign). The 36 walks in one file ran about 215 s (one probe, FilterIt, about 165 s of it), too near the
## corpus's 240 s wall-clock watchdog on the Windows legs; the four parts
## together hold every probe once. One source per file, so each fits the CI
## ceiling (see `tsymex_0016_k9cg_unbacked_e.nim`).
import ./k9cg_probes

const part = seqNames[18 ..< 27]

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", part, "P")

suite "K9c-g unbacked element paths (seq[seq[int]], parameter, part c)":
  test "seq[seq[int]] parameter paths never record weInternalWalkerFault (c)":
    checkProbes("s", part, "P")
