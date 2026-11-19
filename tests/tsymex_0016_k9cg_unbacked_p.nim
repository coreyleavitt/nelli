## RFC-0016 K9c-g. The `seq[seq[int]]` unbacked-element probes
## (`k9cg_probes.nim`) over a parameter (P): each is exact or a classified
## decline, never `weInternalWalkerFault`. One source per file, so each fits
## the CI ceiling (see `tsymex_0016_k9cg_unbacked_e.nim`).
import ./k9cg_probes

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", seqNames, "P")

suite "K9c-g unbacked element paths (seq[seq[int]], parameter)":
  test "seq[seq[int]] parameter paths never record weInternalWalkerFault":
    checkProbes("s", seqNames, "P")
