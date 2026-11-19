## RFC-0016 K9c-g. The `seq[seq[int]]` unbacked-element probes
## (`k9cg_probes.nim`) over a non-empty literal (L): each is exact or a
## classified decline, never `weInternalWalkerFault`. One source per file, so
## each fits the CI ceiling (see `tsymex_0016_k9cg_unbacked_e.nim`).
import std/strutils
import ./k9cg_probes
import nelli/smt/canonicalize

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", seqNames, "L")

suite "K9c-g unbacked element paths (seq[seq[int]], non-empty literal)":
  test "seq[seq[int]] non-empty-literal paths never record weInternalWalkerFault":
    checkProbes("s", seqNames, "L")

  test "walker version floor >= 374 (RFC-0016 K9c-g)":
    check parseInt(symexWalkerVersion) >= 374
