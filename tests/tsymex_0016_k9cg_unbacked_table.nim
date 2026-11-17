## RFC-0016 K9c-g. The `seq[Table[int,int]]` unbacked-element probes
## (`k9cg_probes.nim`) over all four sources: an empty literal (E), a
## non-empty literal (L), `newSeq` (N) and a parameter (P). Each is exact or a
## classified decline, never `weInternalWalkerFault`. Split from
## `tsymex_0016_k9cg_unbacked.nim` so each file fits the bounded runner's
## default cap.
import ./k9cg_probes

genProbes("t", "t", "Table[int, int]", "initTable[int, int]()",
          "initTable[int, int]()", tabNames, "ELNP")

suite "K9c-g unbacked element paths (seq[Table[int,int]])":
  test "seq[Table[int,int]] paths never record weInternalWalkerFault":
    checkProbes("t", tabNames, "ELNP")
