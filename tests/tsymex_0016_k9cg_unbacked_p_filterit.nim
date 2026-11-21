## RFC-0016 K9c-g. The `FilterIt` probe of the `seq[seq[int]]` parameter source
## (P), alone: part of what was `tsymex_0016_k9cg_unbacked_p`. It is one walk
## of about 160 s on c (podman), the other 35 probes of the source together
## under 1 s of run, so no split of the probes can bring it under the corpus's
## 240 s wall-clock watchdog on the Windows legs: the walk itself has to get
## cheaper (`tsymex_0016_int6_d1b_walkbudget` describes its shape, a
## `filterIt` that forks every path every iteration). Kept in a file of its
## own so the cost is visible and the rest of the source is not hostage to it.
##
## RFC-0016 INT-94 (walker 489): the fan-out was the `=dup` of each `seq[int]`
## element added to the result, modelled as a k-unrolled copy loop; a seq of
## plain values is now copied as the value, and the walk is about a second
## (4.0M units, a trusted `sxSat`; `tsymex_0016_int94_dupcopy` pins it).
import std/strutils
import ./k9cg_probes

const part = seqNames[7 ..< 8]  # FilterIt

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", part, "P")

suite "K9c-g unbacked element paths (seq[seq[int]], parameter, FilterIt)":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 489

  test "seq[seq[int]] parameter FilterIt path never records weInternalWalkerFault":
    checkProbes("s", part, "P")
