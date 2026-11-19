## RFC-0016 K9c-g. Every path that reaches a seq element of a type the model
## does not back (`seq[seq[int]]`, `seq[Table[int,int]]`) must be exact or
## decline `seNestedSeqUnsupported`. None may record `weInternalWalkerFault`,
## which is the label for a walker bug, not for a known modelling gap.
##
## RFC-0016 S8cp-r (walker 400): a `seq[seq[int]]` is backed now (held
## leaf-split, `isTreeSeqElemTy`), so its probes below are a totality check
## over that backed path (each must still be exact or classified, never
## `weInternalWalkerFault`), and the decline pin that needs an element the
## model does not back uses `seq[Table[int, int]]`, the shared unbacked
## carrier of the suites that pinned a seq of seqs as unbacked.
##
## The probes live in `k9cg_probes.nim`. The `seq[seq[int]]` probes run one
## source per file: this file an empty literal (E),
## `tsymex_0016_k9cg_unbacked_l.nim` a non-empty literal (L),
## `tsymex_0016_k9cg_unbacked_n.nim` `newSeq` (N) and
## `tsymex_0016_k9cg_unbacked_p.nim` a parameter (P);
## `tsymex_0016_k9cg_unbacked_table.nim` runs the `seq[Table[int,int]]`
## probes. The 184 walks in one file took about 240 s (152 s of it
## compiling), past `scripts/dt-bounded.sh`'s default 180 s cap; two sources
## per file still ran over the CI ceiling's 150 s on msvc (RFC-0016 INT-51),
## so each source has its own file.
import std/strutils
import ./k9cg_probes
import nelli/smt/canonicalize

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", seqNames, "E")

proc tabInsertE(k: int) =
  ## The `sInsertE` probe over the unbacked carrier (`seq[Table[int, int]]`).
  var o: seq[Table[int, int]] = @[]
  o.insert(initTable[int, int](), 0)
  symexTarget("t")

suite "K9c-g unbacked element paths (seq[seq[int]], empty literal)":
  test "seq[seq[int]] empty-literal paths never record weInternalWalkerFault":
    checkProbes("s", seqNames, "E")

  test "insert into an empty seq of an unbacked element declines as a gap":
    let r = symexFind(tabInsertE, tLabel("t"))
    check r.status == sxUnknown
    check r.errors.named(seNestedSeqUnsupported)
    check not r.errors.named(weInternalWalkerFault)

  test "a loop over an empty seq of an unbacked element runs zero times":
    let r = symexFind(sForInE, tLabel("t"))
    check r.status == sxSat and r.trusted
    let w = symexFind(sWhileE, tLabel("t"))
    check w.status == sxSat and w.trusted

  test "walker version floor >= 374 (RFC-0016 K9c-g)":
    check parseInt(symexWalkerVersion) >= 374
