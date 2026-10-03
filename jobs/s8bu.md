# Job: S8bu -- new slice (S8bs's remainder)

Create branch `rfc-0005-s8bu` from origin/rfc-0005-s8bs at e7965d0 (based on 8165899, walker 222). Use provisional walker **225**.

Before starting, read WORKER-BRIEF.md and the "As landed (S8bs)" notes.

In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8bu"
title = "S8bs's remainder: non-terminating Int-heap/BV-local UNSAT queries under unlimited queryRLimit, closure/proc-value calls and addr of a field of an address-taken local, openArray/var openArray/mitems, array index on an address-taken path, whole-address-taken by-value seq/string"
state = "pending"
```
Flip the row to `done` at the end.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **The walk never terminates.** An `int` read from an Int-sorted heap and linked to a bit-vector return value or local produces an UNSAT query Z3 does not decide. With the default unlimited `queryRLimit`, the run never finishes. The `seq[int]` form hangs at the base too.
   - Find the encoding cause. Likely candidates are the bv2int/int2bv bridge, or a missing range fact on the Int side.
   - Fix it so the query decides quickly: keep one sort per value, add the 64-bit range facts at the bridge, or use another encoding you can prove sound.
   - Also make sure no query can run forever under the defaults. A default must bound every query, and when the bound is hit the result must be a decline, never a hang.
   - Pin the int-field and `seq[int]` forms that S8bs had to replace with bool fields. Restore them in the S8bs suites.
2. **A closure or proc-value call into an address-taken variable declines.** Model it through the same `cVarLocs` / `bindVarLocs` path on `closureCallIR`. Batch 5 also applies S8bk's late-address rule to `closureCallIR`; keep your change self-contained so it rebases.
3. **`addr b.x` of an address-taken `b` declines.** Model it as a sub-cell of b's address cell at path `.x`.
4. **`openArray` and `var openArray` parameters are not modelled, and `mitems` declines** on an unsupported statement form.
   - Model `openArray[T]` as a view (base, start, len) over a seq, an array, or a slice (`toOpenArray`). `var openArray` writes go through to the underlying storage.
   - Model `mitems` and `mpairs` over seqs and arrays.
   - Pin each against native Nim.
5. **An array index on a path into an address-taken local cannot be followed**, and the walk declines. Follow constant and symbolic indices, symbolic ones via S8be's element cells for arrays.
6. **A by-value seq or string whose whole address is taken declines.** Model it.

## Notes
- The coordinator accepted S8bs's 4-file split (s8bs_addrglobal/byref/iterparams/byvalue sharing `s8bs_suts.nim`) as meeting the per-file budget. Do not shrink audit coverage to save time.

## Verification
- Suites: yours, the 4 s8bs suites, s8be, s8ax, s8bh, s8bc, s8ac, s8an, s8as, s8ba, s8bd, s8bf_alias, s8i, s7_closure, s8ab_letaudit, s8x_vm_alias, h_stepC, H1, g4, g5, CR2.
- Also run every suite that `command grep -l 'iterator\|openArray\|mitems\|addr ' tests/tsymex_*` returns.
- Run everything on Z3 5.1 and 4.13.4, plus one cpp run.

Push, and report DONE to `worker-reports/s8bu.md`.
