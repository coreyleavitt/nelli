# Job: S8cb -- new slice (bring S8bo up to date + S8bo's remainder)

**HOLD RELEASED** -- base is batch 6 at 80c2904 (walker 230).

S8bo was built on ef08ada, which predates batch 4. Basing its remainder on S8bo itself would repeat S8bw's stale-base block, so this slice has two steps:
1. Bring S8bo onto the current code.
2. Do the remainder there.

The provisional walker is **234**.

Before you start, read WORKER-BRIEF.md, WORKER-LOCAL.md, `git show origin/worker-sls2:worker-reports/s8bo.md` (in full, especially "Item 5 escalation"), and the RFC's "As landed (S8bo)".

In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8cb"
title = "S8bo onto batch 6 (item 5 on the leaf-split base) and S8bo's remainder: newSeq[T](n) in a callee, positional-tuple address cells, multi-variant arm field cells, p[] field range facts, unmodelled magics, replay stack fidelity on non-main threads/other OSes, a hung replay poisoning later ones"
state = "pending"
```
Flip it to `done` at the end.

## Step A -- bring S8bo onto batch 6
Merge origin/rfc-0005-s8bo at 10262dd into your branch with `git merge --no-ff`. The commit is `merge(symex): RFC-0005 S8cb -- stack S8bo (10262dd)`.
- Resolve the conflicts against S8bc's tree-seq / leaf split, S8bh, S8bs, S8bn, S8bw and the batch-5 newSeq unification.
- Do the integrator steps the report lists for item 5:
  - remove `walkElemCell`'s placeholder / `isBackedSeqElemTy` decline;
  - wire `objectCellValue` to the real element storage.
- S8bz (held; it starts from the same base) also models pointers into a seq of aggregates. Coordinate through the reports: you own `addr s[i]` element cells for a seq of OBJECTS from S8bo's item 5. S8bz builds on your cell type if both land, and the batch integrator reconciles them.
- **S8bo's own fix is SOUNDNESS** (isNil false UNSAT and friends). Every S8bo suite must stay green after the merge, with its native evidence intact.

## Step B -- S8bo's remainder
Do all of it. Defer nothing. Pin each item RED first.
1. **`newSeq[T](n)` in a callee fails the whole compile** with "node has no type" (`classifyType` in `parseCalleeImpl`). Batch 5's `parseSeqNew` may already fix it, so check first. Either way, pin it.
2. **A positional tuple's address cell holds one heap for the whole value**, so a field access through the pointer declines. Give positional tuples per-field cells.
3. **Arm fields of a multi-axis case object** (`itMultiVariant`) have no field cell, so an escaping pointer stays `heUnsafeCast`. Model it, reusing S8bw's case-object pointer work.
4. **A whole `p[]` read of a plain object does not assert its fields' declared ranges.** Add the range facts.
5. **Every unmodelled magic declines** (`swap`, `ashr`, `wasMoved`, `move`, `+%`, ...).
   - Model each magic the walker can reach, checking each against native Nim.
   - List any that remain declined, with the reason.
6. **Replay stack fidelity on a non-main Linux thread, and on other OSes** (macOS/BSD defaults): match Nim's real stack size there.
7. **One abandoned replay that never ends leaves every later replay in the process `roContended`.**
   - Isolate or reap the stuck replay so later ones proceed.
   - Pin it with a deliberately non-terminating replay.

(configdefaults' cpp maxCallDepth crash is S8ca's item 1. Do not duplicate it.)

## Verification
- Suites:
  - yours;
  - all s8bo and s8be (3-way split) suites;
  - s8ax, s8bc*, s8bh, s8bs (4), s8bn, s8bw, N2_kindgate, configdefaults (c), CR2, letaudit;
  - every replay, case-object and magic grep hit.
- Run on Z3 5.1 and 4.13.4, plus cpp.
- Push, and report DONE to `worker-reports/s8cb.md`.
