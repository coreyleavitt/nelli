# Job: S8cl -- new slice (S8ca's remainder; item 1 is SOUNDNESS; PRIORITY)

Runs next in the queue, ahead of S8cg.

## Setup
- Branch: create `rfc-0005-s8cl` from the head of batch 8 once it has landed, then merge origin/rfc-0005-s8ca at 8cef160. The coordinator will send the sha. If batch 8 has not landed when a slot opens, use origin/rfc-0005-batch8 at its current tip and tell the coordinator which sha you used.
- That merge conflicts in 8 files, including `runtime.nim` and `dsl_parser.nim`. Push your resolution as `worker-reports/s8ca-trial-merge.diff` on worker-sls2 as soon as it compiles, because the batch 9 integrator needs the same one.
- Walker number is assigned at integration; use the next free one above 241 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md and worker-reports/s8ca.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cl"
title = "S8ca's remainder: unsafeNew is dropped, wasMoved stops the compile, setLen declines on its when statement, a by-value copy of a string of unknown provenance, n43_parity on cpp"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first, against native Nim)
1. **SOUNDNESS: `unsafeNew(p, n)` is dropped.** `var p: ref int; unsafeNew(p, 8); p[] = k; if p[] == 3: target` is sxRaised for live and dead targets, while natively nothing raises and the live label is hit. Model the allocation. The October notes also record a false sxUnsat on a SUT nobody reproduced: find or reconstruct it from `s8ca-work/`, and pin it either way. Audit the other bodiless allocation and lifetime magics (`new` forms, `unsafeNew`, `reset`, `move`, `wasMoved`, `shallowCopy`) for the same silent drop, as `swap` also was. A silent no-op must never be how a bodiless magic is handled; make the unmodelled case decline.
2. **`wasMoved(x)` stops the compile.** `parseCalleeImpl`'s `expectKind` fails on nnkSym for nnkIdentDefs. Model it. Any other input reaching that `expectKind` must decline, not fail the build.
3. **`setLen` declines** on the `nnkWhenStmt` in its system body. Model it, so that a `mitems` body that resizes with `setLen` decides as `add` and `pop` do.
4. **A by-value copy of a string of unknown provenance** (`newString`, an opaque call) declines. A `newString` result is fresh memory and can be placed: model it. An opaque call's result stays a decline unless you can show it is sound to do better; say which.
5. **`tsymex_r6_n43_parity` does not compile on cpp** (`std::atomic` deleted `operator=`, in generated `runtime.nim` code). Fix it, and add the suite to a cpp run.

A `mitems` element used after a resize stays a decline. Its address may be stale, which is undefined natively, so that decline is the right answer. No work is needed there.

## Verification
- Suites: yours, s8ca_*, s8bu_*, configdefaults, n27, emit_roundtrip, n43_parity, s7_closure, letaudit, CR2.
- Run on Z3 5.1 and 4.13.4, plus cpp for the new suite and n43_parity. All three Windows legs green.
- Report DONE to `worker-reports/s8cl.md`, with per-file Windows times.
