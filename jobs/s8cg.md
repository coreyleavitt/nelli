# Job: S8cg -- new slice (batch-7 integration findings; 1 SOUNDNESS + precision)

## Setup
- **HOLD until batch 7 lands.** Base: `origin/rfc-0005-soundness-channels` at the batch-7 landing sha. The coordinator will send it. It is expected to be 136ad60.
- Provisional walker: **240**.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md, and the RFC's batch-7 note first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cg"
title = "Batch-7 integration findings: viewFollows latent risk, var openArray views copied at the call, read-only later arguments, overflow-checked products split on small literal domains, own-context cost cliffs (ti_tuple, bb_rep_sym_empty_hit), concolic in-context solves and nested mergeMemberships, index call through a proc value"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)

1. **SOUNDNESS: S8bu's `viewFollows` latent risk** (S8bu listed it; nothing is wrong on the batch-7 stack).
   - Build the shape that would make it bite.
   - Either prove it unreachable with a pinned test and a comment citing why, or close it.
2. **A `var openArray` view that a later argument writes now declines** (batch 7 `aaf8749`). Instead, copy the view at the call, the way `placeLateAddr` does, so `fill(gArr, bumpA())` decides with Nim's `[101,20,30]`.
3. **S8br's frame check counts a later argument that only reads a global as a write.** Count reads as reads.
4. **ti_tuple (s8bc_remainder_c).** After S8bp's context isolation, the overflow-checked key*value product costs 121M rlimit in its own context, against 40k in the walk's context at batch 6. So the default now declines where batch 6 gave sxSat.
   - Restore the exact sxSat (witness 6) under the DEFAULT budgets.
   - Approaches: split a product on its operand's small literal domain before the overflow check, or seed the own context with the walk's facts or lemmas.
   - Repin to exact.
5. **bb_rep_sym_empty_hit (s8bb_replace), Z3 4.13.4.**
   - It costs 18.8M in its own context, against 12.8M in the walk's context and 0.2M on Z3 5.1. Step 1 gets only half of the 20M seq limit.
   - Restore the exact sxSat (witness "q") under the defaults on BOTH Z3 versions, and repin to exact.
   - Cover the general seq-query cliff on 4.13.4 for replace with an empty match.
6. **S8bp.** Concolic solves currently run inside the walk's context; give them the same isolation. Also run `mergeMemberships` at nested levels, not only at top level.
7. **An index call through a proc value declines.** Bind it once into a temp, as direct index calls are.
8. **Timing.** Batch 7 measured `tsymex_r6_b6_optionregion` at 59 s and `tsymex_rfc0005_s8bb_constructs` at 65 s locally on Z3 5.1, against 35-39 s on sls2 at batch 6.
   - Measure both at your base and at your head, alone, on Z3 5.1 and 4.13.4.
   - If S8bp's isolation is the cause, bring both back under 60 s.

## Verification
- Run these suites: yours, s8bc_remainder (a/b/c), s8bb_replace, s8bb_constructs, s8bp, s8bu, s8br (2), b7_integration, CR2, configdefaults, r6_b6_optionregion.
- Run them on Z3 5.1 and 4.13.4, plus cpp.
- Windows: all three legs green.
- Report DONE to `worker-reports/s8cg.md`.
