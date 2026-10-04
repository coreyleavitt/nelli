# Job: S8cd -- new slice (batch-6 integration findings; all PRECISION)

**Setup.**
- Branch: create `rfc-0005-s8cd` from origin/rfc-0005-batch6 at **80c2904** (walker 230).
- Provisional walker: **236**.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md, and the RFC's batch-6 note first.

In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cd"
title = "Batch-6 integration findings: iekSeqLen on unsupported receiver kinds, ptrTargets on the global entry fallback, case-object globals, isEagerIR bit sets, recvValue observing only the touched part, literal-haystack rfind under a tight cap"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **`iekSeqLen: unsupported receiver kind`** in S8bn's p5/p6 shapes. Model `len` over every receiver kind the walker builds there: ptr/ref deref, a field of a heap object, and a proc-value result.
2. **`ptrTargets` declines on the global entry-value fallback (`ini`).** Make the global's entry cell a valid ptr target.
3. **Case-object globals are not modelled** (`grs_after` declines). Model variant globals: discriminator, arm fields, and FieldDefect on the wrong arm. Reuse S8bw's case-object machinery.
4. **`isEagerIR` lacks `iekBitSet`.** Add it, and check that the eager-evaluation order for set expressions matches native Nim.
5. **`recvValue` observes the whole receiver.** Narrow it to the parts the operation touches, so an untouched unwritten part does not taint.
6. **A literal-haystack `rfind` under a tight cap now declines.** This is the S8o pin moved in batch 6.
   - Decide it when the query is SAT within the cap.
   - Decide it via a lemma when the haystack is a literal (its rfind is computable at walk time when the needle is literal too, and boundable otherwise).

(S8bw's two blocked bullets are S8bz's. S8bq's newSeqUninit taint is S8bv's. Do not duplicate them.)

## Verification
- Suites: yours, s8bn, s8bw, b6_globalrecv, s8as, s8o_termination, s8au, s8bl (7), s8bq, CR2, n27.
- Run on Z3 5.1 and 4.13.4, plus one cpp run.
- Push, and report DONE to `worker-reports/s8cd.md`.
