# Job: S8bv -- new slice (S8bq's remainder; all PRECISION)

**Setup**
- Branch: create `rfc-0005-s8bv` from origin/rfc-0005-s8bq at d8c3b6d (base e5df207, walker 220).
- Provisional walker: **226**.
- Read first: WORKER-BRIEF.md and the "As landed (S8bq)" notes.
- In your first commit, add this row before the S11 row, and flip it to `done` at the end:
```
[[slice]]
id = "S8bv"
title = "S8bq's remainder: iterating a builtin set, set conversion across domains, pigeonhole-hard card queries, newSeqUninit taint precision (inline map/filter/fold, composite results, slices/heap cells/mapped arrays)"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **`for x in s` over a builtin set.** Unroll over the domain in ascending ordinal order, exactly as Nim iterates. Bound it by the domain size, with a scoped decline only past a stated domain cap. Pin it against native order.
2. **Set conversion between two domains** (hidden conversion), e.g. `set[range]` to `set[base]`, or across enums with matching ordinals where Nim allows it. Model it as a bit remap, with a RangeDefect where Nim checks.
3. **Pigeonhole-hard `card` queries.** Large symbolic sets give sxUnknown under `seqQueryRLimit`.
   - Encode `card` with a pseudo-boolean / at-most-k encoding (Z3 PB constraints or a sorting network), or with a bit-count encoding that Z3 decides efficiently.
   - Measure before and after.
   - Pin a pigeonhole case that must decide.
4. **`newSeqUninit` taint precision.** Track written-ness per element, or per a symbolic written prefix:
   - Inline `map`, `filter` and `fold` taint only on reading an unwritten element.
   - A seq nested in a composite call result keeps its written-ness.
   - Slices, heap cells and mapped arrays that mention a base carry the base's written-ness.

## Integration notes (already known; do not act on them)
- `maxModelledInitialSize` duplicates S8bc's constant.
- S8bq item 2 supersedes S8bl's Incl/Excl declines.
The batch integrator reconciles both.

## Verification
- Suites: yours, s8bq, s8bi, s8bb_*, s6b_ops, emit_roundtrip, CR2, n27, letaudit, tsymex_phase1_dsl, plus every `set[`/`card`/`newSeqUninit` grep hit.
- Run on Z3 5.1 and 4.13.4, plus one cpp run.
- Push, then report DONE to `worker-reports/s8bv.md`.
