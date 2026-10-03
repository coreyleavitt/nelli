# Job: S8bt -- new slice (S8bj's remainder)

## Setup
- Branch: create `rfc-0005-s8bt` from origin/rfc-0005-s8bj at 2899d26. That head is based on S8bb, at walker 211.
- Provisional walker: **224**.
- Before you start, read WORKER-BRIEF.md and the "As landed (S8bj)" notes.

In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8bt"
title = "S8bj's remainder: decline unchecked libpcre versions, JIT-vs-interpreter CRLF/ANY start filter, LIMIT between 0 and default, mixed SKIP:NAME, UTF UCP/case folding and (*ANY) in UTF, automaton/step-table/register caps, replace lemmas beyond two shapes"
state = "pending"
```
Flip the row to `done` at the end.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **SOUNDNESS: unchecked libpcre versions.**
   - The model is 8.45's, and only 8.37 has been verified against it.
   - Any other libpcre version must DECLINE with a named reason (`psUnverifiedLibVersion` or similar). Recording the version in the cache key is not enough.
   - Do this through an explicit allowlist (8.45, 8.37), plus a test that fakes or overrides the detected version.
   - If you can verify more versions with the tri-oracle harness, add them. Candidates are the distro's PCRE on the test image, 8.44 and 8.39. Each one you verify gets added to the allowlist with its evidence.
2. **JIT vs interpreter (212 patterns under CRLF/ANY/ANYCRLF and LIMIT).**
   - Model JIT's behaviour exactly where you can: its scan_prefix start filter, and no CRLF skip of a SKIP landing. Keep the oracle as the spec.
   - Calls on a JIT engine should then decide instead of declining.
   - Any residual pattern you can't model stays a scoped decline. Measure the residual with the oracle and report it.
3. **A LIMIT between 0 and the default.** Model `match()`'s per-opcode call accounting for the verbs and pattern classes the walker supports, and check it against the oracle.
4. **Mixed `(*SKIP:NAME)`.** Model pcre_exec's `ignore_skip_arg` re-run order.
5. **UTF.**
   - Cover `(*UCP)` classes, Unicode case folding, and `(*ANY)` with multi-byte newlines.
   - Model what the byte-faithful string model can express, using PCRE 8.45's own Unicode tables (generated, not hand-written).
   - Keep scoped declines for the rest.
6. **Size caps:** 4000 automaton states, 512 step-table states, 6 registers.
   - Measure the real costs.
   - Raise the caps where the solver stays within budget.
   - Where it would not, add a smarter encoding, such as lazy state construction.
7. **Replace lemmas.**
   - Generalise beyond the two current shapes: a symbolic `len(by)`, multi-set patterns, a non-literal `by`, and containment over 16 bytes / non-ASCII.
   - Unbounded replace queries should decide where a sound lemma exists.

## Verification
- **Suites:** yours, s8bj, s8bb, s8ay, s8aw, s6a, and every regex suite (`command grep -l 're"\|rex"\|pcre' tests/`).
- **Configurations:** Z3 5.1 and 4.13.4, plus your PCRE 8.37+JIT build, plus one cpp run.
- Keep each file under 60 s on Windows.
- When done, push, and report DONE to `worker-reports/s8bt.md`.
