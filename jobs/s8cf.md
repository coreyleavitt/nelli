# Job: S8cf -- new slice (S8bt's remainder; 2 SOUNDNESS + precision)

**MODEL: use opus for this job's agent.** It models PCRE resource limits.

## Setup
- Branch: create `rfc-0005-s8cf` from origin/rfc-0005-s8bt at a0c5a7f (walker 224, base 2899d26).
- Provisional walker: **239**.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md, worker-reports/s8bt.md, and S8bt's "As landed" notes first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cf"
title = "S8bt's remainder: PCRE match/recursion limits and the JIT stack limit, JIT LIMIT accounting, limit-accounting gaps, SKIP:NAME past 7, UTF JIT scan residuals, symbolic step-table receiver, UTF priority-route cost, replace-lemma residuals, 8.44/8.39 allowlist"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first, against native PCRE where it applies)

### SOUNDNESS
1. **PCRE's default match and recursion limits (10M) are not modelled.** A match that native PCRE abandons with `PCRE_ERROR_MATCHLIMIT` / `RECURSIONLIMIT` must not get a definite match or no-match verdict.
   - Model the limit as the raise or result Nim's `re` surfaces.
   - Or, where the walk cannot bound the step count, decline.
   - Pin both outcomes against native.
2. **The JIT's machine-stack limit (-27, `PCRE_ERROR_JIT_STACKLIMIT`) on the Windows legs is not modelled.**
   - Same treatment as item 1.
   - Pin it on Windows CI. The local 8.37+JIT build can reproduce it with a small JIT stack if that is how std/re configures it; check.

### PRECISION
3. **The JIT's own LIMIT accounting.** Decide those patterns on the JIT instead of declining.
4. **Limit-accounting gaps.** Close every listed one: auto-possessification next to a property or XCLASS, a possessive non-ASCII UTF class repeat, a possessive (*CRLF) dot repeat, and a kept `ignore_skip_arg` under a limit.
5. **A SKIP:NAME count past 7.**
6. **UTF mode on the JIT.** Cover the U+0080..U+00BF scan, and (*ANY)'s search languages under the scan.
7. **8.37's UTF classes** with a (*UCP) POSIX class or a negated escape (Windows).
8. **A symbolic receiver through the step table** is zsUnknown at every size; it was already so at 2899d26. Make it decide.
9. **Liveness.** Z3 runs past its rlimit on a 269k-node regex. Make the encoding smaller so that query decides, and then lift or relax the regex cap where that is now safe.
10. **The UTF priority route** (matchLen, endsWith, findBounds' end without a selection form) costs Z3 seconds on a concrete subject; `findBoundsLast` of `(*UTF)(*ANY).+` on 5 bytes costs 20.2M rlimit on 4.13.4.
    - Evaluate concrete subjects at walk time, or add a selection form.
    - Pin an rlimit ceiling.
11. **Item 7's replace-lemma residuals.** Cover two-byte containment, sure bytes for UTF, verbs and LIMIT, and `count` over a replace value.
12. **The 8.44 and 8.39 interpreter builds** showed 0 differences but are not allowlisted, because no CI leg runs them.
    - Add them to an existing Windows or Linux leg's matrix only if that costs under 5 minutes of CI; then allowlist them.
    - Otherwise report the cost and keep them declined. I will decide.
    - Also cover 8.39 JIT's 113 prefix-scan differences: model them, or decline them precisely.

## Verification
- Run: S8bt's 138 suites, plus yours.
- On Z3 5.1, Z3 4.13.4 and the local 8.37+JIT build, plus cpp for the new suites.
- Windows: all three legs green.
- Keep the concurrency cap of 3.
- Use your per-job scratch directory only.
- Report DONE to `worker-reports/s8cf.md`.
