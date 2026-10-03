# S8bj -- DONE

- **Branch:** `rfc-0005-s8bj`, head `2899d26`.
- **Base:** `9e15103` (rfc-0005-s8bb).
- **Walker:** 211. `CR2` pins `== "211"`, and `tsymex_rfc0005_s8bj_walker` pins `>= 211`.
- **Commits** (squashed; no WIP left):
  - `10ef8cf` docs(rfc): the pending S8bj row (unchanged);
  - `bbb8d35` test: the PCRE probe harness and the start-of-match oracle data;
  - `3732f10` feat: the reader (verbs, limits, UTF, (?m), (?X));
  - `40ba8be` feat: the port of PCRE's start-of-match data;
  - `3b97eda` feat: the agenda, search, UTF, (?m), the CRLF skip, the engine and version gates, the replace step table and lemmas, walker 211;
  - `2899d26` docs(rfc): "As landed (S8bj)", with the row flipped to done.
- **Windows legs on `3b97eda`, all green:**
  - symex-mingw: 37115466509;
  - fuzzer-mingw: 37115466526;
  - fuzzer-msvc: 37115466522.

  `2899d26` is docs-only, so the paths-ignore rule skips those legs.

  Earlier runs:
  - `8fd3984` (37088867610 / 37088867613 / 37088867569): symex-mingw RED on four things, all fixed (see RED / GREEN).
  - `b09bf1d` (37108670353 / 37108670360 / 37108670344): green, but `entries_utf` took 133 s and `langs` 78 s, so both were split.
  - `e7f8a64` (37112496349 / 37112496323 / 37112496294): green, but `entries_utf_b` took 81.6 s, so the UTF entries were split three ways.
- **Branches:** `rfc-0005-s8bj-probe` is deleted from the remote. Nothing was pushed to main, rfc-0005-soundness-channels or worker-sls2, and no PR was opened.

## Q2 / Q7 / Q8 before and after

All runs use `tests/tsymex_rfc0005_s8bj_replace_lemmas.nim`. "Before" is the same file run on a copy of `9e15103`. Times are per query.

| Query | 9e15103, Z3 5.1 | 9e15103, Z3 4.13.4 | S8bj, Z3 5.1 | S8bj, Z3 4.13.4 |
|---|---|---|---|---|
| Q2 `replace(s, re"[0-9]", "").len > s.len` | sxUnknown 74.8 s | sxUnknown 48.5 s | sxUnsat 0.0 s | sxUnsat 0.0 s |
| Q7 `replace(s, re"f+", "x").contains("ff")` | sxUnknown 41.7 s | sxUnknown 26.8 s | sxUnsat 0.0 s | sxUnsat 0.0 s |
| Q8 `replace(s, re"a", "").contains("a")` | sxUnknown 43.9 s | sxUnknown 36.9 s | sxUnsat 0.0 s | sxUnsat 0.0 s |
| grows_by `replace(s, re"q", "yy").len > 2*len(s)` | sxUnknown 75.4 s | sxUnknown 50.0 s | sxUnsat 0.0 s | sxUnsat 0.0 s |

- The three sat counterparts are sxSat with std/re's witness everywhere.
- S8ay's exact replace pins (Q1, Q3 to Q6, Q9) pass unchanged on both versions, in s8ay_remainder and s8bb_replace.
- Windows symex-mingw, Z3 4.13.4: Q2, Q7 and Q8 are sxUnsat at 0.0 s.

## RED / GREEN

Each new suite was RED first, then GREEN:

| Suite | RED | GREEN |
|---|---|---|
| s8bj_syntax | 165 cases ("quantifier after option" undecided; LIMIT >= 10M not recorded) | 0 |
| s8bj_startopt | 9358 of 142108 differ | 0 (plus 179 probed patterns) |

The verbs, langs, entries, entries_multiline, entries_utf, replace, replace_lemmas and walker suites were all written before their code, against std/re. In walker, `bj_crlf_skip` was RED (a false sxUnsat) until the verifier-sink fix.

Fixed after the first Windows run, each pinned:
- Q7 and Q8 were sxUnknown on Z3 4.13.4. Fixed by the per-byte containment lemma, now 0.0 s.
- startopt had 1 difference on 8.37. Fixed by the version-scoped decline, pinned in startopt.
- s8bb_constructs failed its JIT gate. The test now checks `jitDeclined` instead, and does not build languages the walker declines on JIT. That took it from 108.8 s to 62.2 s on Windows; it was 58.7 s when S8bb landed.
- The s7_closure drain-list audit now lists `regexRecDefConds`.

## Soundness bugs found

1. **The 8.45 model is wrong for the Windows legs' PCRE 8.37 on `{0}` with caseless characters.** 8.37 drops the caseless flag of the required character after a `{0}` item, so `x{0}(?i)a` does not match "A". This was probed on a local 8.37 build. A target guarded by that match would have been a false sxUnsat on Windows. Now `parseSpec` declines it when the library predates 8.38, with a named reason, and the cache key records the library version.
2. **Two bugs in the new code, found by the differentials and fixed before landing.** Neither reached a commit.
   - A verifier "sink" flag leaked through minimisation and gave a false sxUnsat on `(*CRLF)[\x09-\x0b]\z`'s find. It is now a universality fixpoint over (state x newline state x UTF-8 state) on the minimised verifier.
   - The SKIP landing event was fed to every run instead of only the in-flight SKIP.
3. **At 9e15103 (S8bb):** no wrong verdict was found in the S8bb model. `a(*ACCEPT)?` was psUnknown (undecided); PCRE rejects it, and it is now psRejected.

## Design per item

1. **Verbs, start options and the start optimiser.**
   - **Reader parity.** The reader matches PCRE's compile errors (message and offset).
   - **Start-of-match data.** `pcre_startopt` ports PCRE's start-of-match data.
   - **Attempt agenda.** The attempt is an ordered agenda of threads (state, THEN frames, marks, newline condition), ALTEND markers, THEN(target), terminal sentinels and MATCH.
     - A verb's item comes after its continuation.
     - A THEN is caught by the most recent frame whose alternative ends after it (PCRE's frames and code addresses), so the stale-frame case is modelled, not declined.
   - **Search loop.** The search is `pcre_exec`'s loop:
     - the first-char / startline / start-bits filter;
     - the minlength and required-char (< 1000) breaks;
     - SKIP_ARG re-runs, SKIP jumps, the bump on NOMATCH / PRUNE / THEN, COMMIT;
     - the CRLF skip.
   - **Languages.** The languages are DFAs, minimised and then turned into regexes. They are built per previous-byte class (selection, captures, search). The search is guess-and-verify over per-outcome verifier DFAs.
   - **LIMIT.**
     - A limit of 0 is exact: -8, or -21 for RECURSION alone, exactly when an attempt is made.
     - A limit of 10M or more has no effect.
     - Anything in between declines with "a (*LIMIT_..) start option below PCRE's default".
   - **Engine.** The walker probes the engine (`pcre_config(JIT)`) and the version (`pcre_version()`) at walk time, through the wrapper's library names. On a JIT engine, unanchored calls with an observable CRLF skip or a LIMIT decline. Anchored calls never run on the JIT.
2. **UTF, byte-faithful.**
   - Characters are UTF-8 byte sequences, and code points up to 0xFF equal Nim bytes.
   - Errors: -24 for a start past the end, -10 for an invalid subject (validity is a regular language), -11 for a start inside a character.
   - Each entry surfaces the error as std/re does.
   - The languages are over valid UTF-8, and the search definitions are guarded by "no error".
3. **(?m) and (?X).**
   - (?m) reads the previous-byte class (start / CR / LF / other newline / other) under LF, CR, CRLF, ANYCRLF and ANY. Under CRLF, `$` at a CR needs its LF, and a CRLF dot that read the CR dies at the LF.
   - (?X) has compile-time RegexError parity, with options scoping.
4. **CRLF skip.** It is modelled on the interpreter. `crlfSkipSeen` is removed, and `crlfSkipObservable` gates only the JIT decline.
5. **Replace.**
   - **Lowering.** S8aw shapes keep their lowering, and `legacyRun` patterns keep S8bb's run table. Everything else uses a new step table over the agenda (registers resolved by returned reference codes).
   - **Lemmas.** Recursive replace gets these lemmas:
     - the length relation `len(r) = len(s) - c + k*len(by)` with `k*mn <= c <= k*mx`, for a numeral `len(by)`;
     - the image `r in ([^S]|by)*`;
     - per-byte `not contains(r, b)`.
   - **Definition sink.** The definition `r == rec(s)` goes in `regexRecDefConds`. `checkCapped` first tries the query without it, under `factsFirstRLimit`; an UNSAT there is sound, because the query without the definition is weaker.

## Suites

| Suite | Z3 5.1 | Z3 4.13.4 | 8.37 JIT (Z3 5.1) |
|---|---|---|---|
| `phase15_CR10_regex_overflow` | PASS 21 | PASS 39 | - |
| `phase15_CR2_cachekey` | PASS 9 | PASS 25 | - |
| `phase15_S6a_regex_parser` | PASS 19 | PASS 37 | - |
| `phase15_S6b_regex` | PASS 53 | PASS 93 | - |
| `phase15_S7b_smoke` | PASS 55 | PASS 97 | - |
| `rfc0005_s5_str` | PASS 109 | PASS 115 | - |
| `rfc0005_s6b_ops` | PASS 77 | PASS 96 | - |
| `rfc0005_s7_closure` | PASS 90 | PASS 99 | - |
| `rfc0005_s8aw_remainder` | PASS 79 | PASS 134 | - |
| `rfc0005_s8ay_remainder` | PASS 137 | PASS 186 | - |
| `rfc0005_s8bb_captures` | PASS 118 | PASS 162 | PASS 88 |
| `rfc0005_s8bb_capvalues` | PASS 49 | PASS 49 | - |
| `rfc0005_s8bb_capvalues_lf` | PASS 40 | PASS 97 | - |
| `rfc0005_s8bb_capvalues_plus` | PASS 51 | PASS 95 | - |
| `rfc0005_s8bb_constructs` | PASS 85 | PASS 125 | PASS 106 |
| `rfc0005_s8bb_exhaustive` | PASS 63 | PASS 47 | - |
| `rfc0005_s8bb_remainder` | PASS 72 | PASS 88 | - |
| `rfc0005_s8bb_replace` | PASS 84 | PASS 138 | PASS 83 |
| `rfc0005_s8bb_selection` | PASS 75 | PASS 72 | - |
| `rfc0005_s8bj_entries` | PASS 70 | PASS 139 | PASS 49 |
| `rfc0005_s8bj_entries_multiline` | PASS 66 | PASS 88 | PASS 49 |
| `rfc0005_s8bj_entries_utf` | PASS 81 | PASS 90 | PASS 78 (before the split) |
| `rfc0005_s8bj_entries_utf_b` | PASS 80 | PASS 94 | PASS 78 |
| `rfc0005_s8bj_entries_utf_c` | PASS 83 | PASS 110 | (in the first row) |
| `rfc0005_s8bj_langs` | PASS 34 | PASS 27 | PASS 27 (before the split) |
| `rfc0005_s8bj_langs_b` | PASS 34 | PASS 28 | (in the row above) |
| `rfc0005_s8bj_replace` | PASS 42 | PASS 43 | PASS 11 |
| `rfc0005_s8bj_replace_lemmas` | PASS 89 | PASS 88 | PASS 57 |
| `rfc0005_s8bj_startopt` | PASS 30 | PASS 26 | PASS 17 |
| `rfc0005_s8bj_syntax` | PASS 13 | PASS 11 | - |
| `rfc0005_s8bj_verbs` | PASS 52 | PASS 65 | PASS 16 |
| `rfc0005_s8bj_walker` | PASS 148 | PASS 117 | PASS 110 |

Times are local wall seconds including the compile, with three concurrent runs on a loaded host. The JIT column runs against a locally built PCRE 8.37 with JIT, the Windows library: the third oracle. The cpp run is `tsymex_rfc0005_s8bj_verbs`: PASS, 41 s.

To stay under 60 s on Windows:
- `s8bj_langs` is split by pattern parity into `_langs` and `_langs_b`.
- `s8bj_entries_utf` is split three ways into `_entries_utf`, `_b` and `_c`. Each twin `include`s the body with its part, and every file is registered in nelli.nimble.

Windows symex-mingw per-suite wall times on `3b97eda` (Z3 4.13.4, PCRE 8.37 JIT). Every s8bj file is under 60 s:

| Suite | rc | wall |
|---|---|---|
| `phase15_CR10_regex_overflow` | rc=0 | 0s |
| `phase15_CR2_cachekey` | rc=0 | 0s |
| `phase15_S6a_regex_parser` | rc=0 | 0s |
| `phase15_S6b_regex` | rc=0 | 0.1s |
| `phase15_S7b_smoke` | rc=0 | 0.2s |
| `rfc0005_s5_str` | rc=0 | 0.7s |
| `rfc0005_s6b_ops` | rc=0 | 0.8s |
| `rfc0005_s7_closure` | rc=0 | 1.3s |
| `rfc0005_s8aw_remainder` | rc=0 | 6s |
| `rfc0005_s8ay_remainder` | rc=0 | 7.5s |
| `rfc0005_s8bb_captures` | rc=0 | 15.3s |
| `rfc0005_s8bb_capvalues_lf` | rc=0 | 22.7s |
| `rfc0005_s8bb_capvalues_plus` | rc=0 | 16.9s |
| `rfc0005_s8bb_capvalues` | rc=0 | 14.8s |
| `rfc0005_s8bb_constructs` | rc=0 | 62.2s |
| `rfc0005_s8bb_exhaustive` | rc=0 | 17.1s |
| `rfc0005_s8bb_remainder` | rc=0 | 5.5s |
| `rfc0005_s8bb_replace` | rc=0 | 12.2s |
| `rfc0005_s8bb_selection` | rc=0 | 34.6s |
| `rfc0005_s8bj_entries_multiline` | rc=0 | 50.4s |
| `rfc0005_s8bj_entries` | rc=0 | 48.2s |
| `rfc0005_s8bj_entries_utf_b` | rc=0 | 32.8s |
| `rfc0005_s8bj_entries_utf_c` | rc=0 | 45.6s |
| `rfc0005_s8bj_entries_utf` | rc=0 | 34.2s |
| `rfc0005_s8bj_langs_b` | rc=0 | 24s |
| `rfc0005_s8bj_langs` | rc=0 | 33.1s |
| `rfc0005_s8bj_replace_lemmas` | rc=0 | 0.5s |
| `rfc0005_s8bj_replace` | rc=0 | 2.5s |
| `rfc0005_s8bj_startopt` | rc=0 | 13.1s |
| `rfc0005_s8bj_syntax` | rc=0 | 0.2s |
| `rfc0005_s8bj_verbs` | rc=0 | 30.9s |
| `rfc0005_s8bj_walker` | rc=0 | 6.6s |

## Different mechanisms, reported and not fixed here

These are also committed in the RFC section.

- **PRECISION. PCRE's JIT is not the interpreter.**
  - The tri-oracle (8.45 interpreter / 8.37 interpreter / 8.37 JIT) ran over 56764 verb patterns. The interpreters are identical. The JIT differs on 212 patterns, all under CRLF / ANY / ANYCRLF (its scan_prefix start filter, and no CRLF skip of a SKIP landing), plus LIMIT.
  - Those unanchored calls decline on a JIT engine.
  - This is a spec correction: the brief expected only LIMIT and `(*CRLF)\s(*SKIP)b` to differ. It was handled by an engine probe plus a scoped decline, not escalated, because the item's own fallback ("a scoped decline with a named reason") covers it.
- **PRECISION. A LIMIT between 0 and the default declines.** Exactness would need `match()`'s per-opcode call accounting.
- **PRECISION. Mixed (*SKIP:NAME) declines.**
  - These are a SKIP:NAME whose mark only some paths pass, a never-set SKIP:NAME beside a set one, and a never-set SKIP:NAME beside a (*SKIP) under an observable CRLF skip.
  - The cause is pcre_exec's `ignore_skip_arg` re-run order.
- **PRECISION. UTF with (*UCP) classes or Unicode case folding is psUnmodelled**, as is (*ANY) in UTF mode (multi-byte newlines).
- **SOUNDNESS on unchecked library versions.** The model is 8.45's. Only 8.37 (Windows) is checked against it, and its one start-of-match difference is declined. Another libpcre version is recorded in the cache key but not declined.
- **PRECISION. Size caps decline.** These are 4000 automaton states, 512 step-table states and 6 registers.
- **PRECISION. The replace lemmas cover two shapes only.** The length relation needs a numeral `len(by)`. The image and containment lemmas need a one-set pattern with a literal `by`, and the containment lemma covers only at most 16 plain-ASCII bytes. Other unbounded replace queries can still be `beSolverUndef`.
