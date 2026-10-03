# S8bq -- DONE

- **sha:** `d8c3b6d2455f850c14dc688f4a47e238a4ee5b44` (`rfc-0005-s8bq`; the WIP history was rewritten into the final commits and force-pushed with lease).
- **base:** `e5df207` (S8bi). `5241b18` (the S8bq row, pending) sits between the base and the work.
- **commits:** `25c1e39` fix (item 1), `8aa0c1f` fix (item 3), `a9c53da` feat (items 2 and 5), `0ef0b05` fix (item 4, plus S8bc's infeasible-arm rule), `27b5e19` docs (as landed; row done), `d8c3b6d` fix (typed-operator guard; CI).
- **walker:** 220. CR2 is pinned `== "220"` and was run; the new suite has a `>= 220` floor.
- **Windows (d8c3b6d), all green:**
  - symex-mingw 37123777323;
  - fuzzer-mingw 37123777370;
  - fuzzer-msvc 37123777347.
- **Windows (27b5e19):** symex-mingw 37120766220 failed (`tsymex_phase1_dsl`, fixed in d8c3b6d). fuzzer-mingw 37120766213 and fuzzer-msvc 37120766267 passed.

## For the integrator

- **Item 2 supersedes S8bl's `Incl`/`Excl` `vmDeclined` entries** ("a built-in `set[T]` is not a modelled type"). On a builtin set, `incl`/`excl` are intercepted (`parseBitSetInclExcl`) before the var-param magic table. When S8bl lands, those two entries are dead for builtin sets. Remove them or keep them as a backstop for shapes the intercept leaves out.
- **S8bc's item-5 walk rule is ported verbatim into this branch.** In the `isUnsupported` arm, a path that `pathInfeasible` proves dead is dropped instead of tainted. The same text and comment are used, so the merge with batch 4 should be identical or trivial. Without it, item 1's guard turned every bounded-length dead label into sxUnknown, and S8bi's pins went RED on this.
- **The `tsymex_rfc0005_s0_exhibit` pin 2 repin is S8bc's (`cca724b`) hunk verbatim.**
- **`maxModelledInitialSize` (`1'i64 shl 20`) duplicates S8bc's name and value in `dsl_parser.nim`.** On merge, keep one definition and share it.

## RED and GREEN

All pins are in `tests/tsymex_rfc0005_s8bq_remainder.nim` (62 checks, registered in `nelli.nimble` after s8bi).
- **Item 1.**
  - RED: sxSat on 5 pins (newSeq symbolic and literal, `newSeq(s, n)`, newSeqOfCap, newSeqUninit).
  - The infeasible-arm pin (`bq_huge_bounded_dead`) was RED with the `pathInfeasible` drop disabled locally, and GREEN restored.
- **Item 3.** RED came from a probe (`tests/probe/pbq_re.nim`, untracked):
  - the literal forms were sxUnknown (`feUnsupportedExprKind nnkCallStrLit`);
  - `re("(ab")` and `re(p)` aborted the compile ("node has no type", `dsl_typebridge.nim:838`). Because of this, item 3's fixtures could not compile at base.
- **Items 2, 5 and 4.** RED was taken by running the suite on a base worktree (`wt/s8bq-base` at e5df207), with item 3's fixtures and the set-field pin removed.
  - The set-field pin is removed at base because the base cannot render a `set[char]` field witness: "type mismatch: got int literal(0) but expected set[char]".
  - Item 2: 20 / 20 pins FAILED, with only the iteration-decline control passing.
  - Item 5: 6 / 6 pins FAILED.
  - Item 4: 7 pins FAILED: no read, written read, the unwritten read (it carried the whole-path message), add, call result, index check, and augmented assignment. The other 7 controls passed.
  - Before the base run, item 4's RED was also observed on the head with the item-4 runtime stashed: 5 FAILED.
- **CI-observed RED.** symex-mingw 37120766220 failed `tsymex_phase1_dsl` (outside the grep list): an untyped `x + y * 2` reached the set-operator intercept, and `classifyType` aborted. It was reproduced locally and fixed by requiring a symbol operator in the infix and `contains` intercepts. Reruns were GREEN:
  - `tsymex_phase1_dsl` 18 / 18 on Z3 5.1 and 4.13.4;
  - s8bq 62 / 62 on both;
  - symex-mingw 37123777323.
- **GREEN.**
  - s8bq 62 / 62: c on Z3 5.1 and 4.13.4, and cpp on Z3 5.1.
  - Run-only times (built binary, shared host): c 3.9 s real / 3.7 s user; cpp 11.9 s real / 5.4 s user. Both are under 60 s.
  - Compile and run took 140 s (c) and 176 s (cpp).

## Soundness bugs found (wrong verdicts at base)

1. **False sxSat:** a `newSeq` / `newSeqOfCap` / `newSeqUninit` / `newSeq(s, n)` length above 2^20 was modelled as an allocation that succeeds.
2. **Compile abort:** `re(...)` / `rex(...)` call forms outside a regex call ("node has no type").
3. **Compile abort found in this slice:** an untyped infix in the parser's isolation entry point hit the new set-operator intercept. It never shipped; CI caught it on 27b5e19.

The rest were precision only: sxUnknown or over-taint (set values, non-constant literals, `newSeqUninit`).

## Design per item

1. **`parseSeqNew` guard.**
   - After the length is evaluated (and after its negative-length `RangeDefect`), the preamble gets `if n > maxModelledInitialSize: declineAtSite(feUnsupportedOp, ...)`.
   - The message is "`<op>` with a length above 1048576 is not modelled: allocating it raises OutOfMemDefect or not, depending on the host -- path degraded to sxUnknown". The reason is "<op>: length above 1048576", as in S8bc.
   - A literal length within the bound needs no guard.
   - S8bc's `isUnsupported` infeasible-path drop is ported.
2. **Builtin `set[T]`.**
   - New `itBitSet` (`bsElemTy`), `iekBitSet` (`BitSetOp`: lit, contains, incl, excl, union, diff, inter, le, lt, eq, card) and `svBitSet` (one Z3 bit-vector of `bitSetDomain(T).size` bits; bit i is the value lo + i).
   - The domain is `bool`, a ranged int or enum, or the full 8- or 16-bit width, capped at 2^16 bits (`maxBitSetDomain`).
   - `dsl_typebridge` classifies `set[T]` and set aliases.
   - Parser: the `nnkCurly` value arm; `contains` on a set value (the key's conversion is parsed, so it is range-checked); `card`/`len`; typed infix `+ - * <= < ==`; and statement `incl`/`excl` through `parseBitSetInclExcl`. `incl`/`excl` read the location, store back through `parseAsgn`, and decline on an unstable location. A hidden set conversion between domains declines.
   - Runtime: lowering, allocation, zero, merge (`iteSV`/`mergeSV`), return binding, hashing, and witness (`bitSetModelMembers` in 64-bit chunks, `readBitSetAs`).
   - The emit round-trip gate covers the new IR kind.
   - A query that mentions a `card` term runs under `seqQueryRLimit` (`queryMentionsBitSetCard` in `checkCapped`). The default `queryRLimit` is unbounded, and a 256-bit pigeonhole card query hung for more than 280 s.
3. **Regex constructor (`parseRegexCtor`).** For `re`/`rex`, call or call-string-literal, typed `Regex`:
   - a pattern PCRE rejects gives `raise RegexError`;
   - an accepted pattern gives `mkNewT` (non-nil);
   - an undecided or non-literal pattern gives a scoped `seUnsupportedRegex` decline.
   `let r = re"lit"` is recorded in `ctx.regexLetLiterals`, so regex calls through `r` read the literal in place.
4. **`newSeqUninit` read taint.**
   - The call registers its data array as a base (`noteUninitSeqBase`) and no longer taints.
   - `uninitAt(arr, k)` reads the term: the base gives true; a `store` gives the written slot (false, or the moved value's own unwritten-ness when it is a select of an unwritten slot, as with `del`); an `ite` merges; any other term mentioning a base gives true (conservative); a term with no base gives false. The scan is memoised per query.
   - `isIndex` and `isSeqPop` fork in two: written (clean, exact) and unwritten (tainted `feUnsupportedOpHavoc` through the single constant `uninitReadKind`). The facts go in `defectSurvivorPc`, as `drainConvFloatToIntFresh` does. A trivially unwritten read does not fork a written half.
   - An element assignment's bounds-check `isIndex` (synth word `boundsCheckSynthWord = "ixck"`, types.nim) is not a read; `s[i] += v` is.
   - A seq returned by a call is aliased (`noteUninitReturn`): `retSym.data` is unwritten where the returned data is, under the return path's branch conditions. A seq nested in a composite result declines. A closure result holding one is treated as uncertain.
   - Inline map/filter/fold reads taint in-band (`hofElemAt`).
5. **Non-constant set literals.** In `parseSetLitMember`, the key is read first, then every element and range bound in order through `parseAtomicOperand` with its conversion (range-checked). There is no short circuit, and the result is OR'd. As a value, `parseBitSetLit` sets each element's bit, and a range sets bits lo..hi (empty when hi < lo). It works in `while` guards.

## Verification

145 suites were run on the head tree (before d8c3b6d's two-line guard), c backend, 900 s bound, at most 3 concurrent:
- the 142 files from `command grep -l 'set\[\|incl\|excl\|newSeq\|re"' tests/tsymex_*.nim`;
- every `tsymex_rfc0005_s8bb_*.nim`.

This covers s8bq, s8bi, s8bb, s6b_ops, emit_roundtrip, CR2, letaudit and both n27 files. Runners: `scripts/dt-bounded.sh` (Z3 5.1) and `$W/dt413.sh` (Z3 4.13.4).

| Z3 | Suites | Checks |
|---|---|---|
| 5.1 | 145 / 145 rc=0 | 2087 / 2087 |
| 4.13.4 | 145 / 145 rc=0 | 2087 / 2087 |

- On the first Z3 5.1 pass, two suites failed and were then repinned and rerun green on 5.1. The 4.13.4 pass ran after the repins.
  - `tsymex_r6_n27_placeholder_read_audit`: the marker count moved from 85 to 94. The nine new lines only ask whether a data term mentions an uninit base, and a placeholder's inert array mentions none.
  - `tsymex_rfc0005_s0_exhibit` pin 2: S8bc's repin. The drained sevError set is empty, because the decline sits on an infeasible branch.
- No suite hung. The pass counts are equal between the Z3 versions.
- **After d8c3b6d** (it narrows the set-operator intercept to symbol operators): reran `tsymex_phase1_dsl` and s8bq on both Z3 versions, then the full Windows symex-mingw corpus (37123777323, green).
- **Re-pinned:**
  - CR2 `== "220"`;
  - s8bi: `nsUninit` is clean sxSat; the set value is modelled; six newSeq fixtures are bound to n <= 2^20; `nsLen` checks for no sevError (the guard's never-reached decline remains as a hint);
  - s6b_ops: the count stays 14, with the newSeqUninit site moved to `uninitReadKind`;
  - n27: 94;
  - s0: pin 2;
  - emit_roundtrip: `itBitSet`/`iekBitSet` arms, fixtures and a type round-trip.

Per suite (ok / failed, wall seconds including compilation; "rerun" = rerun after the repin):

| Suite | Z3 5.1 (ok / failed, s) | Z3 4.13.4 (ok / failed, s) |
|---|---|---|
| tsymex_161_overflow_obligation | 19 / 0, 72 | 19 / 0, 80 |
| tsymex_163_opaque_transparent | 15 / 0, 61 | 15 / 0, 74 |
| tsymex_163audit_range_domain | 12 / 0, 63 | 12 / 0, 74 |
| tsymex_163rev_assign_rangedefect | 9 / 0, 63 | 9 / 0, 75 |
| tsymex_163rev_concolic_modes | 19 / 0, 70 | 19 / 0, 81 |
| tsymex_163rev_disc_domain | 7 / 0, 20 | 7 / 0, 28 |
| tsymex_163rev_enum_domain | 19 / 0, 65 | 19 / 0, 74 |
| tsymex_163rev_enum_field_witness | 12 / 0, 65 | 12 / 0, 79 |
| tsymex_163rev_enum_positions | 13 / 0, 78 | 13 / 0, 77 |
| tsymex_163rev_enum_valueshapes | 9 / 0, 74 | 9 / 0, 74 |
| tsymex_163rev_inert_argfork | 9 / 0, 83 | 9 / 0, 69 |
| tsymex_163rev_inert_exclusions | 15 / 0, 96 | 15 / 0, 65 |
| tsymex_163rev_intoffset_range | 9 / 0, 101 | 9 / 0, 62 |
| tsymex_163rev_range_bounds | 11 / 0, 95 | 11 / 0, 61 |
| tsymex_163rev_scan_counter_range | 10 / 0, 73 | 10 / 0, 63 |
| tsymex_canonicalize | 32 / 0, 13 | 32 / 0, 18 |
| tsymex_configdefaults | 24 / 0, 130 | 24 / 0, 107 |
| tsymex_g1b_concolic | 15 / 0, 82 | 15 / 0, 68 |
| tsymex_g2_flip | 8 / 0, 89 | 8 / 0, 74 |
| tsymex_g6_algebra | 13 / 0, 11 | 13 / 0, 8 |
| tsymex_h_verification | 18 / 0, 66 | 18 / 0, 64 |
| tsymex_p2b_refobjconstr_expr | 18 / 0, 65 | 18 / 0, 68 |
| tsymex_phase11_walker | 11 / 0, 59 | 11 / 0, 66 |
| tsymex_phase12_notapplicable | 1 / 0, 8 | 1 / 0, 8 |
| tsymex_phase12_phase_closure | 1 / 0, 5 | 1 / 0, 8 |
| tsymex_phase12_renderchoices | 5 / 0, 19 | 5 / 0, 23 |
| tsymex_phase12_witnesses | 10 / 0, 45 | 10 / 0, 64 |
| tsymex_phase13_acceptunknown_guard | 1 / 0, 22 | 1 / 0, 29 |
| tsymex_phase13_layer1_wire | 3 / 0, 46 | 3 / 0, 56 |
| tsymex_phase13_rlimit | 1 / 0, 39 | 1 / 0, 53 |
| tsymex_phase14_b2_forcephases | 3 / 0, 6 | 3 / 0, 10 |
| tsymex_phase14_b3_trace_equivalence | 2 / 0, 14 | 2 / 0, 24 |
| tsymex_phase14_b67_label_filter | 2 / 0, 42 | 2 / 0, 68 |
| tsymex_phase15_A1_unary | 5 / 0, 43 | 5 / 0, 77 |
| tsymex_phase15_A2a_atomicir_audit | 9 / 0, 43 | 9 / 0, 84 |
| tsymex_phase15_A2a_atomize | 4 / 0, 41 | 4 / 0, 100 |
| tsymex_phase15_A2a_chokepoint_audit | 3 / 0, 8 | 3 / 0, 18 |
| tsymex_phase15_A2b_bitwise | 6 / 0, 45 | 6 / 0, 94 |
| tsymex_phase15_C1_canonical_kind | 11 / 0, 47 | 11 / 0, 100 |
| tsymex_phase15_C2_staticparams | 3 / 0, 40 | 3 / 0, 87 |
| tsymex_phase15_CR11_CR18_splitcap | 4 / 0, 39 | 4 / 0, 87 |
| tsymex_phase15_CR15_enum_ordinal | 3 / 0, 41 | 3 / 0, 83 |
| tsymex_phase15_CR2_cachekey | 6 / 0, 6 | 6 / 0, 14 |
| tsymex_phase15_E4_hierarchy | 4 / 0, 38 | 4 / 0, 84 |
| tsymex_phase15_E6_defect | 4 / 0, 38 | 4 / 0, 85 |
| tsymex_phase15_F2_float_literals | 5 / 0, 40 | 5 / 0, 80 |
| tsymex_phase15_F4_float_compare | 4 / 0, 44 | 4 / 0, 70 |
| tsymex_phase15_F8_smoke | 4 / 0, 51 | 4 / 0, 84 |
| tsymex_phase15_M1_seq_fixedwidth | 13 / 0, 48 | 13 / 0, 81 |
| tsymex_phase15_N0_kindgate_widen | 5 / 0, 46 | 5 / 0, 80 |
| tsymex_phase15_N1_resolution_gates | 32 / 0, 46 | 32 / 0, 70 |
| tsymex_phase15_N2_kindgate_audit | 5 / 0, 11 | 5 / 0, 37 |
| tsymex_phase15_N3_scan_boundary | 5 / 0, 46 | 5 / 0, 82 |
| tsymex_phase15_S6b_regex | 5 / 0, 54 | 5 / 0, 64 |
| tsymex_phase15_S7b_smoke | 8 / 0, 55 | 8 / 0, 64 |
| tsymex_phase15_rereview_drains | 15 / 0, 57 | 15 / 0, 81 |
| tsymex_phase15_z3_infra | 11 / 0, 22 | 11 / 0, 30 |
| tsymex_phase16_CR1b_tail_local | 3 / 0, 49 | 3 / 0, 70 |
| tsymex_phase16_R16_1_arithcheck_foundation | 22 / 0, 14 | 22 / 0, 21 |
| tsymex_phase16_R16_2_rangedefect | 10 / 0, 60 | 10 / 0, 86 |
| tsymex_phase16_R16_2b_shortcircuit_conv | 6 / 0, 54 | 6 / 0, 80 |
| tsymex_phase16_R16_3_divzero | 7 / 0, 62 | 7 / 0, 87 |
| tsymex_phase16_R16_4_overflow | 10 / 0, 62 | 10 / 0, 65 |
| tsymex_r11_range_invariant_audit | 7 / 0, 8 | 7 / 0, 8 |
| tsymex_r14_continue_guard | 10 / 0, 80 | 10 / 0, 70 |
| tsymex_r2_scanbound | 3 / 0, 79 | 3 / 0, 63 |
| tsymex_r6_a0_lowhigh | 10 / 0, 106 | 10 / 0, 62 |
| tsymex_r6_a1_variantlit | 8 / 0, 81 | 8 / 0, 57 |
| tsymex_r6_a3_variantconstruct_sym | 12 / 0, 77 | 12 / 0, 56 |
| tsymex_r6_a6r_callwitness | 12 / 0, 58 | 12 / 0, 59 |
| tsymex_r6_b1_stringbacked | 7 / 0, 56 | 7 / 0, 57 |
| tsymex_r6_b4_readcstring | 13 / 0, 51 | 13 / 0, 59 |
| tsymex_r6_b6_optionregion | 8 / 0, 264 | 8 / 0, 612 |
| tsymex_r6_b7r2_pathscope | 11 / 0, 112 | 11 / 0, 101 |
| tsymex_r6_b7r_bytescan | 26 / 0, 62 | 26 / 0, 74 |
| tsymex_r6_degrade_pairing_audit | 5 / 0, 7 | 5 / 0, 16 |
| tsymex_r6_lows_collectors | 5 / 0, 43 | 5 / 0, 66 |
| tsymex_r6_lows_declines | 15 / 0, 52 | 15 / 0, 72 |
| tsymex_r6_n10_coverage_matrix | 22 / 0, 58 | 22 / 0, 56 |
| tsymex_r6_n14_seqops | 25 / 0, 45 | 25 / 0, 62 |
| tsymex_r6_n20_boundedloop | 5 / 0, 36 | 5 / 0, 63 |
| tsymex_r6_n27_hof_placeholder | 6 / 0, 40 | 6 / 0, 71 |
| tsymex_r6_n27_placeholder_read_audit | 4 / 0, rerun | 4 / 0, 15 |
| tsymex_r6_n28_shadow_collision | 5 / 0, 39 | 5 / 0, 69 |
| tsymex_r6_n31_block_counter | 7 / 0, 43 | 7 / 0, 72 |
| tsymex_r6_n36_raise_class_audit | 14 / 0, 6 | 14 / 0, 14 |
| tsymex_r6_n42_deref_taint | 15 / 0, 47 | 15 / 0, 103 |
| tsymex_r6_n43_parity | 25 / 0, 50 | 25 / 0, 99 |
| tsymex_r6_n49_dottedfield_mutation | 8 / 0, 46 | 8 / 0, 98 |
| tsymex_r6_r2_zerodefault_result | 25 / 0, 56 | 25 / 0, 105 |
| tsymex_r6_r4_collector_scoping | 7 / 0, 49 | 7 / 0, 98 |
| tsymex_r6_r6_emit_roundtrip | 105 / 0, 13 | 105 / 0, 25 |
| tsymex_r7_caseexpr | 5 / 0, 47 | 5 / 0, 81 |
| tsymex_rectify_effects | 5 / 0, 45 | 5 / 0, 109 |
| tsymex_rectify_mutation | 6 / 0, 48 | 6 / 0, 109 |
| tsymex_rectify_variants | 3 / 0, 47 | 3 / 0, 104 |
| tsymex_retest_defect_net | 2 / 0, 46 | 2 / 0, 88 |
| tsymex_rfc0005_s0_exhibit | 10 / 0, rerun | 10 / 0, 86 |
| tsymex_rfc0005_s10_replay_verdict | 31 / 0, 113 | 31 / 0, 101 |
| tsymex_rfc0005_s11_surface | 34 / 0, 125 | 34 / 0, 118 |
| tsymex_rfc0005_s1_lattice | 23 / 0, 98 | 23 / 0, 52 |
| tsymex_rfc0005_s1b_kinds | 18 / 0, 120 | 18 / 0, 77 |
| tsymex_rfc0005_s1c_verdict | 24 / 0, 112 | 24 / 0, 94 |
| tsymex_rfc0005_s2_replay | 15 / 0, 116 | 15 / 0, 66 |
| tsymex_rfc0005_s3_monotonicity | 27 / 0, 108 | 27 / 0, 76 |
| tsymex_rfc0005_s4_alloc | 20 / 0, 99 | 20 / 0, 64 |
| tsymex_rfc0005_s5_str | 35 / 0, 111 | 35 / 0, 92 |
| tsymex_rfc0005_s6b_ops | 44 / 0, 101 | 44 / 0, 92 |
| tsymex_rfc0005_s7_closure | 37 / 0, 98 | 37 / 0, 97 |
| tsymex_rfc0005_s8_scope | 28 / 0, 64 | 28 / 0, 120 |
| tsymex_rfc0005_s8ab_letaudit | 28 / 0, 169 | 28 / 0, 160 |
| tsymex_rfc0005_s8ac_remainder | 19 / 0, 120 | 19 / 0, 119 |
| tsymex_rfc0005_s8ag_indexsplit | 15 / 0, 123 | 15 / 0, 117 |
| tsymex_rfc0005_s8am_remainder | 29 / 0, 71 | 29 / 0, 86 |
| tsymex_rfc0005_s8an_remainder | 25 / 0, 118 | 25 / 0, 197 |
| tsymex_rfc0005_s8ao_remainder | 11 / 0, 60 | 11 / 0, 75 |
| tsymex_rfc0005_s8ap_remainder | 36 / 0, 96 | 36 / 0, 163 |
| tsymex_rfc0005_s8aw_remainder | 31 / 0, 70 | 31 / 0, 128 |
| tsymex_rfc0005_s8ay_remainder | 38 / 0, 111 | 38 / 0, 156 |
| tsymex_rfc0005_s8b_substitutions | 26 / 0, 92 | 26 / 0, 112 |
| tsymex_rfc0005_s8bb_captures | 13 / 0, 92 | 13 / 0, 166 |
| tsymex_rfc0005_s8bb_capvalues | 1 / 0, 32 | 1 / 0, 74 |
| tsymex_rfc0005_s8bb_capvalues_lf | 1 / 0, 55 | 1 / 0, 132 |
| tsymex_rfc0005_s8bb_capvalues_plus | 1 / 0, 61 | 1 / 0, 100 |
| tsymex_rfc0005_s8bb_constructs | 7 / 0, 73 | 7 / 0, 79 |
| tsymex_rfc0005_s8bb_exhaustive | 2 / 0, 69 | 2 / 0, 38 |
| tsymex_rfc0005_s8bb_remainder | 21 / 0, 101 | 21 / 0, 132 |
| tsymex_rfc0005_s8bb_replace | 7 / 0, 116 | 7 / 0, 197 |
| tsymex_rfc0005_s8bb_selection | 4 / 0, 95 | 4 / 0, 101 |
| tsymex_rfc0005_s8bi_remainder | 45 / 0, 128 | 45 / 0, 173 |
| tsymex_rfc0005_s8bq_remainder | 62 / 0, 140 | 62 / 0, 177 |
| tsymex_rfc0005_s8d_typeheads | 17 / 0, 74 | 17 / 0, 106 |
| tsymex_rfc0005_s8f_witness | 29 / 0, 85 | 29 / 0, 130 |
| tsymex_rfc0005_s8k_bounds | 19 / 0, 89 | 19 / 0, 116 |
| tsymex_rfc0005_s8l_exits | 50 / 0, 90 | 50 / 0, 125 |
| tsymex_rfc0005_s8o_termination | 14 / 0, 66 | 14 / 0, 90 |
| tsymex_rfc0005_s8p_precision | 30 / 0, 90 | 30 / 0, 142 |
| tsymex_rfc0005_s8s_precision | 29 / 0, 109 | 29 / 0, 218 |
| tsymex_rfc0005_s8u_precision | 17 / 0, 83 | 17 / 0, 167 |
| tsymex_rfc0005_s8x_vm_alias | 7 / 0, 9 | 7 / 0, 22 |
| tsymex_rfc0005_s8z_remainder | 37 / 0, 122 | 37 / 0, 254 |
| tsymex_snd1_uncertain_taint | 5 / 0, 68 | 5 / 0, 110 |
| tsymex_snd3_loopdegrade | 7 / 0, 80 | 7 / 0, 124 |
| tsymex_tot1_totality_corpus | 21 / 0, 65 | 21 / 0, 122 |
| tsymex_typebridge_variants | 3 / 0, 10 | 3 / 0, 27 |

## Different mechanisms, reported and not fixed here

These are also committed in the RFC under "As landed (S8bq)".
- **PRECISION:** iterating a builtin set (`for x in s`) declines, classified.
- **PRECISION:** a set conversion between two different domains (a hidden conversion) declines (`feUnsupportedExprKind`).
- **PRECISION:** a pigeonhole-hard `card` query (comparing the cardinalities of large symbolic sets) can be sxUnknown under `seqQueryRLimit`.
- **PRECISION:** some `newSeqUninit` reads taint more than the element they read:
  - inline `map`/`filter`/`fold` over a possibly-unwritten seq taint the whole path in-band;
  - a seq nested in a composite call result declines its binding;
  - a slice, a heap cell or a mapped array that mentions a base counts as unwritten everywhere.

## Untracked, not staged

`tests/probe/` (pbq_re.nim, pbq_shapes.nim, pbq_rt*.nim, pbq_bs.nim, pbq_un.nim and its .nims).
