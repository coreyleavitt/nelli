# S8bv progress
- Worktree /home/corey/tmp-usage/work/wt/s8bv, branch rfc-0005-s8bv (pushed, upstream set). Scratch: /home/corey/tmp-usage/work/s8bv-work/ (run.sh = pause-aware runner; probe.sh = engine probe; probe/ = probes; logs/)
- d2533c7: RFC row pending added.
- Uncommitted: walker 226 + CR2 pin; item 1 parser arm (dsl_parser itemsArgDirect + itBitSet for-arm, maxBitSetIterDomain=256 in types.nim); symex.nim witness fix: set[range[..]] param rendered as set[int] (compile abort) -> range[T(lo)..T(hi)]; tests/tsymex_rfc0005_s8bv_remainder.nim item 1 pins.
- Item 1 RED observed (all sxUnknown "unsupported for-loop container kind: itBitSet"). GREEN: E4 ok, set[char] fixture hangs (>900s) -> diagnosing (probe/it1.nim).
- ITEM 2 (coordinator decision): premise false (Nim 2.2.10 has no cross-domain set conversion; probes probe/conv*.nim, e2.nim).
  (a) delete unreachable decline arm in own commit with evidence; (b) pin native retyping + element check;
  (c) report as "spec-assumption finding plus replacement scope (coordinator-approved)".
  REPLACEMENT SCOPE IN THIS SLICE: enum subranges: set[range[a1..a2]] over enums; range[a1..a2] enum params/locals/fields incl RangeDefect on assignment/conversion; card/in/iteration/set ops over subrange. Native pins, RED first.
- Items 3, 4 not started.

## Update (after 49559bf)
- 07f5e5b WIP item 1 GREEN (14/14). Includes bvSignedInterval/bvOverflowDischarged (runtime.nim): signed-BV overflow obligations discharged by structural intervals (needed: set[char] iteration with inc k ran minutes). S8bq bsIter repinned to sxSat.
- 49559bf WIP item 2 GREEN (27/27 total): enumRange IRType field, classifyEnumSubrange (typebridge), subrangeMemberEnum (parser sym arm), witness range[E(lo)..E(hi)] via witnessIntAs, dead set-conv arm deleted (needs own commit in final history).
- Item 2 RED (base, logs/item2-red.log): SubHolder SE field witness compile abort; params/sets sxUnknown; SOUNDNESS: bv_sub_assign_out false sxSat (x: SE == e0), assign/conv/arg RangeDefect false sxUnsat.
- Item 1 RED: all sxUnknown "unsupported for-loop container kind: itBitSet"; set[range] param witness compile abort ("set is too large") fixed in symex.nim.
- Next: item 3 (card PB encoding, measure before/after both Z3), item 4 (newSeqUninit precision). Remove TIMING echo from verdict template before final.

## Update (item 3 + 4 in progress, uncommitted in runtime.nim + test file)
- Item 3: bsPopcount + bitSetCardFacts (pairwise part identities) added to checkCapped rootsIn. RED observed (logs/item3-red.log: 4 pins sxUnknown at 20M). GREEN not yet run (gate-sweep pause since 18:25).
  Before/after: logs/card-before-{51,413}.txt, card-after-{51,413}.txt, card-units.txt (raw SMT2 bench, bv_* vs spl_*).
- Item 4 code written (not yet compiled): uninitReadConds sink + drainUninitReads stage (rskUninitRead); hofElemAt deposits; noteUninitReturn recursive over composites; uninitAt handles array map, heap select chains, slice lambdas. Fixtures in test file (bv_un_*).
- Next: after pause lifts: item 4 RED = stash runtime.nim (HEAD 49559bf lacks items 3/4) and run; then GREEN full.

## Update (2e423b9 wip(symex): RFC-0005 S8bv -- items 3 and 4, card part identities, newSeqUninit precision)
- All items GREEN on Z3 5.1 c: tsymex_rfc0005_s8bv_remainder 27/27 (items 1,2), tsymex_rfc0005_s8bv_card_uninit 13/13 (items 3,4). Both registered in nelli.nimble.
- Item 4 RED logs: logs/item4-red.log (7 failed at base), logs/item4-mapped-red.log.
- Next: batch verification (s8bv-work/batch.sh, list s8bv-work/verify-list.txt + card_uninit) on 51 then 413; cpp run; repin collateral; RFC as-landed; final history; Windows CI.

## Update (verification running)
- Z3 5.1 batch launched over 173 suites (s8bv-work/verify-list.txt -> results-51.txt), 3 concurrent, pause-aware; 15/173 done, 0 failures so far. Host heavily shared, ~3 min/suite.
- Uncommitted: n27 marker count repin (94 -> 93, noteUninitReturn now 4 marked lines), RFC As-landed draft (verification/repins TBD).
- Windows CI at 2e423b9: fuzzer-mingw success; fuzzer-msvc, symex-mingw in progress. The 07f5e5b symex-mingw red (s8bq bsIter decline pin) was fixed by the repin in 49559bf (green).

## Resume 2026-11-02 (new agent; prior agent gone since 2026-10-04)
- Head at resume 59ebe5a. Host 12 cores; cap for this job is 2 concurrent runs. batch.sh capped accordingly.
- Stale 5.1 results and logs moved to s8bv-work/dead/ (evidence of those runs at that sha only).
- TIMING echo: already gone from committed tests since 2e423b9 (only scratch test-full.nim has it). Closed.
- No force-push on this resume: the final history (with the dead-arm deletion in its own commit) goes on a new branch rfc-0005-s8bv-final, tree-identical to rfc-0005-s8bv.
- Verification list: s8bv-work/ordered.txt (job-criteria suites first, then the prior wider list). Re-verifying everything on the head.
- 59ebe5a: s8bv_remainder 27/27, s8bv_card_uninit 13/13 on 5.1 c, observed this resume. Queue s8bv-work/q1.txt running (results.txt, 2 concurrent, rows carry sha): required on 51, then 413, cpp, then the wider list.
- Coordinator rule (2026-11-02): DONE report must include per-file Windows times from symex-mingw logs for the report's Windows sha; 60 s convention checked at integration. Keep provisional walker 226.
- 60 s convention: tsymex_rfc0005_s8bv_remainder took 136.1 s compile+run on symex-mingw at b999ff6 (37180630597), over budget; splitting. card_uninit 46.9 s.
- Split remainder into iter_order/iter_forms/subrange/subrange_sets (1ad5521, pushed); 5.1 c 30/30 green. Next: 413 + cpp, Windows per-file times.
- Coordinator rule: push only when a Windows result is needed or ~every 30 min; cancel own queued/in_progress runs before pushing a new tip; final DONE sha must have all 3 legs green.
- 1ad5521 symex-mingw 41430397416 green, but iter_order 102.4 s (84 s compile; set[char]/set[int8] verdicts). Compile probes in s8bv-work/probe/io: floor about 22 s local, a verdict over a 256 domain +4-6 s, a second verdict on one such fixture +12 s. Re-splitting into iter_order, iter_char, iter_int8, iter_forms.
- d4b3ece pushed for a Windows result (iter split). Rows in results-split2.txt marked sha=1ad5521 were that tree uncommitted, tests only; re-run at the final sha.
- Merging e497dcf (walker 245, nim-z3 cc5ffc9) into the branch, uncommitted: conflicts resolved by s8bv-work/resolve.py and resolve_rfc.py. Walker 250. _deps/z3 at cc5ffc9, tree identical to milpa cas identity 9a033beb. Pre-merge results moved to dead/pre-merge; they do not certify the merged tip.
- Merged tree: iter_order hung 400 s (rc=137) in guardLiteral's $simplify printing (ast_to_string) a guard over the unrolled counter; fixed by reading the literal with Z3_get_bool_value (guardLiteral, loopArmInfeasible). Uncommitted. Other $simplify sites remain.
- Merge and fix committed locally. Verification queue s8bv-work/q7.txt -> results-m.txt at the merged code (rows carry sha). Then: RFC with the Edit tool, push (a docs tip still gets legs because the push range holds code), Windows times, report.

[2026-11-02 16:15] Merged-tree queue running at 14266a8 (385 runs, 5 done, no failures so far). Windows legs on 14266a8 in progress: fuzzer-msvc 41535445001, fuzzer-mingw 41535445002, symex-mingw 41535445004 (queued). RFC header, re-pins, guardLiteral note and different mechanisms written, uncommitted; Verification still TBD. Workflows have no workflow_dispatch and ignore docs-only pushes, so the final tip needs a non-docs change to get its own legs: plan is to raise the seven S8bv floor pins to >= 250 with the docs commit, then rerun those seven suites.

[2026-11-02 16:55] 14266a8 legs green: fuzzer-msvc 41535445001, fuzzer-mingw 41535445002, symex-mingw 41535445004. iter_order 60.2 s on Windows, over convention: moved set[char] test to iter_char (uncommitted). Floors to >= 250. This test change gives the final tip its legs. Rerun the 7 suites after the queue finishes, to keep cap 2.
