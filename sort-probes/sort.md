# RFC-0005 release-blocker sort: 6cbfe8f (main) against e497dcf (channel)

## How to read this

- Every verdict is **observed** on `scripts/dt-bounded.sh c`, Z3 5.1.0 (the image's), PCRE 8.45 without JIT, Linux, unless the row says otherwise. The two rows marked WORKER come from the worker's table and were not re-run, at the coordinator's instruction. Z3 4.13.4 was not run: it is not on this host.
- "Native" is a native run of the same SUT in the same probe file. HIT means a native input reached the label; no means none of the inputs tried did. A native "no" is exhaustive only where the row says so.
- "Fix" names a branch or slice. Where the fix is on a branch, the claim that it fixes the item comes from the worker report or RFC text. **I did not re-run any probe on a fix branch, except `p_fp` at 28ab1a7.**
- Deps: main uses nim-z3 d3ae858 (dag-sha256:9b181a87), channel uses cc5ffc9 (dag-sha256:9a033beb), each matching its own `milpa.lock`.
- Probes are in `probes/`, logs in `logs/<probe>.<main|chan>.<c|cpp>.log`.
- `compile-stop` means `symexFind`'s macro aborted the compile on valid input. I treat it as neither a verdict nor a decline. Rows where main is a compile-stop and the channel gives a false verdict are classed BLOCKER, and they say so, because the definition asks for "a correct verdict or a decline".
- Labels on a `k + 1` SUT can show `sxRaised` because the overflow at `high(int)` is real. Those are not counted as false. The hook family was re-probed without the overflow in `p_hook2`.

## Blockers

| # | Item | Source | Shape | 6cbfe8f | e497dcf | Native | Class | Fix | Probe |
|---|---|---|---|---|---|---|---|---|---|
| B1 | Store through a pointer to a global the path only read | S8cd, coordinator family 1 | Worker's `p_scalar`, plus tuple field, array element, seq element, two pointers. Cause per the worker: `ptrTargets` scans only globals bound on the path | WORKER: sxUnknown (feGlobalReadUnmodelled) or compile failure | WORKER: false sxUnsat with feGlobalHavoc | WORKER | BLOCKER | rfc-0005-s8cd 6fe7cff (worker, local until pushed) | worker's |
| B2 | Set expression evaluation order | S8cd, coordinator family 2 | `(s + {x}) + f()`, `b2(s <= {A}, f())`, `i2(card(s + {x}), f())`, `f2({k}, g())`. Cause per the worker: `isEagerIR` lacks `iekBitSet` | WORKER: sxUnknown or compile failure | WORKER: false verdict | WORKER | BLOCKER | rfc-0005-s8cd | worker's |
| B3 | Direct by-value seq whose global the callee writes | S8cq 1 | `gWrite(gs)` | sxUnknown (fault, KeyError) | r==50 false sxUnsat; r==x false sxSat | r==50 HIT, r==x no | BLOCKER | S8cq, not started | p_cq `dg_*` |
| B4 | Direct by-value large object | S8cq 1 | `gWriteBig(gBig)`, 16 ints | sxUnknown | r==50 false sxUnsat with feGlobalHavoc; r==x sxUnknown | r==50 HIT | BLOCKER | S8cq | p_cq `bg_*` |
| B5 | Nested closure writes its capture, received by value | S8cq 1 | `inner(s)` | sxUnknown (fault) | false pair | r==50 HIT | BLOCKER | S8cq | p_cq `in_*` |
| B6 | A nested call writes the by-value global | S8cq 1 | `outerR(gs)` | sxUnknown (fault) | false pair | r==50 HIT | BLOCKER | S8cq | p_cq `ou_*` |
| B7 | A call evaluated twice under inc, dec, swap, += | S8cq 3 | `inc(getR()[])`, `dec(...)`, `swap(getR()[], y)`, `getR()[] += 1` | sxUnknown, all four | once false sxUnsat, twice false sxSat, all four | once HIT, twice no | BLOCKER | S8cq | p_cq `ir_ dr_ sr_ pe_` |
| B8 | A call evaluated twice under setLen | S8cq 3 audit | `getSeqR()[].setLen(1)` | sxUnknown | once false sxUnsat, twice false sxSat | once HIT | BLOCKER | S8cq | p_cq `sl_*` |
| B9 | setLen's length argument writes the seq | S8cl item 3 (coordinator 3) | `gs = @[1]; gs.setLen(growG())` | sxUnknown | `gs[1]==5` false sxUnsat; `gs[1]==0` false sxSat | ==5 HIT, ==0 no | BLOCKER | S8cl 2271cb1 | p_cd `sg_*` |
| B10 | ensureMove of a seq | S8cb | `let b = ensureMove(a)`, `a: seq` | sxUnknown (retBindEq) | `b.len==1` false sxUnsat; `b.len==0` false sxSat | ==1 HIT | BLOCKER | S8cb 28ab1a7 | p_cb `ems_*` |
| B11 | PCRE stop code read as no-match, find | S8cf 1, 2 | `find(re"(a|a)*[bc]") == -8` at a^30 | sxUnknown | false sxUnsat | HIT | BLOCKER | S8cf a0824d0 | p_cf `cf_find_code` |
| B12 | PCRE stop code, replace | S8cf 1, 2 | `replace(re"(a|a)*[bc]|a","x") == s` | sxUnknown | false sxUnsat | HIT | BLOCKER | S8cf | p_cf `cf_replace_stops` |
| B13 | PCRE stop code, matchLen and findBounds | S8cf 1, 2 | `matchLen(...) < -1`, `findBounds(...).first < -1` | compile-stop | false sxUnsat | HIT | BLOCKER (main is compile-stop) | S8cf | p_cf |
| B14 | A subject that matches can read as a miss | S8cf; S8co 10's area | `s[s.len-1]=='c' and not s.contains(re"(a|a)*b|c$")` | sxSat, correct | false sxUnsat | HIT at a^30 c | BLOCKER | S8cf by report (altPlus moved to unknown); this exact shape not run there | p_cf3 `alt_miss*` |
| B15 | uncheckedAssign, branch-changing | S8cp 2 | `{.cast(uncheckedAssign).}: o.k = kC` | live sxSat, dead sxUnsat, correct | false sxRaised on both | no raise; live HIT | BLOCKER | S8cp, not started | p_cp `ua2_*` |
| B16 | uncheckedAssign, read the other arm | S8cp 2 | as B15, then `o.y == v` | sxSat, correct | false sxRaised | HIT | BLOCKER | S8cp | p_cp `ua3_same` |
| B17 | Replay kills the host: real quit | S8cp 3 | `if gG == 0: quit(7)`; via a callee; label then quit | sxUnknown (feGlobalReadUnmodelled) | process dies, no verdict | the SUT really quits | BLOCKER | S8cp 3 covers quit | p_q5, p_q7, p_q10 |
| B18 | Replay kills the host: nil deref | not on any list | `if gG == 0: gN[] = 1` | sxUnknown | process dies, SIGSEGV | really faults | BLOCKER | none: S8cp 3 names exit only | p_q8 |
| B19 | Replay kills the host: unbounded recursion | not on any list | `if gG == 0: discard rec(k)` | sxUnknown (depth budget) | process dies, call depth limit | really overflows | BLOCKER | none | p_q9 |
| B20 | Replay stack: 3 MiB frame on a 16 MiB foreign thread | S8cb | opaque calling a 3 MiB frame, symexFind from a raw pthread | sxSat, correct | process dies | ok; label hit on that thread | BLOCKER | S8cb 28ab1a7 | p_frame |
| B21 | cpp compile failure on a SUT with `std/atomics` | S8cp 5, S8cl 5 | `tsymex_r6_n42_deref_taint`, `tsymex_r6_n43_parity`, cpp | both suites pass, rc 0 | g++ error, deleted `std::atomic` operator= | n/a | BLOCKER | S8cl 2271cb1 by its RFC note. Reports call this pre-existing, which holds only against 136ad60, not main | tests' own, logs `*.cpp.log` |
| B22 | Hook write unseen, global read first | not on any list; coordinator's pattern | `let a = gW; block: var d = mkD(k); ...; if gW != a` where `=destroy` writes gW. Scope exit, callee local, named callee, overwrite, loop, tuple field, seq of it, `reset` | sxUnknown, all eight | false sxUnsat with feGlobalHavoc, all eight | HIT, all eight | BLOCKER | none. S8cp 1 names `=destroy` for the replay footprint only | p_hook2 `k1`-`k8`, p_havoc2 `a1` |
| B23 | Hook write unseen, global written first | not on any list | `gW = 0; block: var d = mkD(k)...; if gW == 1` | sxUnknown (fault) | `==1` false sxUnsat, `==0` false sxSat | ==1 HIT | BLOCKER | none | p_hook2 `w1_*`, p_cp `dg1_dead dg3_dead` |
| B24 | Opaque write behind a local alias or plain callee | not on any list; coordinator's pattern | `{.symexOpaque.}` doing `let p = gPtr; p[] = 9`, `let o = gPH; o.p[] = 9`, `o5a(gPtr)`, `var c = gPtr; c[] = x` | sxUnknown, all | false sxUnsat with feOpaqueEffectHavoc | HIT | BLOCKER | none | p_hook2 `n1 n2 n5 n13`, p_havoc2 `b8` |
| B25 | Opaque write inside a hook | not on any list | opaque with a local whose `=destroy` writes gW, directly or via a plain callee | sxUnknown | false sxUnsat with feGlobalHavoc | HIT | BLOCKER | none | p_hook2 `n6 n7`, p_havoc2 `b9` |
| B26 | Opaque write inside `{.emit.}` | not on any list | opaque with `{.emit: "gCw = gCw + 1;".}` | sxUnknown | false sxUnsat with feGlobalHavoc | HIT | BLOCKER | none | p_hook2 `n11` |

## No class fits: worse than main, but main is also wrong

The classes do not cover "main gives a false verdict, the channel kills the process". These are counted apart. I recommend treating them as blockers.

| # | Item | Source | Shape | 6cbfe8f | e497dcf | Native | Fix | Probe |
|---|---|---|---|---|---|---|---|---|
| W1 | Raw C exit behind an opaque | S8cp 3 | `proc qOp {.symexOpaque.} = cExit(7)` | false sxSat | process dies | never reaches the label | S8cp 3 | p_q4 |
| W2 | Quit behind a proc value behind an opaque | S8cp 3 | `{.symexOpaque.} = gV()`, gV calls quit | false sxSat | process dies | never reaches the label | S8cp 3 | p_q6 |

## Same on both

| # | Item | Source | Shape | 6cbfe8f | e497dcf | Native | Fix | Probe |
|---|---|---|---|---|---|---|---|---|
| S1 | Direct var-returning actual | S8cq 2 | `rab(t["a"], t, "a")` | false pair | same false pair | r==x+1 HIT | S8cq | p_cq `vc_*` |
| S2 | `$` of a negative int | S8cb, S8cl | `$x == "-5"`, `($x).len == 2`, `$x == ""`, `repr(x) == "-5"` | false sxUnsat, sxUnsat, sxSat, sxUnsat | same | as expected | S8cb | p_cb |
| S3 | `$` of a char | S8cb | `$a == "a"`, `$a == "97"` | false sxUnsat, false sxSat | same | "a" HIT | S8cb | p_cb |
| S4 | `$` of an enum | S8cb | `$a == "ea"`, `$a == "0"`, string-named enum | false sxUnsat, false sxSat, false sxUnsat | same | names HIT | S8cb | p_cb |
| S5 | ensureMove of an int | S8cb | `b == 0 and x != -1` | false sxSat | same | no | S8cb | p_cb `em_dead` |
| S6 | procCall zero value | S8cl, coordinator 4 | `r == 4 and k != 3` | false sxSat | same | no | S8cl 2271cb1 | p_cb `pc_dead` |
| S7 | uncheckedAssign, the other arm's bytes differ | S8cp 2 | `o.y != v` | false sxSat | false sxRaised (different wrong verdict) | no | S8cp | p_cp `ua3_diff` |
| S8 | A hook write through a local ref | hook family | `DR(r: r)`, hook writes `d.r[]` | false pair | same | r==1 HIT | none | p_cp `dg2_*` |
| S9 | A hook on overwrite, global written first | hook family | `gW = 0; var d = mkD(k); d = mkD(k)` | false pair | same | ==1 HIT | none | p_hook2 `w2_*` |
| S10 | PCRE stop read as true | S8cf 1 | `s.match(re"(a|a)*[bc]")` at a^30 | false sxUnsat | same | HIT | S8cf | p_cf `cf_match_hit` |
| S11 | PCRE stop as a witness | S8cf 1 | `not s.match(...)` at a^30 | false sxSat | same | no | S8cf | p_cf `cf_miss_long` |
| S12 | Compile-stop on `create` and `GC_ref` | S8cl 1, 2 | `create(int)`, `GC_ref(p)` | compile-stop | compile-stop | run fine | S8cl names GC_ref and create as declines | p_wm `m4 m6` |
| S13 | Compile-stop on a sort callback | found here | `s.sort(proc ...)` | compile-stop | compile-stop | runs fine | none | p_havoc2 `a15` |

## Improved

| # | Item | Source | 6cbfe8f | e497dcf | Probe |
|---|---|---|---|---|---|
| I1 | uncheckedAssign keeping the branch, dead label | S8cp 2 | false sxSat | correct sxUnsat | p_cp `ua1_dead` |
| I2 | Opaque quit, direct, via a callee, with addExitProc | S8cp 3 | false sxSat | decline (feOpaqueCallUnmodelled) | p_q1 p_q2 p_q3 |
| I3 | `wasMoved` on int, seq, through a pointer | S8cl 2 | compile-stop | correct | p_wm `m1 m2 m3` |
| I4 | `move` of a seq | S8cl 1 audit | compile-stop | correct | p_cb `mv_*` |
| I5 | newString length, dead label | S8cl 4 | false sxSat | decline | p_wm `m7_dead` |
| I6 | var seq parameter aimed at the global (found here) | havoc pattern | false sxUnsat with feGlobalReadUnmodelled | decline | p_havoc `h14` |
| I7 | setLen with one-branch length bound | S8cn 1 adversarial | false pair | live decline, dead correct | p_cn/p_cn3 `ob_*` |
| I8 | setLen past 4096 | S8cn 1 adversarial | SIGSEGV inside Z3_solver_check | decline | p_cn `past_*` |
| I9 | grow_pad labels | S8cn 1 | false sxRaised on dead, sxRaised on live | correct pair | p_cn `grow_pad_*` |
| I10 | A long regex subject | S8cf | killed at 400 s | decline in time | p_cf2 |
| I11 | Short subject, `(a|a)*b|c$` | S8cf | false sxSat | correct sxUnsat | p_cf3 `alt_short` |

## Not reproduced on e497dcf

| # | Item | Source | What I tried | Observed |
|---|---|---|---|---|
| N1 | Step 1d false UNSAT | S8cn 1 | `grow_pad_dead`, native exhaustive over s.len 0..8, n 0..12, three fill bytes; length one past 4096; bound on one branch; bound only sequence theory gives; real models at 70000, 150000 and 300000 bytes; 24 labels over find, rfind, substr, setLen, NUL bytes and byte bounds, native exhaustive to length 4 on {a, b, x} | No false verdict. Past-cap models all decline. This is a probe of the facts' effects, not the written audit of each fact the job asks for |
| N2 | Three replay footprint gaps | S8cp 1 | A spinning opaque abandoned at 100 ms that writes through a hook, a shared C static, or a program-set proc variable, then a reader; at e497dcf **and at 28ab1a7**, where the footprint exists | sxSat, correct, on both. The hanger is sxUnknown. My reader may not race the writer reliably, so this does not prove the gap absent at 28ab1a7, and S8cb's report still lists it |
| N3 | rc=139 of p7 | S8cb note, S8cp 4 | Reconstructed from the report's one line; the original probe is not available. 200 runs per sha, c only, no valgrind or ASan | 200 of 200 rc 0 on each. **The cause stays unknown** |
| N4 | Z3's `m_cache.mk_unique` check | S8cj 2 | `x*y == 6999433`, x and y below 200000, both forms | Message absent; sxSat and sxUnsat correct on both. S8ci's report gives different figures; I did not establish why |
| N5 | unsafeNew | S8cl 1 | Nil check and a write through it | Main sxUnknown (walker fault or global read); channel sxUnknown (feUnsupportedOp, unregistered `unsafeNew`). The false verdicts in S8cl's text were seen only at 8cef160 |
| N6 | `setLen(a[gi], bump())` | Coordinator 3 | Module-level `array[2, seq[int]]` | Correct on channel: `sa1_len3` sxSat with native HIT, `sa0_len3` sxUnsat with native no. Main sxUnknown. My global-array form may differ from S8cl's shape, which I did not have |
| N7 | Thread variable behind a same-signature routine | S8cb | `tvBehind` | Declines (feReplayRefuted), no false verdict |
| N8 | Hook routes the walker does see | havoc pattern | `p_havoc` 22 routes, `p_havoc2` others: var formal, addr, proc value, method, iterator, converter, setter, defer, finally, opaque with a direct write | Correct or declining, except the rows above |

## Unverifiable

| # | Item | Source | Why |
|---|---|---|---|
| U1 | JIT stack limit -27, false sxUnsat | S8cf 1, 2 | Needs a JIT build. The image's 8.45 has none: observed `a2000.find` = -1, not -27, and the verdict there is right for this library |
| U2 | 8.39 JIT's 113 prefix-scan differences; 8.44, 8.39 and 8.37 class behaviour | S8cf 12, S8co 2, 8 | Needs those PCRE builds or the Windows legs |
| U3 | Stack size on macOS and the BSDs | S8cp 6 | Never run there. Needs those hosts; no zig or sysroot attempted |
| U4 | `v == f` segfault in `regexRecDefConds` | S8co 1 | S8cf's own discarded encoding. Reaching it needs an engine change, and no SUT at e497dcf expresses it |
| U5 | The October notes' false sxUnsat "on a SUT nobody reproduced" | S8cl 1 | The SUT does not exist to run; `s8ca-work/` is on the worker |
| U6 | `z3ApiErrorCount` over-count changing a verdict | S8ck 6 | I could not build a SUT that gives a caught API error on demand. From reading only, `runtime.nim:26026` turns the count into sxUnknown, so an over-count looks like a decline. Read, not observed |
| U7 | `tregex_index` hang reachable from the walker | S8ck 4 | The nim-z3 suite's shape was not ported into a probe. A hang is outside this sort's soundness definition, but it is not checked |
| U8 | All of the above on Z3 4.13.4 | general | That library is not on this host |

## Excluded as precision, read from the jobs, not probed

S8bv all; S8bz all (its branch's "store through a pointer" fix relates to B1); S8cd items other than families 1, 2; S8cg 2-8 (item 1, `viewFollows`, is recorded as fixed by S8ca; not probed); S8ch; S8ci; S8cj 1; S8ck 2, 3, 5, 7-12 (leaks, tooling, docs; S8ck 1, the nim-z3 valgrind gate and examples, was not run either); S8cl 3, 4 except where listed; S8cm (CI only); S8cn 2-6; S8co 3-9; S8cp 7, 8; S8cq 4.
