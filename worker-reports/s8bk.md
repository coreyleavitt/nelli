# S8bk -- DONE

- **sha:** 9ce7fdb on `rfc-0005-s8bk` (pushed). History: 6359c76 `docs(rfc): 0005 -- add the S8bk row`, then 9ce7fdb `feat(symex): RFC-0005 S8bk -- a by-address argument's address is taken at the call`.
- **base:** built on d42204d (batch 3, walker 209). After the push I rebased onto origin/rfc-0005-soundness-channels 621af8f, which holds batch 3's own fixes; the walker there is still 209. The reason: d42204d's own symex-mingw run (37066358068) is red on s8ar, s8at, s8au, s8ba and s8bd, and my first push inherited those exact reds (37070986692). 621af8f fixes all five.
- **walker:** 209 -> 212. The CR2 `==` pin is updated to 212 and run (6/0 on both versions). The `>= 212` floor is in the new suite.
- **Job:** REVISION 1, the late-address design.

## RED and GREEN observed
New suite `tests/tsymex_rfc0005_s8bk_argtiming.nim`, registered in nelli.nimble: 9 tests and 33 labels.
- **Time per backend:** the binary runs in about 3 s; the full run, compile included, took 57-103 s (c) and 184 s (cpp) on the shared, loaded host.
- **RED at the base (Z3 5.1):** the suite was 2/9 (`nim` and `fw` passed).

Per-label verdicts, base -> head:

| label | base | head | what it is |
|---|---|---|---|
| cp / cp_dead | sxUnsat / **sxSat** | sxSat (replays roConfirmed) / sxUnsat | copy-in/out, `touch(gP.x, moveP())`; the witness is `old.x == k, gP.x == 105`, i.e. native `old.x=10 gP.x=105` |
| co / co_dead | sxUnsat / **sxSat** | sxSat (roConfirmed) / sxUnsat | the later call writes the old object, then rebinds it (`old.x == 50`) |
| gd / gd_dead | -- | sxSat (roConfirmed) / sxUnsat | the call is an `if` condition (added after the base run) |
| ch / ch_dead | sxUnsat / **sxSat** | sxSat / sxUnsat | field-of-field chain rebound partway (`gO.inner.x`) |
| ar, sq / dead | sxUnsat / **sxSat** | sxSat / sxUnsat | an array or seq element the later call writes |
| fw / fw_dead | sxSat / sxUnsat | same | a `var` formal forwarded on; already right |
| ad / ad_dead | sxUnsat / **sxSat** | sxSat / sxUnsat | S8an `addr` cell |
| ai / ai_dead | sxUnsat / **sxSat** | sxSat / sxUnsat | `addr gArr[gi]` cell, element written by the later call |
| ar2 / ar2_dead | sxSat / sxUnsat | same | `addr` by reference; already right |
| rs / rs_dead | sxSat / sxUnsat | same | by-reference symbol base `gP`; already right, now pinned |
| re / re_dead | sxUnsat / **sxSat** | sxSat / sxUnsat | S8bd element base `gA[gi].x`, the element rebound |
| rc / rc_dead | sxSat / sxUnsat | same | call base `getB().x`: eager, called once, writes the OLD box (native `old.x=15 gP.x=100 calls=1`) |
| ik / ik_dead | sxUnsat / **sxSat** | sxSat / sxUnsat | index unchanged by the later call: exact |
| im, am, rm | sxUnsat (Nim reaches them) | sxUnknown, feEvalOrderUnmodelled "never checked" | the later call moves the index (var, addr, by-ref element) |
| ss | sxRaised | sxUnknown, feEvalOrderUnmodelled | the later call shortens the seq after its bound check |
| hx | -- | sxUnknown, feEvalOrderUnmodelled | a check no snapshot carries (`gH.s[gi]`) |

**Vertical TDD caveat.** RED was observed for the whole first set of pins at once, then GREEN was observed for all of them together. These later pins were added afterwards and run GREEN at head: `ar2`, `ai` and `am` (base verdicts measured), and `hx` and `gd` (base not measured).

## Soundness bugs found
- **SOUNDNESS (the slice's subject).** Nim takes a `var`/`addr` actual's address at the call, after every later argument (`T1_ = moveP(); touch(&(*gP).x, T1_);`), with an index's bound check where the argument stands. The walker read the value early and wrote back through the late address. This affected copy-in/out, the S8an addr cell, and the S8bd by-reference element base (index read early). The result was false sxSat for dead labels, and false sxUnsat or sxRaised where Nim reaches the label or has undefined behaviour.

## Design
1. **Late reads.** `userCallStmt` records, per by-address argument, a `LateAddr` covering:
   - the preamble span of the lvalue's lowering;
   - the statements that bind it for the call (the copy-in temporary; the S8an cell's `isNew` and store; nothing for a by-reference base);
   - which indices on the path index a growable container (anything but an array; `lvalueIndexGrowable`).

   In `orderOperands`, a fixed operand with a `LateAddr`, when a later argument may write, goes through `placeLateAddr`:
   - its trailing lazy reads and binding move after the last argument, so copy-in, the cell fill and the by-ref base read all happen at the call;
   - the copy-out (which re-parses the lvalue after the call) writes through that same late address;
   - an eager part stays where it stands and is evaluated once.
2. **Checks at Nim's position.** Each moved index check snapshots its index and, for a growable container, `len`, where the argument stands. A path on which either changed declines `feEvalOrderUnmodelled` before the access, with the message "Nim accesses through a value it never checked". UB is never modelled. A check the snapshot cannot carry (its index or container is itself a moved read, e.g. `gH.s[gi]`; a variant-arm field) keeps the lvalue in place, and the call declines whenever a later argument may write (pinned by `hx`).
3. **Call base eager.** `getB().x`: the call is not lazy, so it stays and is called once (`rc`, `gCalls == 1`).
4. **Symbol base.** `gP` was already read at the call; pinned by `rs`.
5. **Proc-variable forms.** Not implemented: S8bh is not on this base. Natively they behave like the direct call. Left to S8bh's integration, as the coordinator directed.
6. **Native pins.** The `nim` test asserts every native outcome. `cp`'s witness (`old.x=k, gP.x=105`) replays roConfirmed beside its dead twin.

**Audit.** Every user call reaches `userCallStmt`: the expression call and the three statement-position arms. `parseOrderedArgs` (opaque callees, calls through a proc value) is unchanged. Inside a guard condition nothing is reordered, as in S8ax; the `if touchB(gP.x, moveP()):` form was probed and is exact (`gd`).

## Suites (rebased head 9ce7fdb's tree, c; `ok/failed`)
| suite | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| `rfc0005_s8bk_argtiming` | 9/0 | 9/0 |
| `rfc0005_s8bf_alias` | 13/0 | 13/0 |
| `rfc0005_s8bd_remainder` | 23/0 | 23/0 |
| `rfc0005_s8ba_remainder` | 32/0 | 32/0 |
| `rfc0005_s8ax_remainder` | 52/0 | 52/0 |
| `rfc0005_s8au_remainder` | 35/0 | 35/0 |
| `rfc0005_s8an_remainder` | 25/0 | 25/0 |
| `rfc0005_s8ac_remainder` | 19/0 | 19/0 |
| `rfc0005_s8i_models` | 39/0 | 39/0 |
| `rfc0005_s8_scope` | 28/0 | 28/0 |
| `phase15_CR2_cachekey` | 6/0 | 6/0 |
| `phase14_var_param` | 1/0 | 1/0 |
| `phase14_var_param_downstream` | 2/0 | 2/0 |
| `a3_closure_iterators` | 11/0 | 11/0 |
| `phase12_phase_closure` | 1/0 | 1/0 |
| `phase15_C2a_closure_capture` | 3/0 | 3/0 |
| `phase15_C2b_closure_call` | 3/0 | 3/0 |
| `phase15_C5_closure_eq` | 5/0 | 5/0 |
| `phase15_CR1_CR5_closure_heap` | 5/0 | 5/0 |
| `phase15_r13_closure_ref` | 1/0 | 1/0 |
| `phase16_R16_5_overflow_thru_closure` | 3/0 | 3/0 |
| `r6_n16_closure_zerodefault` | 10/0 | 10/0 |
| `rfc0005_s7_closure` | 37/0 | 37/0 |
| `snd1b_closure_uncertain_axiom` | 4/0 | 4/0 |
| `h_stepC_heapidentity` | 10/0 | 10/0 |
| `h_verification` | 18/0 | 18/0 |
| `h_witness` | 11/0 | 11/0 |
| `phase15_H1_path_heap_fields` | 2/0 | 2/0 |
| `phase15_r10_budget` | 5/0 | 5/0 |
| `phase15_r11b_smoke` | 11/0 | 11/0 |
| `phase15_R1a_ir` | 9/0 | 9/0 |
| `phase15_r1b_callheap` | 2/0 | 2/0 |
| `phase15_r9_recursive` | 3/0 | 3/0 |
| `r6_heap_raise_totality` | 9/0 | 9/0 |
| `163rev_armfield_write` | 4/0 | 4/0 |
| `163rev_assign_rangedefect` | 9/0 | 9/0 |
| `163rev_assign_scope` | 10/0 | 10/0 |
| `163rev_assign_sites` | 33/0 | 33/0 |
| `163rev_concolic_diagnostics` | 25/0 | 25/0 |
| `163rev_concolic_flip_width` | 13/0 | 13/0 |
| `163rev_concolic_modes` | 19/0 | 19/0 |
| `163rev_degrade_classification` | 8/0 | 8/0 |
| `163rev_disc_domain` | 7/0 | 7/0 |
| `163rev_enum_domain` | 19/0 | 19/0 |
| `163rev_enum_field_witness` | 12/0 | 12/0 |
| `163rev_enum_ordinal` | 14/0 | 14/0 |
| `163rev_enum_positions` | 13/0 | 13/0 |
| `163rev_enum_valueshapes` | 9/0 | 9/0 |
| `163rev_frontier_default` | 9/0 | 9/0 |
| `163rev_inert_argfork` | 9/0 | 9/0 |
| `163rev_inert_exclusions` | 15/0 | 15/0 |
| `163rev_int_literal_width` | 27/0 | 27/0 |
| `163rev_intoffset_range` | 9/0 | 9/0 |
| `163rev_nested_clamp` | 5/0 | 5/0 |
| `163rev_parser_gaps` | 10/0 | 10/0 |
| `163rev_range_bounds` | 11/0 | 11/0 |
| `163rev_scan_counter_range` | 10/0 | 10/0 |
| `163rev_seqelem_promoted_int` | 3/0 | 3/0 |
| `163rev_table_elem` | 6/0 | 6/0 |
| `163rev_transparent_guard` | 9/0 | 9/0 |
| `163rev_transparent_result` | 4/0 | 4/0 |
| `163rev_variant_armfield` | 6/0 | 6/0 |
| `rfc0005_s8ar_remainder` | 50/0 | 50/0 |
| `rfc0005_s8at_remainder` | 67/0 | 67/0 |

Totals: 64 suites, 892/0 on 5.1 and 892/0 on 4.13.4. cpp (5.1): `s8bk_argtiming` 9/0.

On the pre-rebase base d42204d the same list was 0 failed, except `s8au` 34/1, `s8ba` 31/1 and `s8bd` 22/1. Each failure was identical to the batch-3 targeted run (`vpr`, B1-1 at 3383328 / 7766466 units, `ge_dead`), and 621af8f fixes all three.

## Windows
- **Final head 9ce7fdb, all success:** symex-mingw 37085817964, fuzzer-mingw 37085818008, fuzzer-msvc 37085817982.
- **Previous head 0ed26c5** (identical code; 9ce7fdb only amends RFC text): symex-mingw 37082189804 success, fuzzer-mingw 37082189532 success, fuzzer-msvc 37082189639 success.

## Different mechanisms, reported and not fixed here
- **PRECISION: an index call in a `var` actual's lvalue.** `touch(gArr[nextI()], f())` declines with `unsupported nnkAsgn shape`, because the copy-out would call `nextI` again. This is present at the base. Natively, `nextI()` is evaluated once where the argument stands and the element is read at the call.
- **PRECISION: a check no snapshot carries.** `touch(gH.s[gi], f())` declines whenever `f` may write, even when `f` leaves `gH` and `gi` alone.
- **Out of scope here (SOUNDNESS on this base): a call through a proc value.** `let f = touch; f(gP.x, moveP())` (natively `old.x=10 gP.x=105`) has no `var` write-back here. S8bh adds it, and its integration takes these forms.

Scratch probes are untracked in `wt/s8bk/probe_s8bk/` (not committed). The `wt/s8bk-base` worktree was removed.
