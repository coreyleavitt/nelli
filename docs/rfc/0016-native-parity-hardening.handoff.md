# RFC-0016 native-parity hardening — handoff

- **Stage:** design done: `/architect` rounds 1-3 on 2026-11-06, on branch
  `rfc-0016-design` (base `main` 83c1d304). Implementation of
  Wave 1 (0.9.2) is next (decision D-0016-5).
- **Resume:** `/tdd rfc-0016 wave 1` (K9a first, then W1-c3; order in §11).
- **Research:** `docs/rfc/0016-research/` (six lens reports, the merged list
  W-01..W-69, the magic table, the test classification). Snapshot 83c1d304,
  walker 272.
- **Open forks:** none.

## Findings ledger (§3.2), newest at the bottom

Severity against `main` not yet measured for any row; W1-z adds the
three-way rows. Evidence V = coordinator re-ran walker and native on one
build; P = the lens did.

| F | date | class | vs release | source | shape | evidence | fix | state |
|---|---|---|---|---|---|---|---|---|
| F-0001 | 2026-11-06 | soundness | same (expected) | research lens A | `except T as e:` (W-01) | V | W1-a | open |
| F-0002 | 2026-11-06 | soundness | same (expected) | research lens B | local `{.cursor.}` (W-02) | V | W1-b | open |
| F-0003 | 2026-11-06 | soundness | same (expected) | research lens D | `--panics:on` Defect path (W-03) | V | W1-c2 | open |
| F-0004 | 2026-11-06 | soundness | same (expected) | research lens A | float32/float64 conversion (W-04) | P | W1-e | open |
| F-0005 | 2026-11-06 | soundness | same (expected) | research lens C | `low(int) mod -1`, literal divisor (W-05) | P | W1-d1 | open |
| F-0006 | 2026-11-06 | soundness | same (expected) | research lens B | unsigned div/mod by zero (W-06) | P | W1-d1 | open |
| F-0007 | 2026-11-06 | soundness | same (expected) | research lens D | checks-off signed wrap (W-07) | P | W1-d2 | open |

## Round 1 ledger (2026-11-06)

Five lenses (liveness, depth, design, breadth, feasibility). Every point was
resolved by recommendation; none reached Corey.

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | liveness | K1 "reporting first" is green-but-inert | ratchet allowlist failing from the first commit, planted RED per leg (§8.2) |
| 2 | liveness | no Linux or cpp CI leg runs the test task | CI-A/CI-B precede K1a (§11 Wave 2) |
| 3 | liveness | K8 host (sls2) offline, no `schedule:` workflow | K8a skeleton in Wave 2 on a scheduled Linux job; §4.2 corrected |
| 4 | liveness | Wave 1 W-03 needs a profile producer | minimal `buildProfile` const in W1-c, constructor-only grep pin (§8.3) |
| 5 | liveness | F-NNNN ledger never created | this file, F-0001..F-0007 |
| 6 | liveness | exact cells pinned outside public entry points | K1 refuses them (§10) |
| 7 | depth | UB is not sequenced: trusting a prefix-defined witness is unsound | whole-run definedness check on the winning path (§9.1 item 3); model continuation chosen over UBSan replay at verdict time, which needs a sanitizer build of the consumer |
| 8 | depth | UB on the default build too; `arithTrapConds` is x86-only | default build is a row of `admitDefinedness`; trap model retired (§9) |
| 9 | depth | W-13 noinit is not UB-as-halt | replay-side unconfirmable mark, MSan/valgrind pin (§9 "Not in K10") |
| 10 | depth | cell granularity ill-defined; K1 overclaims | cell = (dispatch site, arm key); single-site only; pairwise figure in §12 |
| 11 | depth | grep gates can be dodged | K2 census parses the AST; K7 by type (`Survivors`) |
| 12 | depth | `sxUndefined` breaks every exhaustive status case | no new status; `stkUndefined` target + `ubUndefinedBehaviour` halt (design lens's proposal) |
| 13 | depth | K5 should read effective C flags; compiler is a pin axis | §8.3 |
| 14 | design | hand-annotated TSV is a second source of truth | ledger generated from admission tables (§8.2) |
| 15 | design | K2-K6 are one mechanism | `smt/admission.nim`, `Admission[K]`, `feUnadmitted` (§8.1) |
| 16 | design | BuildProfile scattered | one const, three derivations (§8.3) |
| 17 | design | K7 grep acceptable | overruled by #11 |
| 18 | breadth | oracle not in the universe | §10: boundary values, witness-directed, sampled state, sanitized native rows, render round-trip, VM column |
| 19 | breadth | missing axes | call-site × callee shape, exceptions × memory (§8.2) |
| 20 | breadth | other NimNode parsers outside dsl_parser | K2 census covers all of `src/nelli` |
| 21 | breadth | MSVC/mingw have no UBSan; arm64 differs | declared Windows cells; arm64/macOS compile-only legs (§8.3, §9.1) |
| 22 | breadth | alternatives unweighed | §13 (post-transf AST, CBMC/KLEE recorded) |
| 23 | breadth | K8 across every build ≈100 h/day | one build row per night rotation (§11) |
| 24 | feasibility | seven parallel bumps | Wave 1 integrated as one bump (W1-z) |
| 25 | feasibility | W-05/06/07 are K10 (breaking) yet listed for 0.9.2 | 0.9.2 ships the fail-closed decline; K10 restores precision in 0.10.0 (§9 last paragraph) |
| 26 | feasibility | `staticRead` of ~850 tests too costly | pin-file checks at run time (§8.2) |
| 27 | feasibility | `holdsSharedMemory` not found | refuted: `dsl_parser.nim:16561` |
| 28 | feasibility | K4c/K6/K10b flip verdicts broadly | marked *round*, gated by a pinned sweep baseline (§11) |
| 29 | feasibility | `bindsViewWhole` is IR-level | stays separate from `mayWrite` (§8.1) |
| 30 | feasibility | `Admission[K]` designed against one consumer | ADM-1 spike moves `varParamMagics` and `verifiedLibs` onto it first |

**For round 2:** apply E-reconcile's corrections to §5.1-§5.8 (closures,
duplicates, stale evidence, reclassifications); check §8-§13 against the code
once more (the admission table list, the 20 degrade sites, the census reach);
stale CLAUDE.md lines (active RFC, "not green on a good day") are a
repo-hygiene edit outside this RFC.

## Round 2 ledger (2026-11-06)

Five Fable lenses on `ff843ccc`; a sonnet agent applied the breadth lens's
row-by-row §5 reconciliation. Every point resolved by recommendation; none
reached Corey.

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | depth | shifts are masked by Nim's codegen (`ccgexprs.nim:665-667`), not UB | §9 corrected; shift decline dropped from W1-d; `shiftCountBV` is a defined row |
| 2 | depth | a UB halt taints runs whose UB side is infeasible | halt only if `pc ∧ cond` sat, decided once per path at exit (§9.1 item 2) |
| 3 | depth | whole-run check has no lattice home; replay could override it | `Soundness.witnessUndefined`, `trustedSat` respects it (§9.1 item 4); shared with noinit |
| 4 | depth | continuation is not a concrete walk; no failure rule | reach an exit with every predicate unsat, any other ending counts as undefined; static IR scan gate |
| 5 | depth, design | `SymexTargetKind` cases break; UB witness has no payload home | migration note; `undefined: seq[UbFinding[T]]` |
| 6 | depth | `feUnadmitted` as `dcOmitted` leaves the surviving path clean | `dcNoAnswer` until K7b drops the path |
| 7 | depth, design | a table does not prove a dispatch consults it | generated dispatch (`dispatchMagic`), arm ⇔ row checked at compile time; type-op verdict attached to the IR |
| 8 | depth | enum-keyed tables as `openArray` lookups | `array[K, …]`; `exact(...)` constructor rejects empty rows |
| 9 | depth | `querySetting` cannot see `--passC`, `-O`, compiler version | declared `-d:nelliFwrapv`; compiler family by `defined`, version a pin fact |
| 10 | depth | inlined stdlib body under a push | stdlib-body rows carry their check-option delta |
| 11 | depth | cell identity churns under refactor | cell = (axis, arm key); registered site strings |
| 12 | depth | §12 vacuous three ways | non-empty rows; precision non-regression item 5; pairwise floor from K8a's first run |
| 13 | depth | compile-only arm64/macOS cannot satisfy §12 | refused by name until run legs exist |
| 14 | depth | `skip()` not checkable against cells | `skip("cell:<axis>/<key>")` |
| 15 | design | `Admission[K]` is a row type, not a module | per-axis verbs, private rows, `Admit` answer, `Cell` enumerator (§8.1); old shape recorded in §13 |
| 16 | design | `proven(paths, pin)` reopens the hole | dropped; `halt` returns void; `walkUnsupported(): Survivors` |
| 17 | design | `$buildProfile` unstable; cc identity keyed | `cacheSegment` via `fieldPairs` + golden pins; semantic vs provenance fields |
| 18 | design | K9 a fourth lineage, arity-locked | grows `s8cu_helpers.nim`, on the splat, typed `Domain`, typed cell |
| 19 | design | float-to-int is a fresh symbol, not a halt | moves to the halt (K10a) |
| 20 | liveness | W1 pins written before K9 | K9a first in Wave 1 |
| 21 | liveness | K1 cannot read run-time `exhaustive`; shards split pins | pin records + post-shard K1 job |
| 22 | liveness | ratchet forbids introducing an axis | per-axis introduction rule |
| 23 | liveness | §5 rows and F ledger invisible to §12 | `Cell.items` + run-time id scan; §12 item 2 |
| 24 | liveness | fuzzer and scheduled legs have no failure consumer | issue per shape hash / per red run; §6 intake rule |
| 25 | liveness | MSVC shipping build has no row | `symex-msvc` in CI-B |
| 26 | liveness | refc refusal only in Wave 3; RFC-0014 pointer missing | refusal in W1-c1; SND-14 |
| 27 | liveness | older pending slices orphaned | "Carried slices" paragraph (§11) |
| 28 | liveness, feasibility | 0.9.2 gate undefined | sweeps c/cpp/4.13.4 at the W1-z sha vs a 0.9.1 baseline, Windows legs, wiring audit, code review |
| 29 | feasibility | W1-c and W1-d are rounds | split into c1/c2/c3 and d1/d2/d3; W-32 to Wave 4 |
| 30 | feasibility | W-06 has two sites; W-20 cite wrong; W-21 has a third site | corrected in the Wave-1 table |
| 31 | feasibility | second `nimPanics` read at `canonicalize.nim:6537` | rerouted in W1-c1 |
| 32 | feasibility | stale cache between W1 slices | bump in W1-a |
| 33 | feasibility | `verifiedLibs` needs a payload or absent-kind | ADM-1 decides; interface expected to change |
| 34 | feasibility | CI-A hides a known-red allowlist and provisioning | sized m-l with its parts listed |
| 35 | breadth | many W rows and §5 rows had no slice | §5.9; PRC-01/02 in Wave 3; K7 takes W-11/W-16; K5b takes W-58 |
| 36 | breadth | 0.10.0 migration note unnamed; second cold start | K10d writes it |
| 37 | breadth | §3.1 still said "tracked by rate" | restated; INF-03 rate report dropped |
| 38 | breadth | §5.1-§5.8 reconciliation | applied row by row (closes, merges, moves, SND-13/14, PRC-36/37, CRH-06..09) |

**Next:** `/tdd rfc-0016 wave 1`, starting with K9a. The RFC's `state` stays
`in-progress` (it was already past `ready` when RFC-0005's slices moved in).

## Round 3 ledger (2026-11-06)

Five Fable lenses on `9e275cf6`. Every point resolved by recommendation;
none reached Corey. Two looked like forks and are not: `-d:nelliFwrapv` can
produce `-fwrapv` itself (a global `{.passC.}`), which beats recording it as
an assumption; and 0.9.2's compile breaks follow 0.9.1's precedent of a
patch release whose migration note lists them (D-0016-5 stands).

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | depth | UB disjunction solved at the survivor's exit is trivially unsat (the survivor carries `¬cond`) | §9.1 item 2: the undefined side is its own terminal path at the op, decided at the raise boundary |
| 2 | depth | an infeasible UB side inside a callee replays clean from the call cache | unsat side is `logPrune`d; `pruneFactsHold` guards reuse |
| 3 | depth | the three drains are gated on `arithChecks` and return `@[p]` clean | the UB sink is ungated; gated drains taint `feCheckOption` until K10d |
| 4 | depth | the whole-run gate scanned one `IRProc` | transitive over walked callees, unwalked calls answer "may be undefined"; reuses `scanOpaqueDefects` |
| 5 | depth | continuation unspecified | `wmFollowConcrete` with the model as `concreteEq`; undecided counts as undefined |
| 6 | depth | an untrusted UB witness would be host-run by `symexForAll`/`assertCoveredBy` | `hostRunnable` requires `witnessUndefined == {}` |
| 7 | depth | optional sixth cache field ambiguous with `runDependence` | version 4: six fixed fields, optional seventh |
| 8 | depth | `{.noinit.}` read has no per-path carrier | Wave 1 is run-level (`feNoinitRead`); per-path in K10b |
| 9 | depth | checks-off model keyed to a setting the build never sees; W1-d2 closed only the push route | W1-c1 carries check options; W1-d2 covers the settings route, *round*, last before W1-z |
| 10 | depth | W1-c1's pin narrower than §8.3 | pin covers `defined(nimPanics)` and `compileOption(` |
| 11 | depth | panics: defect-ness after handler search; bare `except:` on unknown type; W1-c3 dead under panics | all three in W1-c2's scope; W1-c3 pins panics-off only |
| 12 | depth | "row with no arm" checkable only per site | rows carry consuming sites; dispatch checks its own site |
| 13 | depth | `-d:nelliFwrapv` trusted, not enforced | the define emits `{.passC: "-fwrapv".}`; refused under `vcc` |
| 14 | depth | §12 item 5 not measurable by `sweep-diff.sh` | restated as a per-axis exact-cell ratchet plus kept 0.9.1 baselines |
| 15 | design | `pin` and `items` on `Cell` put test/RFC metadata in `src/` and duplicate the pin record | removed; RFC rows carry `cell:`; pin records are the only link |
| 16 | design | `site: string` has the wrong cardinality | per-axis site enums, `dispatchMagic(site: static …)`, census checks each once |
| 17 | design | `Axis` mixed admission, coverage and pin families | error-kind coverage is a K1 derivation; call-shape and exn × memory are test-side families |
| 18 | design | `amOutOfScope` as a consumer branch, with no kind | `Admit[P]` is admitted/not with payload; `Intent` is ledger-only |
| 19 | design | `admission.nim` placement misdescribed | above `types.nim`, Z3-free |
| 20 | design | `Survivors` underspecified | `halted`/`surviving`/`admittedExact`; end state every arm (K7c) |
| 21 | design | `runtime.nim:19172` records and continues | fourth shape: keeps its path through `taintInPlace` |
| 22 | design | `cell: static Cell` circular | pins name a `CellKey`, checked at compile time |
| 23 | design | `witnessUndefined: bool` loses the kind; not projected | `set[UbKind]`; `FindingUndefined` projection; `UbKind` not "class" |
| 24 | design | `stkUndefined` breaks more in-tree `case`s than cited | `wireTarget`/`unwireTarget` and four `bindSym` splices listed |
| 25 | design | `BuildProfile` field list plus assertion | split by type: `BuildSemantics`/`BuildProvenance` |
| 26 | design | `Soundness.profile` naming | `buildSegment` |
| 27 | breadth | CRH-01 contradicts C-06 (the `sort` stop is gone) | sort half to W-36; CRH-01 keeps the two unprobed stops |
| 28 | breadth | PRC-29 shard claim false | sharded at the median; measure it |
| 29 | breadth | stale cites INT-23, INT-25, INT-27 | re-cited |
| 30 | breadth | CRH-04, INT-20 missing their "Includes" | added |
| 31 | breadth | §5.0 and F ledger pointed at pre-split W1-c/W1-d | re-pointed |
| 32 | breadth | INT-33 used as a row and a slice id | slice renamed K8-0 |
| 33 | breadth, liveness | §5.9 ids invisible to K1's regex; "open" undefined | one id per row (MOV-01, STY-01..09); closed-state vocabulary in §5.0 and §8.2 |
| 34 | breadth | `(F-06)` in CI-A was a lens id | `(W-59)` |
| 35 | breadth | W-19, W-57, W-59, W-60, W-64, W-69 unhomed | homed in §5.9's preamble and rows; CI-C/CI-D in CI-B |
| 36 | breadth | sanitizer job, 132 assertions, 481 suites had no ids | K8c, K9c, K9d |
| 37 | breadth | `symexFind` off the main thread uncovered | §8.2 threads bullet: a build-axis cell pinned by the three isolation suites |
| 38 | breadth | concolic flip solve outside K10 | K10a scope |
| 39 | breadth, liveness, depth | MSVC absent from the 0.9.2 gate | W1-m runs `tsymex_0016_*` under vcc on `fuzzer-msvc` |
| 40 | breadth | `docs/symex/README.md` decline catalogue stale; new declines name no kind | W1-z rewrites it; each W1 RED names its kind; messages point at the README |
| 41 | breadth | four unlisted 0.9.2 compile breaks; no release per wave | Compile breaks section in W1-z; §11 Releases paragraph |
| 42 | breadth | publication steps absent | nimble bump, dry run, tag, registry check in 0.9.2's gate; W3-z for 0.10.0 |
| 43 | feasibility | K9a cannot type `Cell` before ADM-1; splat private; no crash pin | `static string` key until K9b; export `emitWitnessSplat`; `pinCrash` |
| 44 | feasibility | W1-d2 is a *round*: settings route and 13 files | scope and files below; last before W1-z |
| 45 | feasibility | W1-d3 threading cost | run-level in Wave 1 (row 8) |
| 46 | feasibility | cites: W1-e `:4126`, W1-f `:12789` | dropped / replaced by the three `case` sites |
| 47 | feasibility | no versioned Z3 4.13.4 tooling | INF-05 |
| 48 | feasibility | K1a is m-l | split K1a-test / K1a-ci |
| 49 | feasibility | Wave 1 order | K9a, W1-c3, W1-a, W1-c1, W1-c2, W1-b/e/f/g, W1-d1, W1-d3, INF-05, W1-m, W1-d2, W1-z |
| 50 | liveness | pin records unread for a release | K9a ships `pinRecords` and round-trips it |
| 51 | liveness | universe test races its pins inside `sweep.sh` | runs last over the record directory; records keyed by (file, segment) |
| 52 | liveness | K1a's post-shard job named no workflow; misses legs | K1a-ci lists the three workflows, depends on CI-B |
| 53 | liveness | ratchet rules not test-checkable | test checks membership and staleness; growth is a review rule |
| 54 | liveness | W1-d3 RED could pass vacuously | forced zero slot: `rsConfirmed and not trusted()` |
| 55 | liveness | issue sinks end at a person; schedules run `main` and die after 60 days | `rfc-0016-intake` label; `workflow_dispatch` `ref`; heartbeat; W2-z/W3-z/W4-z check them |
| 56 | liveness | per-build golden needs a selector | `defined(cpp)`/`defined(vcc)`/Z3 version |
| 57 | liveness | W-63 JIT row not in CI-B | closed against the Windows legs (PRC-27); K2a rechecks |
| 58 | liveness | pre-W1-z chores not in W1-z | UPS filing and MOV-01 in W1-z's RED |
| 59 | liveness | no Wave 4 tracker row; stale W1/W2/W3/S8ci/rv0005-lows titles | `W4` added; titles corrected |
| 60 | liveness | §12 items without a producer | each item names its slice; pairwise floor file (K8b); `.summary` in CI-A |
| 61 | liveness | `symex-mingw.yaml:217-230` cite is the Z3 install step | the cite was in the replaced §8.2 text; dropped |
| 62 | liveness | INF-04 item 10 "do not file" contradicts D-0016-3 | superseded note in §11 carried slices |

**W1-d2's files** (verdict-bearing `acOverflow` opt-outs, 13 of the 19 that
name `arithChecks`): `tsymex_161_overflow_obligation`,
`tsymex_163rev_concolic_modes`, `tsymex_163rev_inert_exclusions`,
`tsymex_phase16_R16_4_overflow`, `tsymex_phase2_overflow`,
`tsymex_phase3_summarization`, `tsymex_rfc0005_s8aa_remainder`,
`s8ac_remainder`, `s8ad_remainder`, `s8aj_remainder_c`, `s8cu_cl_over`,
`s8cu_push`, `s8w_remainder_b`. The other six pin settings shape or mention
it in a comment.

**Next:** `/tdd rfc-0016 wave 1`, K9a first. The RFC is ready for `/tdd`;
`state` stays `in-progress`.
