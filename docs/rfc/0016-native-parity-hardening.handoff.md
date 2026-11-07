# RFC-0016 native-parity hardening — handoff

- **Stage:** design done: `/architect` rounds 1 and 2 on 2026-11-06, on branch
  `rfc-0016-design` (base `main` 83c1d304). Implementation of
  Wave 1 (0.9.2) is next (decision D-0016-5).
- **Resume:** `/tdd rfc-0016 wave 1` (K9a first).
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
| F-0003 | 2026-11-06 | soundness | same (expected) | research lens D | `--panics:on` Defect path (W-03) | V | W1-c | open |
| F-0004 | 2026-11-06 | soundness | same (expected) | research lens A | float32/float64 conversion (W-04) | P | W1-e | open |
| F-0005 | 2026-11-06 | soundness | same (expected) | research lens C | `low(int) mod -1`, literal divisor (W-05) | P | W1-d | open |
| F-0006 | 2026-11-06 | soundness | same (expected) | research lens B | unsigned div/mod by zero (W-06) | P | W1-d | open |
| F-0007 | 2026-11-06 | soundness | same (expected) | research lens D | checks-off signed wrap (W-07) | P | W1-d | open |

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
