# RFC-0016 native-parity hardening — handoff

- **Stage:** design. `/architect` round 1 done 2026-11-06 on branch
  `rfc-0016-design` (base `main` 83c1d304); round 2 next. Implementation of
  Wave 1 (0.9.2) waits for round 2 (decision D-0016-5).
- **Resume:** `/architect rfc-0016 round 2`, then `/tdd rfc-0016 wave 1`.
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
