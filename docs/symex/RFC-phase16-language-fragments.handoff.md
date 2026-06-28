# Phase 16 (language fragments part 2) — handoff

- **Stage:** 3 implementation IN PROGRESS (rfc-flow grind via `/loop … /tdd`)
- **Done so far:**
  - ✅ **A5** (commit `5288e99`, walker **v18**) — classify/copySign modeled, nextafter is a documented Z3 bound; both backends green, canaries clean (F6 expectations flipped sxUnknown→sxSat).
  - ✅ **D0-ADR** — ADR-0011 STATUS → **ACCEPTED**. F1=unified, F2=`set[ArithCheck]` default **all-on**, F3=add both dk* (append at enum end), F4=D1a/b first then R16-2..5, F6=skip overflow fork on svInt. Open-questions resolved (two-axis policy-first ordering; feConvDomainExcluded retire+freeze). Doc-only; no version bump (verdicts unchanged until R16-1).
- ✅ **D1a + D1b** (commit `f3a33e6`, walker **v19**) — defect forks now unconditional, route via `routeRaise`; verdict-API break sxSat→sxRaised for tIndexError/tFieldDefect/tAssertionViolation/tNilAccess; `assertCoveredBy` replays `raisedWitness`; +CR-22 DSL nil-classifier fix. 174/174 both backends. 33 existing tests migrated.
- ✅ **D1c — short-circuit modeling** (commit `268dfb0`, walker **v20**; Corey-approved out-of-band slice). D1a unmasked a pre-existing soundness gap: the parser A-normalized index/variant-field/deref sub-exprs into a SHARED preamble, so an `and`/`or` RHS ran unconditionally → `if o.inner.k and o.inner.x > 0` falsely reported `sxRaised{FieldDefect}` (Invariant-3 violation). **Fix (parser-only, walker untouched):** `dsl_parser.nim` `nnkInfix` arm now parses the RHS into a separate preamble; when non-empty, emits `isLet(__sc, lhs)` + a guarded `isIf` (`and`: `if __sc`, `or`: `if not __sc`) whose body runs the RHS preamble + `__sc = rhs`, value = `mkVar(__sc)`. Empty-RHS-preamble fast path = `mkBinop` unchanged (zero new paths for pure bools); `bXor` never short-circuits. New `tsymex_phase16_D1c_shortcircuit.nim` 7/7 both backends; real defects still surface (no false negatives); hang canary clean. The 5 D1a flat-`and` test workarounds were RESTORED as regression coverage (kept nested only where the guard protects a genuinely-reachable real defect). _Independently re-verified by control loop: guarded→sxSat, unguarded→sxRaised, parity PASS._
- ✅ **R16-1 — arith-defect enum + ArithCheck policy foundation** (commit `ac40f25`, walker **v21**). Appended `dkOverflowDefect`(7)/`dkDivByZeroDefect`(8) at DefectKind END (CR-16); new `ArithCheck = {acOverflow, acDivByZero, acRange}` enum; `arithChecks: set[ArithCheck]` field on SymexSettings **default all-on**, threaded like `defectExclusions` at 5 sites (field decl, `defaultSymexSettings`, `+` merge, `validateSymexSettings` w/ 2 bidirectional waste/empty warnings, canonicalize `;ac=` cache-key render); `typeIdToDefectKind` maps the two new strings. **NO forks yet, NO verdict change.** 21/21 new tests + CR2(7/7, pin→"21")/fielddefect/D1c/F5hang regressions green both backends. ⚠ CR2_cachekey pin had been left at "19" by D1c — R16-1 corrected to "21"; see [[symex-version-bump-cr2]].
- **Resume (Stage 3):** next is **R16-2** (float→int **RangeDefect**, replaces CR-3). ADR-0011 cycle row R16-2 (line ~129): **DUAL-DRAIN, not substitution** — keep `drainConvFloatToIntBounds`→`p.pc` (sound BV truncation on the normal path) AND add a new `drainConvFloatToIntRaises(p,w): seq[Path]` (parallel to `drainParseIntRaises`, returns seq[Path] so it canNOT live in the single-Path `drainPendingLowerEffects`; call at walk-arm level) forking `not(domainCond)`→`routeRaise("RangeDefect")`, gated on `acRange`. **Hint teardown** (5 sites/3 files): remove domHint32/domHint64 emission + `syncConvFloatToIntDomainHint` + `convFloatToIntDomainHints` threadvar/WalkCtx-field/reset/drain. `feConvDomainExcluded` (types.nim:711) is a CLOSED-enum member → **freeze-annotate `## retired R16-2 — do not reuse ordinal`, do NOT delete** (CR-16). Bumps walker v21→v22 (verdict-changing) → **update+run CR2_cachekey pin** [[symex-version-bump-cr2]]. Perturbs CR3_CR4_CR6_float, F5hang_derefwrite, rereview_drains, cr9_lowerInExpr (retire 6 hint asserts across 4 files). F5-hang canary mandatory. → then R16-3 (div/mod-by-zero) → R16-4 (int overflow, skip svInt) → R16-5 (deferred).
  - ⚠ R16-3/R16-4 add MORE defect forks — D1c now guards them correctly under short-circuit (`if x != 0 and a div x …`), so build on it.
  - grind cmd: `/loop implement the next unimplemented RFC slice with /tdd …`
- **Commit hygiene:** NO Co-Authored-By trailer (Corey strips it via global hook — see [[no-claude-trailer]]).
- RFC: `docs/symex/RFC-phase16-language-fragments.md` · first-slice ADR: `ADR-0011-rangedefect-overflow.md`
- **Before A7 is scheduled:** resolve the open fork below (Path B vs Path A).

## Slices (all stub / unimplemented — Stage 3 not started)
- [ ] A0 — CR-9 trailing threadvars → WalkCtx (infra)
- [x] D — defect-flow unification: ✅ D0-ADR, ✅ D1a, ✅ D1b, ✅ D1c (short-circuit) — prerequisite COMPLETE
- [~] R16 — arithmetic defects: ✅ R16-1 (enum+policy foundation, v21); next R16-2 → R16-3 → R16-4 → R16-5(deferred)
- [x] A5 — float classify() + copySign (DONE, walker v18; nextafter = documented Z3 bound)
- [ ] A2 — ref-of-variant pointee (needs own design ADR)
- [ ] A3 — closure iterators
- [ ] A6 — symbolic-length filter/map (engine-side)
- [ ] A7 — Unicode rune witnesses (UTF-8 layer) · A8 — radix · A9 — ASCII case-fold/reverse/bounded-sort
- [ ] INV — wire never-emitted se* kinds + add geVtableDispatch
- [ ] B1 — regex find over patterns (engine-side or upstream indexof_re wrapper)

## Open forks (awaiting Corey)
- **A7 spec-assumption escalation (the one genuine fork):** full-Unicode **Path A**
  (lift the ≤0xFF free-string constraint) reopens the **Corey-locked byte-faithful
  ADR-0006** and breaks all 14 S-cluster tests. RFC mandates **Path B** (additive
  parallel `Rune`/`runes(s)` path; byte model untouched). → _Recommend: confirm Path B
  is the scope; Path A stays out unless you explicitly unlock ADR-0006._
- **F1/F2/F3/F6** (defect mechanism / overflow policy / enum additions / svInt rule)
  — leans recorded in ADR-0011; **formalized at D0-ADR**, not blocking before then.

## Key decisions (this session)
- Track B **dissolved** by a Z3/nim-z3 capability investigation → engine-side A7/A8/A9; only genuine-cannot = full-Unicode case-fold + symbolic-length sort (documented bounds). No appetite/fork remains.
- Defect-flow unification **elevated** to prerequisite Cluster D; D1 retrofit **front-loaded** (pairs with R16-2); ADR-0011 rescoped to "defect-flow architecture."
- A5 = lowest-risk opener (pure lowerMathCall extension, zero plumbing/test-breakage).
- ADR-0011 F5 resolved (BV overflow predicates present in nim-z3 bitvec.nim).
- **Round 2:** D1 split into **D1a** (engine route-swap + gate removal + verdict-API break) + **D1b** (`assertCoveredBy` raisedWitness replay); **R16-1 ≺ R16-2** is a hard edge (acRange gate); +NilAccessDefect as a 4th retrofit site; A7 **Path B** mandated; **F6** (svInt short-circuit) added as a real fork; B1 → `post-16`; GC-2 split (DefectKind=cache / SymexErrorKind=external).

## Review ledger (stage 4 — not started)
| id | sev | finding | status | proof/reason |
|----|-----|---------|--------|--------------|
| —  | —   | —       | —      | —            |
