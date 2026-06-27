# Phase 16 (language fragments part 2) — handoff

- **Stage:** 2 architect **COMPLETE (rounds 1 + 2 done)** → ready for Stage 3
- **Resume (Stage 3):** start with **A5** (low-risk opener) then **D0-ADR** (lock F1/F2/F3/F6, flip ADR-0011 → ACCEPTED) → D1a → D1b → R16-1 → R16-2 …
  - i.e. `/tdd` A5 first, or the rfc-flow grind: `/loop implement the next unimplemented RFC slice with /tdd …`
- RFC: `docs/symex/RFC-phase16-language-fragments.md` · first-slice ADR: `ADR-0011-rangedefect-overflow.md`
- **Before A7 is scheduled:** resolve the open fork below (Path B vs Path A).

## Slices (all stub / unimplemented — Stage 3 not started)
- [ ] A0 — CR-9 trailing threadvars → WalkCtx (infra)
- [ ] D — defect-flow unification (D0-ADR, D1 retrofit) ← prerequisite
- [ ] R16 — arithmetic defects (R16-1..R16-5; RD5 deferred-within)
- [ ] A5 — float classify() + math ops ← recommended low-risk opener
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
