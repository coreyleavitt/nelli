# Control-loop verification of lens findings

## F-01 (cpp gate log at 1a02b496 is a copy of the c log) -- REFUTED (ran)
- The fourth column of a sweep log is the per-test WARNING count (sweep.sh:245 `echo "$rc $b $f $warn_n"`), not seconds.
  Warnings come from the shared front end, so identical counts across c and cpp are expected.
- The cpp log is a genuine eos run: different row order (tbias vs tautolabels at line 3), its own
  `~/nelli/cpp-1a02b496.log.summary` on eos: backend=cpp pass=989 fail=0 total=989.
- The local copy in g11gate lacks .summary only because just the .log was copied back.
- Kept from F-01: copy the .summary sidecar with any certifying log (provenance hygiene, Low).

## E spot-checks (read)
- SND-02 closed: tests/tsymex_rfc0005_s8cb_tostr.nim:37-41 runs `$n` natively -- holds (see read below).
- SND-12: no test contains `gc_shared` (grep tests/ empty) -- holds.
- ceUnsupportedCapture has no producer in src (only its classOf arm, types.nim:3420) -- holds.

## D-01 (--panics:on: Defects modelled as catchable) -- CONFIRMED (ran, control loop re-run on eos wt-rsD, 2026-11-06)
- pDivCaught/label: sxSat pathTaint={} runTaint={} replay=rsNotNeeded witness (5,)
- pIdxCaught/label, pFinally/label: same clean sxSat; pRaised: clean sxRaised.
- Native pDivCaught(5): `Error: unhandled exception: division by zero [DivByZeroDefect]`, process exits; handler never runs.
- Severity: false trusted sxSat under a build flag the walker does not consult. Same severity as 0.9.x (not a regression).

## A-01 (`except T as e` in a SUT) -- CONFIRMED (ran, control loop re-run on eos wt-rsA, 2026-11-06)
- as/caught_as: sxUnsat, pathTaint={} runTaint={} errs=[]  -- native 3=>after+caught_as  (FALSE UNSAT, clean)
- as/raised: sxRaised clean -- native: the handler catches it, nothing escapes (FALSE RAISED)
- control `except ValueError:` (no `as`): caught sxSat (3,), raised sxUnsat -- correct.
- Severity: false clean sxUnsat on everyday syntax. Highest-priority row in the merged list.

## B-05 (`{.cursor.}` local pragma stripped) -- CONFIRMED (ran, control loop re-run on eos wt-rsB c/orc)
- pg_cvar_shared: walker sxUnsat, native true, errs [] (FALSE UNSAT clean); pg_cvar_copy: sxSat, native false (FALSE SAT clean); `let {.cursor.}` twin identical.
## B-04 (let over variant holding a seq) -- agrees with native on c/orc (re-run p_varcur: all "ok"); divergence is refc-only, and refc cannot build symex (B-14/D-04). Keep as build-sensitive, not a c/orc soundness bug.
