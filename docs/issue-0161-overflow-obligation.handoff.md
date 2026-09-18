# Issue #161 — promotion must keep the OverflowDefect obligation live

Issue-scoped handoff (not an RFC; no `docs/rfc/NNNN` number). Newest entries
at the BOTTOM.

- **Branch:** `rfc-161-overflow-obligation` (named `rfc-*` deliberately — the
  three Windows legs trigger on `[main, 'rfc-*']`, and this is a walker
  semantics change that `symex-mingw` must verify).
- **Base:** `a1ebeb1`.
- **Issue:** #161. Sibling #162 (int32 range subtypes lose their base width)
  is NOT fixed here — slice 5 pins it as a known-wrong trip-wire.

## Design decision (accepted by Corey, 2026-09-17)

**ADR-0001 amendment — obligation-as-floor.** ADR-0001 says "bit-vectors as
the floor, promote on proof". The amendment: the floor is the proof
*obligation*, not the *representation*. A value may be Int-sorted only if
every operation on it is proven non-overflowing; every promotion must either

- **discharge** the obligation statically (interval proof), or
- **keep it live** dynamically (carry the width so `overflowCondInt` fires).

Either is sound. The forbidden third state — obligation neither discharged
nor kept — was the bug.

Consequence for the architecture: the **dynamic fork is the soundness floor**
and the **static interval analysis is an optimisation on top**. Today's code
had it inverted (static analysis as the sole proof, no backstop), which is why
any gap in `tryEvalInterval`'s coverage was a potential false `sxUnsat`.

Rejected: the issue's option 1 (widen the ban scan). It demotes the param to
BV *everywhere*, losing Int-speed on every other operation it touches, and
demotes *into* the more expensive encoding (`overflowCond`'s BV predicates vs
`overflowCondInt`'s Int range check). Measured: under the chosen design the
#161 repro answers `sxRaised` **while staying promoted (2 abstractions)**; the
ban would have left 0.

**Where the ban IS correct: unchecked arithmetic (slice 3).** With
`acOverflow` absent from `arithChecks`, overflow is not a defect, it WRAPS —
so there is no raise fork to keep live and no dynamic backstop exists. There
promotion must be proven statically or declined, and declining means BV,
which is the correct wrapping model. The two halves of the amendment need
opposite mechanisms, and the reason is the amendment itself.

## Slice status — ALL FIVE LANDED

| slice | what | state |
|---|---|---|
| 1 | **Floor** — stamp `ziWidth`/`ziSigned` on `promoteSound` params | **DONE** `3ce1dfd`, walker v126 |
| 2 | **Prune** — static discharge via intervals on `SymVal.ziIvl` | **DONE** `fed5396`, walker v127 |
| 3 | **Unchecked semantics** — `arithChecks` without `acOverflow` now wraps | **DONE** `744012c`, walker v128 |
| 4 | Remaining behaviours (add/sub, chained propagation, over-ban guard, unsigned, `isExact`) | **DONE** `fc5cfd9`, tests only |
| 5 | #162 int32 case pinned as a still-red trip-wire | **DONE** `fc5cfd9` |

`tests/tsymex_161_overflow_obligation.nim` — **14/14**, registered in
`nelli.nimble` and named `tsymex_*` so `derive-ci-suites.ps1` pulls it into
the symex-mingw corpus.

## Slice 1 — the floor

`runtime.nim`'s promoteSound allocation stamps the static Nim width, so
`lowerArith` keeps pushing `overflowCondInt`. `promoteLoose` (isLoose) and
`isIntOffset`-only promotions stay **unstamped** by design.

Reverses the R3 (S2) scope note *only for promoteSound*. That note's 15+minute
blowup was measured on `isIntOffset` params, which promote unconditionally
with **no proven range** — every fork looks satisfiable so Z3 explores all of
them. A `promoteSound` param puts `[rangeLo, rangeHi]` in `initialPC`, so its
forks are overwhelmingly UNSAT at birth. The note was right about its own case
and does not generalise.

## Slice 2 — the prune

`SymVal.ziIvl: Option[Interval]` carries a sound over-approximation of an Int
term's values. Seeded from a `promoteSound` param's declared range and from
integer literals (`coerceIntLit`); propagated by `arithInt`. `lowerArith`
calls `tryDischargeOverflowInt`, which composes the operand intervals and
tests the result against the **same `intBounds(width)`** `overflowCondInt`
compares to — so "discharged" means exactly "the cond would have been UNSAT".

**The direction of failure is the design.** `none` is `Option`'s zero value,
so every `SymVal` construction that does not think about intervals gets ⊤ and
keeps the obligation live. Forgetting to propagate costs a redundant fork; it
can never delete a defect path. Soundness stays entirely in slice 1's
`ziWidth`.

**The abstract domain had to be made total first.** Its bounds live in
`int64`, so the analysis's own arithmetic can overflow — `[0..4e9] * [0..4e9]`
needs 1.6e19. Unguarded, that raised `OverflowDefect` *inside the walker*
under checked builds and would have silently WRAPPED under `-d:danger`, where
a wrapped bound looks small and would "prove" an unsafe site safe.
`add`/`sub`/`mul`/`neg` now return `Option[Interval]`.

**`SymexResult.obligations`** reports every obligation and its disposition
(`odDischargedStatic` / `odLive`, with the proven bound). Same argument that
put `abstractions` there: a verifier that silently decides which obligations
to prove itself is not one you can check. Empty when `fromCache`.

Measured (`scratchpad/bench/bench_abstraction.nim`, median of 5):

| | a1ebeb1 | after slice 1 | after slice 2 |
|---|---|---|---|
| bounded loop | 3.30× | 3.30× | **4.22×** |
| arithmetic chain | 1.6–2.2× | 0.99× | **1.89×** |
| comparison ladder | ~2.4× | 1.43× | **1.93×** |
| bit-twiddling | 0.85× | — | 0.96× (BV both, 0 promoted) |

`scratchpad/bench/probe_obligations.nim` confirms the mechanism rather than
inferring it from timings: constrainedChain 2/2 discharged, ladder 3/3
discharged, mul64 1 live, boundedAccum 5 live.

## Slice 3 — unchecked arithmetic

`ArithCheck`'s doc already said "Empty set = release-like (all arithmetic is
unchecked / wrapping)", and dropping `acOverflow` did suppress the raise fork.
But `isOptimised` kept modelling promoted params as unbounded `Z3Int`s, which
do not wrap. Measured before the fix, `if a*b < 0` over `range[0'i64..4e9]`:

```
unchecked, isExact (ORACLE)   sxSat     <- correct; BV wraps by construction
unchecked, isOptimised        sxUnsat   <- false negative
```

Two integer modes contradicting each other is what ADR-0001 exists to forbid,
so this was a soundness bug in its own right — **independent of slices 1–2 and
older than them**.

Fix: `collectBan` grows a `BanPolicy` with a second rule — under unchecked
semantics, any `add`/`sub`/`mul`/`neg` not provably inside the type's window
bans promotion. This gives Phase 2's `tryEvalInterval` its **first caller in
`src/`**.

**The ban is whole-program on purpose.** A partial ban would leave one param
BV-sorted and another Int-sorted, and `reconcileInt` bridges those by
converting the BV side UP to an unbounded Int — reintroducing exactly the
non-wrapping arithmetic the ban exists to prevent. Under unchecked semantics
the representations cannot be mixed safely, so it is all or nothing.

**Known precision cost, recorded in the code:** an unprovable node anywhere
disables promotion everywhere for that run, and locals carry no interval in
the scan, so `let s = a + b` makes every later use of `s` unprovable. On
unchecked builds `isOptimised` therefore degrades towards `isExact`. Two ways
to recover it, neither attempted: per-param bans over a provenance dataflow,
or encoding the wrap explicitly as a Z3 Int `mod 2^W` constraint and keeping
the promotion (precise, but mod-by-2^64 is a real performance risk and this
codebase has CR-17 non-termination history with mixed-theory terms).

## Slices 4–5 — pins, no implementation

Every test passed on first run against slices 1–3. They are regression pins,
and each one is a claim the design makes that nothing else checks — in
particular "the obligation survives a safe intermediate local", which is the
only thing that fails if `arithInt`'s width propagation is deleted.

Slice 5 asserts the **wrong** answer for `range[0'i32..100_000'i32]` on
purpose (`sxUnsat` where `sxRaised` is correct) so it flips red the moment
#162 lands. When it fails: delete it and assert `sxRaised`.

## Walker versions

125 → **126** (slice 1) → **127** (slice 2) → **128** (slice 3). The
`CR2_cachekey` pin tracks each bump; `tsymex_161_overflow_obligation` pins the
floor at `>= 126`.

## Gates run (all `c` backend, in-container)

- `tsymex_161_overflow_obligation` 14/14
- `tsymex_phase15_CR2_cachekey` 7/7, `tsymex_phase1_arith` 7/7,
  `tsymex_phase2_abstraction` 5/5, `tsymex_phase2_fallback` 2/2,
  `tsymex_phase2_overflow` 4/4, `tsymex_rectify_abstraction` 2/2
- No blowup on the r6 perf corpus: `b4_readcstring` 18s, `b5_chained` 17s,
  `b6_optionregion` 19s (baseline 18/20/19s)
- Full `-f tsymex` sweep diff vs a clean `a1ebeb1` worktree — see below

## Sweep baseline — how to take it correctly

A sweep compiles per-test **as it runs**, so a baseline started before an edit
and finished after it is contaminated (one was discarded this way). Take it
from a pinned worktree instead:

```
git worktree add <tmp>/base161 a1ebeb1     # pinned sha, not a branch
```

and run the two sweeps **strictly sequentially** — concurrent `dt-bounded`
runs of the same test file clobber one shared binary, which reads as a flaky
product bug. `<tmp>/gate161.sh` does baseline → current → diff in one pass.

Operational note: a prior sweep's `xargs -P6` pool survived its parent, was
reparented to the background daemon, and kept spawning containers after the
task reported "failed". Kill the pool PID directly, then the `dt-bounded.sh`
workers, then `podman rm -f` the `dtbound_*` containers — and filter by
`ancestor=localhost/nelli-dev:latest`, because `amoxtli-dev` and `crisol-dev`
containers from other jobs share the host. `pgrep -cf 'xargs -P6'` matches its
own argv; use a bracket pattern (`'xargs -P[6]'`).

## Follow-ups — surfaced, NOT filed (need Corey's go to open issues)

1. **`isIntOffset` promotions keep the same class of hole.** Unconditional
   promotion, no range proof, `ziWidth: 0`, so no fork. Different promotion
   route from #161's repro; the R3 perf blowup is real for it, which is why it
   was left alone here.
2. **Intervals on BV-sorted values.** `ziIvl` exists only on `svInt`, so a
   literal-initialised BV local (`var acc = 0`) has no bound and every
   arithmetic site on it stays live — `boundedAccum` pays 5 forks it could
   prove away. Pure optimisation, no soundness content.
3. **Precision of the unchecked ban** (slice 3's recorded cost, above).
4. **`bytesMode` has branches only in `drawBoolean`/`drawInteger`.**
   `drawFloat`, `drawBytes` and `drawString` have none, so a float/bytes/
   string strategy fuzzed through the documented libFuzzer/AFL door
   (`fuzzOnce`) ignores the buffer entirely — 256 distinct first bytes produce
   1 distinct float.
5. **`symexFind` cannot walk a `{.cover.}`'d proc** — returns `sxUnknown` with
   an unclassified `weInternalWalkerFault`. `concolicFlip` can (G3fix is
   mode-gated to `wmFollowConcrete`).

## Resume command

```
git checkout rfc-161-overflow-obligation     # at fc5cfd9
scripts/dt-bounded.sh c tests/tsymex_161_overflow_obligation.nim 700
scripts/dt-bounded.sh c scratchpad/bench/bench_abstraction.nim 840     # perf
scripts/dt-bounded.sh c scratchpad/bench/probe_obligations.nim 600     # audit trail
scripts/dt-bounded.sh c scratchpad/bench/probe_wrap.nim 600            # mode agreement
```

Landing: fast-forward to `main`, then tag (this repo never opens PRs).
