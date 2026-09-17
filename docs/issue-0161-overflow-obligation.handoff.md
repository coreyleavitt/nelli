# Issue #161 — promotion must keep the OverflowDefect obligation live

Issue-scoped handoff (not an RFC; no `docs/rfc/NNNN` number). Newest entries
at the BOTTOM.

- **Branch:** `rfc-161-overflow-obligation` (named `rfc-*` deliberately — the
  three Windows legs trigger on `[main, 'rfc-*']`, and this is a walker
  semantics change that `symex-mingw` must verify).
- **Base:** `a1ebeb1`.
- **Issue:** #161. Sibling #162 (int32 range subtypes lose their base width)
  is independent and NOT addressed here.

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

## Slice status

| slice | what | state |
|---|---|---|
| 1 | **Floor** — stamp `ziWidth`/`ziSigned` on `promoteSound` params | **DONE** (`3ce1dfd`, walker v126) |
| 2 | **Prune** — wire `tryEvalInterval` as fork-*pruning* | **NEXT** |
| 3 | Unchecked-semantics knob (`-d:danger` / `--overflowChecks:off`) | todo — Corey confirmed it lands in #161 |
| 4 | Remaining behaviours (add/sub/underflow, chained propagation, comparison-only non-regression, `isExact` unchanged) | todo |
| 5 | #162 int32 case pinned as a still-red trip-wire | todo |

## Slice 1 — landed

`runtime.nim` promoteSound allocation now stamps the static Nim width, so
`lowerArith` keeps pushing `overflowCondInt`. `promoteLoose` (isLoose) and
`isIntOffset`-only promotions stay **unstamped** by design.

Reverses the R3 (S2) scope note *only for promoteSound*. That note's 15+minute
blowup was measured on `isIntOffset` params, which promote unconditionally
with **no proven range** — every fork looks satisfiable so Z3 explores all of
them. A `promoteSound` param puts `[rangeLo, rangeHi]` in `initialPC`, so its
forks are overwhelmingly UNSAT at birth. The note was right about its own case
and does not generalise.

**Gates run (all on `c` backend, in-container):**

- `tsymex_161_overflow_obligation` 2/2, `tsymex_phase15_CR2_cachekey` green.
- Perf, base → fixed: `r6_b4_readcstring` 18→16s, `r6_b5_chained` 20→19s,
  `r6_b6_optionregion` 19→21s, `phase2_abstraction` 16→19s,
  `phase2_overflow` 17→17s. **No blowup.**
- Correctness probe (`scratchpad/bench/probe_ban_restores_fork.nim`):
  `mul64` → `sxRaised`/2 promoted; `addSafe` → `sxUnsat`/2 promoted (no
  over-firing); `isExact` unchanged.

**Known cost — this is slice 2's job.** Emitting forks on promoted values
costs part of the abstraction speedup on arithmetic-heavy code
(`scratchpad/bench/bench_abstraction.nim`): constrained-chain 1.6–2.2× →
**0.99×**, comparison-ladder ~2.4× → **1.43×**, bounded-loop **3.3×**
(unchanged), bit-twiddling ~1× / 0 promoted (unchanged, correct).

## Slice 2 — the design question to settle first

`tryEvalInterval` takes `(IRExpr, RangeMap)`, but `lowerArith` sees `SymVal`s
*after* lowering and has no `IRExpr` in hand. Two options, **not yet decided**:

- **(a) IR pre-pass.** Mark each arithmetic node "overflow-proven" before
  lowering; `lower` passes the flag down. Surgical, but it is a second static
  pre-pass — the architecture this design criticised.
- **(b) Interval on `SymVal`.** Carry a lattice element alongside the existing
  `ziWidth`/`ziSigned` representation metadata; `arithInt` already propagates
  width and would propagate the interval with it. More principled, composes
  through lets/reassignment/calls, but touches `SymVal` broadly.

Lean: **(b)** — it is the same kind of metadata `SymVal` already carries, and
it is the thing that makes pruning compose. Confirm before building.

## Sweep baseline — NOT yet taken

A `-f tsymex` baseline was started and **discarded**: it was launched before
the `runtime.nim` edit but compiles per-test as it runs, so tests reached after
the edit built against modified source. Do not trust any sweep log written
this session. A clean baseline must be taken from `a1ebeb1` (worktree or
stash) before the pre-land sweep diff.

Operational note: that sweep's `xargs -P6` pool survived its parent, was
reparented to the Claude background daemon, and kept spawning containers after
the task reported "failed". Kill the pool PID directly, then the
`dt-bounded.sh` workers, then `podman rm -f` the `dtbound_*` containers —
and filter by `ancestor=localhost/nelli-dev:latest`, because `amoxtli-dev`
and `crisol-dev` containers from other jobs share the host.

## Out of scope, surfaced not buried

- **`isIntOffset` promotions keep the same class of hole** (unconditional
  promotion, no range proof, `ziWidth: 0`, so no fork). Different promotion
  route from #161's repro; the R3 perf blowup is real for it. Recommend its
  own issue.
- **#162** — `range[0'i32..100000'i32]` loses its 32-bit base type; both
  `isExact` and `isOptimised` answer `sxUnsat`. Slice 1 does not fix it
  (params stay `svInt` stamped at the *wrong* width). Slice 5 pins it red.
- **Unrelated, found while benchmarking:** `bytesMode` has branches only in
  `drawBoolean` and `drawInteger`. `drawFloat`, `drawBytes` and `drawString`
  have none, so a float/bytes/string strategy fuzzed through the documented
  libFuzzer/AFL door (`fuzzOnce`) ignores the buffer entirely — 256 distinct
  first bytes produce 1 distinct float. Needs its own issue.
- **`symexFind` cannot walk a `{.cover.}`'d proc** — returns `sxUnknown` with
  an unclassified `weInternalWalkerFault`. `concolicFlip` can (G3fix is
  mode-gated to `wmFollowConcrete`). Needs its own issue.

## Resume command

```
git checkout rfc-161-overflow-obligation     # at 3ce1dfd
# settle slice 2 option (a) vs (b), then RED on the prune
scripts/dt-bounded.sh c tests/tsymex_161_overflow_obligation.nim 600
scripts/dt-bounded.sh c scratchpad/bench/bench_abstraction.nim 780   # the perf gate
```
