## RFC-0005 0.9.1 (review R1-17). `ResourceBudget`, in a leaf module that
## imports nothing.
##
## Why a leaf. A verdict is relative to the budget it ran under: an `sxUnsat`
## is a proof only within these bounds. `SymexResult.bounds` carries them, and
## `SymexFinding` (`engine/types.nim`, the Z3-free and IR-free record the
## terminal report and its renderers read) must carry them too. So the type
## moved here from `smt/types.nim`, which imports and re-exports this module:
## every name is still reachable exactly where it was. Same reasoning as
## `smt/soundness.nim`.

type
  ResourceBudget* = object
    ## CR-9(b): caps on walker resource usage, consolidated out of
    ## SymexSettings. 0 = unlimited for every field EXCEPT `maxCallDepth`,
    ## `maxLoopUnwind`, and `seqInlineThreshold` (documented once here;
    ## per-field notes give the default value and what happens when the
    ## limit is reached).
    ##
    ## RFC-0010 B4: this promise was FALSE for four fields (`maxCallDepth`,
    ## `maxLoopUnwind`, `maxClosureInlineCount`, and the since-deleted
    ## `maxBytesEncodingLen`) as
    ## originally written — each enforcement site was missing the
    ## `cap > 0 and` guard `maxFrontierSize`/`maxSplitParts` already used, so
    ## an explicit 0 exhausted the budget on the very FIRST use instead of
    ## behaving as unlimited. Two of the four were fixed and genuinely
    ## honour 0 = unlimited: `maxClosureInlineCount` (`runtime.nim`'s
    ## `applyClosureGround`) and `maxBytesEncodingLen` (deleted with the
    ## `bytes(s)` model it capped, RFC-0005 S8c). A guard for `maxCallDepth` was added in the
    ## same round and then REVERTED in round 2 — see below; it traded a
    ## bounded-but-useless `sxUnknown` for a native-stack-exhaustion SIGSEGV.
    ##
    ## THREE fields are DELIBERATE, DOCUMENTED exceptions — not bugs, and
    ## nothing in this slice changes their runtime behavior. All three share
    ## one reason: the walker cannot survive unbounded descent along that
    ## axis, whether the descent is a Z3-level unroll or the host process's
    ## own native call stack.
    ##
    ## `maxCallDepth` (RFC-0010 B4 round 2): `isCall`'s depth check
    ## (`runtime.nim`) is implemented as ordinary native recursion in
    ## `walk` — one native stack frame per SUT call-stack level. A cap of 0
    ## disabling the check does not make the search "unlimited," it removes
    ## the only thing standing between the walker and the host's native
    ## stack limit. `w.activeCalls` does NOT rescue this: it only
    ## cycle-breaks recursion whose argument shape is IDENTICAL across
    ## levels (`argShapeKey`/`symValHash` hash the Z3 AST), so ordinary
    ## linear recursion like `f(n) = if n > 0: f(n-1) + 1 else: 0` produces a
    ## syntactically distinct AST at every level and is never caught. Two
    ## independent reviewers reproduced a SIGSEGV (native stack exhausted in
    ## under a second) against exactly this shape under `maxCallDepth: 0`.
    ## A crash is worse than the `sxUnknown` the guard traded it for: it
    ## takes the whole test BINARY down, not just one query, and violates
    ## this engine's Invariant 3 (never hang, always classify) more severely
    ## than an over-eager decline does. So `maxCallDepth: 0` exhausts
    ## immediately, by design, same as any other implausibly-tight budget —
    ## a caller wanting deep analysis writes an explicit bound sized to the
    ## SUT's real maximum call depth instead, which works and is honest.
    ## Measured directly (this engine's Linux/podman debug build, 8MB
    ## `ulimit -s`): unconstrained linear recursion is safe through a cap of
    ## 85 and SIGSEGVs by 88 — a "large-looking" round number like `1000` is
    ## NOT automatically safe, because the cap bounds NATIVE recursion depth,
    ## and this walker's per-level native stack cost turns out to be large
    ## (roughly 8MB / ~86 levels here). Pick a bound close to the depth you
    ## actually need, not an oversized safety margin, and treat the exact
    ## ceiling as build/platform-dependent rather than a fixed constant.
    ##
    ## `maxLoopUnwind` cannot honour 0 = unlimited without reopening a walker
    ## hang: `isWhile`'s wmExplore k-unroll forks BOTH the continue and exit
    ## branch whenever it is feasible (RFC-0005 S8k's per-iteration check;
    ## before S8k, at EVERY iteration unconditionally), so the active-path
    ## set never shrinks on its own for a loop with a symbolic trip count — `unwind = 0` read as "no bound" would not
    ## terminate for essentially ANY while loop reaching that arm, violating
    ## this engine's Invariant 3 (never hang, always classify). The
    ## concrete-replay counterpart (`walkWhileFollowConcrete`) is no safer in
    ## principle: its own pre-existing doc comment already says the bound is
    ## kept as a backstop specifically because a malformed/adversarial
    ## `concreteEq` must not hang the walker either. So `maxLoopUnwind`
    ## keeps its own, already-documented ">= 1" contract (below) instead —
    ## an explicit 0 there exhausts immediately, exactly like any other
    ## implausibly-tight budget, not unlimited.
    ##
    ## `seqInlineThreshold` was never actually covered by the promise at all
    ## (an audit gap this slice found and closes here, not a runtime defect —
    ## see its own field doc below for the full mechanism). It selects between
    ## two equally-sound modeling strategies rather than gating an exhaustion
    ## decline, so `0` means the SEMANTIC OPPOSITE of unlimited: "always
    ## axiomatize, never inline."
    queryRLimit*: uint = 250_000_000
      ## Z3 logical step count bound. `0` is unbounded.
      ## Wired into `runtime.nim:trySolve` via `Z3_solver_set_params`.
      ## Phase 13.
      ##
      ## RFC-0005 S8bu: the default is `250_000_000`, no longer `0`. Every
      ## other solve the walker issues was already bounded under the
      ## defaults (the loop and path feasibility checks, the tainted
      ## target-hit solve, the concrete-branch solves, and every query
      ## naming a string / seq through `seqQueryRLimit`); a target-hit
      ## query over plain arithmetic was not, and one Z3 does not decide
      ## (S8bs's int-field read across the signed `bv2int` bridge) left the
      ## walk running forever. Now such a query runs out of the budget and
      ## is `sxUnknown` with `beSolverUndef` naming it: a decline, never a
      ## hang. Not the `20M` the other bounds use: a target-hit query that
      ## decides without one can need more (`tsymex_augmented_assign`'s
      ## 64-bit `acc * x == 12` needs between 100M and 150M units on Z3
      ## 4.13.4, about 55 s, and 20M made it `beSolverUndef`); `250M` is past
      ## that with room, and at ~2M units/s about two minutes of search.
      ## The default does not raise the solves bounded by
      ## `defaultConcreteBranchRLimit` (`concreteBranchRLimit`,
      ## `taintedSolveRLimit`), which take a `queryRLimit` other than this
      ## default as the caller's. An explicit `0` still means unbounded
      ## (this type's `0 = unlimited` contract, RFC-0010).
    maxSeqLen*: int = 128
      ## RFC-0005 S8k. The longest string / seq (in elements -- bytes for a
      ## `string`) any solver query may choose for one term. Default `128`.
      ## `0` means unlimited. Every query the walker issues caps each
      ## uninterpreted seq-sorted term (an input, a fresh return, a heap
      ## `select`) at this length (`runtime.nim`'s `checkCapped`): a model
      ## found under the cap is a model of the query; an UNSAT is the
      ## query's own only when the query without the sequence theory, or
      ## an unsat core without the cap, shows it; an UNSAT the cap took
      ## part in is neither, and the solve is `zsUnknown` -- recorded as
      ## `beSolverUndef` naming this field.
      ##
      ## Why a cap and not `queryRLimit`: Z3's sequence solver explores
      ## lengths upward, and its work per step grows super-linearly with
      ## the length (measured on the pinned Z3, `len(s) > N` alone: N=100
      ## 1.4 s, N=200 19 s and 1.6 GB, N=300 102 s and 3.4 GB). Past ~250
      ## elements single steps run for minutes WITHOUT polling the resource
      ## counter, so neither `rlimit` nor a wall-clock `timeout` stops them
      ## (a 10 s `timeout` returned after 102 s; `findColon(s, 0) > 1000`'s
      ## query never returned). Under the cap Z3 never takes those steps,
      ## and `seqQueryRLimit` bounds what remains. `128` admits the 100-byte
      ## witnesses the existing suites pin (`s.len == 100 and s[99] == 7`).
    seqQueryRLimit*: uint = 20_000_000
      ## RFC-0005 S8k. The Z3 `rlimit` of every query that mentions a string
      ## or seq (one `maxSeqLen` caps), when smaller than the query's own
      ## (`queryRLimit`, `0` = unbounded, or the tainted target-hit budget).
      ## `0` means no extra bound. The query's model search (the capped
      ## check, then the uncapped one) spends at most this in all, half
      ## per check (`checkCapped`). Under the cap the sequence solver DOES
      ## poll the counter, but it can spend it slowly (measured on the
      ## pinned Z3: 40-55k units/s, against ~1M/s for arithmetic). In the
      ## lowered byte-test form `s.len == 20 and s[19] == 'q'` needed 2.3M
      ## units (~60 s) and the same at length 100 34M (~10 min); the query
      ## now takes a byte equality in its character form (`checkCapped`),
      ## which decides both at once, but other string queries still cost
      ## that much, and unbounded (the default `queryRLimit`) nothing
      ## stopped a within-cap query that needed more.
      ## `20M` is the bound `concreteBranchRLimit` and the tainted target-hit
      ## solve already use by default (`defaultConcreteBranchRLimit`): a few
      ## minutes of sequence search at most. Deterministic (a step count,
      ## not a clock), so a query it cuts off is the same `beSolverUndef` on
      ## every machine, and cacheable. Ignored when `maxSeqLen == 0` (no
      ## cap, no bound: the caller opted out of both).
    queryTimeoutMs*: uint = 600_000
      ## RFC-0005 S8bu. A wall-clock bound, in milliseconds, on every solve
      ## the walker issues (Z3's `timeout` solver parameter), beside the
      ## step bounds above. `0` means none. A solve it cuts off is
      ## `zsUnknown`: `sxUnknown` with `beSolverUndef` naming this field,
      ## and the run's verdict is not written to the verdict cache (it is
      ## the machine's, not the program's).
      ##
      ## Why a clock beside `rlimit`: Z3 can stop advancing its step
      ## counter. A mixed Int / bit-vector query (`sbv2int(r) == 2 *
      ## sbv2int(k) and r != 2 * k`, from an `int` read back out of an
      ## Int-sorted heap) reached 12.4M units in 10 s and then stayed
      ## there: at 60 s it had 12.47M, and under a 20M `rlimit` it ran past
      ## 250 s without returning; Z3's `timeout` stopped it on time. A
      ## step bound cannot end a search that takes no steps, so without a
      ## clock no default bounded every query. `600_000` (10 minutes) is
      ## past where `seqQueryRLimit` / `queryRLimit` end the slowest search
      ## measured (the sequence solver spends 20M units in about 6-8
      ## minutes at 40-55k units/s), so on a query whose counter advances
      ## the step bound, which is deterministic, still answers first; the
      ## clock is the backstop for one whose counter does not.
    walkRLimit*: uint = 1_000_000_000
      ## RFC-0016 K7. The total work units every solver check of ONE walk may
      ## spend together (Z3 `rlimit` units plus, at `walkerTermUnits` per term
      ## visit, the walker's own query construction and fact passes, so the
      ## budget bounds wall time and not only solver time); `0` opts out (unbounded). The
      ## per-query bounds above do not bound the SUM: a loop nest whose
      ## unrolled paths multiply (`for l in s.splitLines` over an unbounded
      ## `string`: three nested loops, each unrolled 5x, the live set 1, 33,
      ## 594, ...) issues thousands of fast checks, each well under
      ## `queryRLimit`, and no live-path cap bounds the work (it grows as
      ## `(5 * cap) ^ depth`). Every check of the walk is charged
      ## (`ownContextCheck`); a query runs under at most what is left, and
      ## once the total is spent the walk stops: the paths not yet decided
      ## are dropped as `beBudgetExhaustedPrune` (`sxUnknown`, cap
      ## `ckWalkWork`), while a target already reached with a sound witness
      ## stays a hit. Deterministic (a step count, not a clock), so a walk it
      ## cuts is the same on every machine, and cacheable: it is part of the
      ## cache key. A walk's spend is appended to the file named by the
      ## environment variable `NELLI_WALK_UNITS_LOG` (`logWalkUnits`), which
      ## is how this default is re-measured.
      ##
      ## Why `1_000_000_000`: measured over the whole suite (1047 test files,
      ## 7818 walks, 2026-11-09, sha d5d1d563). The largest walk that reached
      ## a decided verdict spent 175,310,967 units (`label:prod12`, `sxSat`,
      ## `tests/tsymex_augmented_assign.nim`); the next decided walks spent
      ## 25,590,064 (`label:wrapped`) and 20,955,494
      ## (`label:s8cj_wide_factoring`, `sxRaised`). The default is about 5.7x
      ## the largest decided walk, so no decided verdict in the corpus is lost
      ## to the cap. The largest walks overall (175.3M, then 120,601,918
      ## `label:ti_tuple` and 103,233,480 `label:t`, both `sxUnknown`) were
      ## undecided anyway. Re-measure when the corpus or the solver changes.
    tailWalkCappedChecks*: int = 5
      ## RFC-0016 W3-z R9. The work units the whole-run gate's tail walk
      ## (`verifyTailDefined`, one per label `sxSat` and per replay candidate)
      ## may spend together, counted in capped scratch checks: the tail walk
      ## stops once its checks spent this many times the rlimit one of its
      ## scratch checks runs under (`concreteBranchRLimit`, 20M units unless
      ## `queryRLimit` is set). Past it the tail fails closed: the `sxSat`
      ## stands but is untrusted (`ubTailUnverified`). `0` opts out (only
      ## `walkRLimit` bounds it).
      ##
      ## The budget is the run's (RFC-0016 W3-z int4r): every tail walk of one
      ## run draws on it, the winner's or one per replay candidate, and a walk
      ## that starts with none left fails closed at once. Per walk, a run with
      ## eleven candidates spent up to eleven budgets
      ## (`tsymex_r6_n36_raise_degrade`, past 900 s).
      ##
      ## Why: a branch the witness's pins leave open (a global havoc, an
      ## opaque call's result) is forked both ways (W3-z R6), and each fork
      ## asked its scratch checks at the cap when the query was hard; in a
      ## nested loop the forks multiplied the capped checks until `walkRLimit`
      ## (about 50 capped checks, over 20 minutes; `tsymex_r6_b7r_bytescan`
      ## B7R-6 ran past 1500 s). Why `5`: one undecided branch used to cost
      ## four capped checks (two asks, each both ways) and now costs one (a
      ## capped check is not asked again), so five covers the old worst
      ## branch with one to spare; under the defaults it is 100M units, a
      ## tenth of `walkRLimit`, and 200 times the largest decided tail walk
      ## measured (499,300 units, `tsymex_0016_k10b_round`). Part of the
      ## cache key: it decides whether a verdict is trusted.
    maxFrontierSize*: int = 0
      ## Issue #163 item 3 (rev). The one INCREMENTAL per-statement frontier
      ## cap — `walkBlock` (`runtime.nim`) prunes the post-step path
      ## frontier down to this many paths (highest-uncertainty-first
      ## eviction) whenever it grows past the cap, tainting the evicted
      ## paths' contribution as `sxUnknown` via the classified
      ## `beBudgetExhaustedPrune` kind (RFC-0005 S6a; `beBudgetExhausted`
      ## before it) (Invariant 3 — an honest degrade, never a
      ## silent truncation that could fake an `sxSat`/`sxUnsat`). `0` STAYS
      ## the documented opt-out meaning UNLIMITED (this field is in the
      ## `ResourceBudget` majority `0 = unlimited` covers, unlike
      ## `maxCallDepth`/`maxLoopUnwind` — see the type's own umbrella
      ## comment) — this only changes what an OMITTED field gets.
      ##
      ## Before this, the omitted-field default was Nim's bare zero —
      ## unbounded — with no cap at all on multiplicative path growth. This
      ## matters more since finding R22 added a `RangeDefect` fork at ranged
      ## assignments: a ranged loop counter can now fork per iteration
      ## whenever its `ziIvl` discharge is defeated by an unconstrained RHS
      ## operand, and `maxLoopUnwind`/`maxCallDepth` bound other axes but
      ## nothing bounded this one.
      ##
      ## `256` is MEASURED, not guessed (2026-09-18, this engine's Linux/
      ## podman debug build, `walkBlock` instrumented with a temporary
      ## max-frontier-seen counter in a throwaway `git worktree`, never
      ## committed): the LARGEST post-step frontier any of ~20 sampled
      ## heavy/branchy existing suites reached — including every suite this
      ## round's own regression list calls "large"
      ## (`tsymex_161_overflow_obligation`, `tsymex_162_range_base_width`,
      ## `tsymex_163rev_assign_rangedefect`), plus the dedicated frontier-
      ## pruning suite, several deep-nested-if/while/case suites, and every
      ## variant/multivariant/container suite sampled — was **16**
      ## (`tsymex_r6_n9_variant_budget.nim`). `256` is 16x that measured
      ## ceiling: comfortably clear of anything a currently-green, currently-
      ## TERMINATING analysis in this codebase actually reaches, while still
      ## bounding a runaway multiplicative blow-up to a small constant
      ## instead of letting it run unchecked (the R22 concern this field
      ## exists for). Also matches an existing precedent value already
      ## chosen by a test author in this exact codebase for this exact field
      ## (`tsymex_phase7_assertcovered.nim`'s `lax` config), rather than an
      ## arbitrary round number invented fresh.
      ##
      ## One sampled suite (`tsymex_snd3_loopdegrade.nim`) did not terminate
      ## within a 300s bound even at HEAD, with no frontier cap at all
      ## (confirmed independently of this instrumentation) — a pre-existing,
      ## out-of-scope non-termination this change does not need to fix, but
      ## also cannot regress: it was not passing before, so a `256` cap
      ## converting its eventual fate to an honest, fast `sxUnknown` (should
      ## its frontier ever exceed 256) would be a strict improvement, not a
      ## truncation of anything that used to pass.
    maxCallDepth*: int = 3
      ## Upper bound on symbolic call-stack depth explored by `isCall`'s
      ## walker arm (`runtime.nim`) before bailing with a fresh
      ## unconstrained return value. Default `3`. `0` does NOT mean
      ## unlimited (RFC-0010 B4 round 2 — REVERTED from an earlier `0 =
      ## unlimited` claim; see the type's own umbrella comment above for the
      ## full rationale). The check is ordinary native recursion in `walk`,
      ## so disabling it lets ordinary linear recursion (not just a
      ## pathological shape) exhaust the native stack and SIGSEGV the whole
      ## process — `w.activeCalls` only cycle-breaks recursion with
      ## IDENTICAL argument shapes and does not catch this. An explicit `0`
      ## here exhausts on the very first call, same as any other
      ## implausibly-tight budget. A caller who wants deep analysis should
      ## write an explicit bound sized to the SUT's real maximum call depth
      ## instead. This cap bounds NATIVE recursion depth, and what one
      ## level costs is build- and backend-dependent; RFC-0005 S8ca: the
      ## walk no longer trusts the count alone. A call is not inlined when
      ## the native stack left below it is under what one more level needs
      ## (`nativeStackShort` in `runtime.nim`): it declines in-band
      ## (`beBudgetExhaustedUnmodelled`, naming the native stack) at any
      ## `maxCallDepth`, about 48 levels on an 8 MB stack on c, 40 on cpp,
      ## 3 on 1 MB. Before S8ca a large cap overflowed the stack (SIGSEGV):
      ## 50 levels on cpp, 88 on c.
    maxRecursionDepth*: int = 24
      ## RFC-0005 S8ax. The hard budget on the call-inlining depth. Past
      ## `maxCallDepth` the walk keeps inlining while the frontier is not
      ## growing -- the callee walks entered at the next depth would not
      ## outnumber those at the depth above -- up to this depth (or
      ## `maxCallDepth`, when that is higher). A recursion whose depth its
      ## arguments decide is then followed to its base case; one that fans
      ## out declines at `maxCallDepth` as before. Default `24`. Past it the
      ## call declines (`beBudgetExhaustedUnmodelled`), naming both budgets.
      ## `0` turns the extension off. The same native-stack check as
      ## `maxCallDepth`'s applies (RFC-0005 S8ca): on a 2 MB thread the
      ## extension's 24 levels overflowed the stack before it.
    maxLoopUnwind*: int = 5
      ## Phase-6 loop unrolling cap; >= 1 — one of the ResourceBudget fields
      ## `0` does NOT mean unlimited for (RFC-0010 B4; see the type's own
      ## umbrella comment above for the full hang-safety rationale). Default
      ## 5 (`defaultSymexSettings`).
      ##
      ## This is an INTENTIONAL decidability boundary, not a bug surface
      ## (chapulin round-3/4 doc note): a loop whose trip count is bounded
      ## by a SYMBOLIC quantity cannot be decided by ANY finite unroll —
      ## chapulin's own bisect of its dependent-scan shapes confirmed
      ## unwind 2 vs 5 give the identical `sxUnknown` (it is decidability,
      ## not budget). Raising this helps only loops whose REAL trip count
      ## is a small concrete number above the default. Exhaustion is
      ## always classified (`beBudgetExhausted`, v64 — never a bare
      ## sxUnknown) with the configured bound in the message, and the cap
      ## is per-call: pass a `SymexSettings` with a different value to
      ## `symexFind`. The structural levers for symbolic trip counts are
      ## the closed-form lifts (Q1's scan-to-indexOf, ADR-0025; strip's
      ## decomposition, ADR-0026), not a larger k.
    maxHeapDepth*: int = 8
      ## Phase 15 Cluster R (R1a, ADR-0010). Upper bound on the recursive
      ## `ref object` field-expansion / heap-read (`isDeref`) hop count per
      ## path. Default `8`. `0` means unlimited. When a `p[]` deref would
      ## push `path.heapDepth` past this bound the walker halts with
      ## `sxUnknown` + `SymexErrorInfo{kind: heDepthExhausted}` (R9).
    maxFreshnessAssertions*: int = 256
      ## Phase 15 Cluster R (R2, ADR-0010). Upper bound on the number of
      ## fresh-ref distinctness inequalities (`newRef != prior`) the walker
      ## will emit on a SINGLE path. Default `256`. `0` means unlimited.
      ## SOUND over-approximation (heFreshnessCapExceeded hint).
    maxClosureInlineCount*: int = 64
      ## Phase 15 C2b (ADR-0009 D6). Per-call-stack cap on nested closure
      ## descent. Default `64`. `0` means unlimited.
      ## ceInlineBudgetExceeded (sevError) when exceeded.
      ## R2-10: unlike `maxCallDepth`, this guard has no independent
      ## cycle-breaker behind it (`w.activeCalls` cycle-breaks identical
      ## argument shapes, but closure descent has nothing analogous) — the
      ## `cap > 0 and` check IS the only thing stopping unbounded descent.
      ## `0` is safe today only because a forward-declared self-referencing
      ## closure is declined with `ceClosureUnknownCallee` before it can
      ## recurse — i.e. closure self-recursion is not representable in the
      ## DSL's symex model. Latent, not live: reopen this if that ever
      ## changes.
    maxInstantiationsPerProc*: int = 64
      ## Phase 15 G1c (ADR-0008 D7 / OQ5). Per-base-proc cap on DISTINCT
      ## generic instantiations the parser will register. Default `64`.
      ## `0` means unlimited. geInstantiationCapped (sevError) when exceeded.
    maxVariantConstructorForks*: int = 8
      ## Round-6 A3 (ADR-0029). Structural cap on the number of tags
      ## `isVariantConstructSym` will fork per symbolic-discriminant variant
      ## CONSTRUCTION — checked against `vcsTagSet.len` (parse-time
      ## `case`-branch-narrowed, or the full declared non-else arm count)
      ## BEFORE any solver work, mirroring `maxSplitParts`'s structural-cap
      ## style. Default `8`. `0` means unlimited. Exceeding it classifies a
      ## `beBudgetExhaustedUnmodelled` decline (RFC-0005 S6a; sxUnknown) —
      ## never a crash, never an
      ## unbounded fork explosion for a wide unconstrained enum.
    maxVariantConstructorFieldAllocs*: int = 64
      ## N9 (round-6 review remediation, ADR-0029 companion), unit corrected
      ## by D2 (round-6 review remediation). Structural cap on TOTAL per-fork
      ## LEAF Z3 ALLOCATIONS `isVariantConstructSym` will perform:
      ## `vcsTagSet.len` (the fork count `maxVariantConstructorForks` already
      ## bounds) times the sum of `allocCostOf(ft)` (`smt/types.nim`) over
      ## every field type `ft` across EVERY declared arm of `vcsVariantTy`
      ## (every fork allocates FRESH fields for ALL arms, not just the
      ## fork's own tag — see `isVariantConstructSym`'s own doc comment).
      ## The unit is LEAF ALLOCATIONS, not flat field COUNT: `allocCostOf`
      ## mirrors `allocateSym`'s own recursion, so a composite field type
      ## (`array[N, T]`, nested tuple/variant) contributes its true
      ## allocation cost (e.g. `array[1_000_000, int]` costs 1,000,000, not
      ## `1`) — D2's fix for the gap N9 left open, where a flat field COUNT
      ## bounded the number of fields but nothing bounded what each field
      ## itself cost to allocate. `maxVariantConstructorForks` alone only
      ## bounds the OUTER fork count; it does nothing to bound a wide or
      ## deeply-composite variant, letting per-fork allocation amplify
      ## unboundedly (forks x total-arm-leaf-allocations) even when the fork
      ## count itself is comfortably under budget. Checked BEFORE any solver
      ## work, same structural-cap style as `maxVariantConstructorForks`.
      ## Default `64` (unchanged by D2 — the unit changed from "fields" to
      ## "leaf allocations", which is the honest unit; a composite-fielded
      ## shape that previously passed at exactly 64 flat fields may now
      ## exceed 64 leaf allocations and decline — the intended behavior
      ## change). `0` means unlimited. Exceeding it classifies the SAME
      ## `beBudgetExhaustedUnmodelled` decline kind (RFC-0005 S6a; never a
      ## parallel mechanism) —
      ## never a crash, never unbounded allocation work for a wide- or
      ## deeply-fielded variant.
    maxSplitParts*: int = 8
      ## Phase 15 S5. Upper bound on the number of parts a symbolic
      ## `string.split` decomposition may produce. Default `8`. `0` means
      ## unlimited.
    seqInlineThreshold*: int = 8
      ## Phase 15 C4 (net-new, ADR-0009). Upper bound on CONCRETE seq
      ## length a DSL HOF will UNROLL inline. Default `8`. A concrete
      ## length above this bound — or a SYMBOLIC length — takes the
      ## axiom path. Ignored when `inlinePolicy` is not `ipHybrid`.
      ##
      ## RFC-0010 B4: one of the three fields the umbrella "0 = unlimited"
      ## promise does not reach (see that comment for the full list) — and
      ## the only one of the three for the OPPOSITE reason. The other two are
      ## descent bounds the walker cannot survive removing; this is not an
      ## exhaustion cap at all. It is a strategy-selection threshold between
      ## two equally-sound modeling paths (`lowerHofCall`, `runtime.nim`:
      ## `canInline = lenOpt.isSome and lenOpt.get <= threshold`). `0`
      ## therefore means the SEMANTIC OPPOSITE of unlimited: every concrete
      ## length except an empty seq fails `<= 0`, so `0` selects "always
      ## axiomatize, never inline," not "inline without bound" (a zero-length
      ## seq satisfies `0 <= 0` and inlines, which is a no-op either way).
      ## Exceeding the threshold is not a decline (never
      ## `beBudgetExhausted`, never `sxUnknown` on its own) — it is a normal,
      ## sound path switch, so there is no exhaustion behavior to fix here.
