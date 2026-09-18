# Issue #163 — an opaque call ahead of the target must not cost the answer

Issue-scoped handoff (not an RFC; no `docs/rfc/NNNN` number). Newest entries
at the BOTTOM.

- **Branch:** `rfc-161-163-symex-defects` — the combined branch, created at
  the same sha as `rfc-163-opaque-call-taint` once it became clear the three
  issue branches were ALREADY cumulative (each was cut from the previous
  one's tip, so `main` is an ancestor and all 22 commits sit in one linear
  line; nothing needed merging, only a name that says so). The three
  per-issue branch names remain as markers. Still `rfc-*` deliberately — the
  three Windows legs trigger on `[main, 'rfc-*']`.
- **Consequence of the stack:** #161 and #162 can no longer be evaluated
  independently. The walker version is cumulative (125→132 across the three)
  and #162 retires a trip-wire #161 deliberately planted, so gates and audits
  are scoped to the COMBINED surface.
- **Base:** `ac507c1` (the tip of #162). The stack is incidental, not
  semantic: #163 touches the opaque-call arm and the pragma plumbing, which
  #161/#162 never went near. It is stacked only because #162 has not
  fast-forwarded to `main` yet.
- **Issue:** #163.
- **Test file:** `tests/tsymex_163_opaque_transparent.nim`.

## The defect

`walk`'s `#137` opaque-call arm (`runtime.nim`, `if stmt.opaque:`) did two
things unconditionally: set `w.sawUnknown = true` and continued every path via
`forkPathTainted`. So any target reached *after* an opaque call degraded the
whole run to `sxUnknown`.

Reproduced at `ac507c1` (`scratchpad/bench/probe_163_opaque.nim`, gitignored):

| SUT | `tRaisedExn` | `tLabel` |
|---|---|---|
| `plain` | `sxRaised` | `sxSat` |
| `withEcho` (echo *before* the branch) | `sxUnknown` | `sxUnknown` |
| `echoAfter` (echo *after* the branch) | `sxRaised` | — |
| `covered` (`{.cover.}`) | `sxUnknown` | **`sxSat`** |
| `callsCovered` (plain proc calling a `{.cover.}`'d one) | `sxUnknown` | — |

The `covered`/`tLabel` cell is the one the issue predicted as `sxUnknown` and
which measured `sxSat`. It is not a discrepancy, it is the mechanism in plain
view: `{.cover.}` injects `recordEdge` *inside each branch arm*, so the
fall-through path (no `else` arm to instrument) reaches the trailing label
untainted, while the raise path — which goes through the instrumented `if`
arm — does not. `withEcho` degrades both queries because `echo` sits ahead of
every path.

Every `sxUnknown` carried exactly one error: `weInternalWalkerFault`,
"sxUnknown produced with no classified reason". That is the Invariant-7
backstop firing, i.e. the walker reporting *its own bug* for an ordinary
unmodelled call.

## Two problems, deliberately kept separate

1. **The taint is too coarse.** Correct for an opaque call whose result is
   used or that can mutate state the SUT reads. Wrong for a void call taking
   only values — `recordEdge(id)`, `logCmp(lhs, rhs, op)`, `echo "x"`.
2. **The degrade is unclassified.** Even where the taint is right, the user
   should learn *which call* cost them the answer.

## Design decision — `{.symexTransparent.}` is a promise, not a heuristic

`{.symexOpaque.}` says "do not enter this body". It buys that with a path
taint, which is the right price for `readSensor()` and the wrong price for
`recordEdge(id)`. `{.symexTransparent.}` says the stronger and, for
instrumentation, *true* thing: the call is void, takes only values, and
touches nothing the SUT can read back — so symex deletes it.

Three judgement calls worth recording:

- **Statement position only.** The parser honours the pragma where Nim's own
  typing already guarantees there is no value to drop. A
  `{.symexTransparent.}` proc whose result *is* used reaches the expression
  arm, which gives it `{.symexOpaque.}` handling instead. An over-claimed
  pragma therefore costs precision, never soundness — and the half of the
  opaque contract it still earns (body not walked) is the half that keeps the
  G3fix `KeyError` closed.
- **Arguments are still parsed**, into the preamble; only their values are
  discarded. The pragma is a promise about the *callee*, not about the
  expressions at the call site: Nim evaluates those regardless, so dropping
  them unparsed would silently delete any effect they carry, and any honest
  degrade an unmodellable argument owes. Both instrumentation shapes parse to
  nothing but a value, so the preamble stays empty in the motivating case.
- **`recordEdge`/`logCmp` were RETAGGED, not double-tagged.** Carrying both
  pragmas would have been a hedge with no owner ("which wins?"). The G3fix
  pin (`tests/tsymex_g3fix_walkergap.nim`) is the safety net that proves no
  route regressed to walking their bodies: it still passes.

## Slice status

| # | Slice | Commit | Nature |
|---|---|---|---|
| 1 | `{.symexTransparent.}`; parser drops the call; instrumentation retagged | `b859b4a` | fix |
| 2 | pin `{.covercmp.}`, `{.cover, covercmp.}`, instrumented-callee | `4c7256d` | pins only |
| 3 | classify the remaining degrade (names the callee) | `0c85b80` | fix (walker 130→131) |
| 4 | an inert opaque call does not taint | `ea21496` | fix (walker 131→132) |
| 5 | nimble registration + version floor pin | `1e91448` | pins only |

### Slice 1 — the floor

`hasSymexPragma(sym, name)` (generalised from `hasSymexOpaquePragma`) +
`hasSymexTransparentPragma`; the statement-position call arm in
`dsl_parser.nim` returns `mkBlock(@[])` — the established no-op — for a
transparent callee; `coverage.nim` declares its own private
`template symexTransparent() {.pragma.}` (it must stay a Z3-free leaf, so it
cannot import `nelli/symex`; the parser matches pragmas purely by NAME, which
is what makes the private copy sufficient); `symex.nim` exports a public
`symexTransparent*` beside `symexOpaque*`.

**No walker version bump.** This is a parse-time change: the IR itself
differs, so `canonicalize(prog)` moves the cache key on its own and no stale
verdict can be replayed.

### Slice 2 — pins, no implementation

All four passed on first run against slice 1. All four were then verified RED
against `ac507c1`'s `src/` (same test file, `git checkout ac507c1 -- src/`),
so they are sensitive pins rather than vacuous ones.

### Slice 3 — the degrade names the call

New classified kind `feOpaqueCallUnmodelled` (sevError), appended at the enum
tail for ordinal stability, sunk into `w.walkDegradeErrors` (whose drain
dedups by message, so N calls to one callee collapse to one entry while two
callees each get named). `fe` and not `we` deliberately: the black-box
decision is the front end's — the parser chose `mkOpaqueCall` — and this is a
construct gap, not a walker fault.

Walker 130→131. Not a verdict change (the status is `sxUnknown` before and
after) but `r.errors` is part of the cached result, so a v130 entry would
replay the old misdiagnosis.

### Slice 4 — the engine proves inertness for an untagged call

`{.symexTransparent.}` is the author's promise. Slice 4 is the engine proving
the same thing for a call nobody tagged, keeping the `mkOpaqueCall` IR and
dropping only the taint. An opaque call is **inert** iff it binds no result
AND every actual argument is plainly value-typed: no `nnkHiddenAddr` (which
IS how Nim passes a `var` formal) and a `typeKind` in a closed allowlist of
`ntyBool`/`ntyChar`/`ntyString`/`ntyEnum`/`ntyRange` and the int/uint/float
families, with `nnkHiddenStdConv`/`ntyVarargs` unwrapped to its `nnkBracket`
elements. `ntyObject`, `ntyTuple`, `ntySeq`, `ntyRef`, `ntyPtr`, `ntyProc`
and `ntyCString` are excluded — a copied object can carry a `ref` field whose
pointee the callee writes, and a `cstring` is a writable pointer. Unrecognised
means not inert.

**The soundness argument, which was measured and not argued.** With no bound
result and nothing writable passed in, the only channel left is a
module-level global. The walker does not model globals AT ALL: a SUT
branching on one already answers `sxUnknown` carrying a raw `KeyError: key
not found: gLimit`, independently of any opaque call
(`scratchpad/bench/probe_163_globals.nim`). So a SUT that could observe such
a mutation has already degraded at its own read site, and dropping this taint
cannot introduce a false verdict. What it forgoes is a callee that never
returns or that raises — a pre-existing, symmetric gap, since `echoAfter`
(echo *after* the branch) already answered `sxRaised` before any of this.
Ordering, not soundness, is what changed.

Five sites: `IRStmt.opaqueInert` + `mkOpaqueCall(..., inert = false)`
(`types.nim`), the predicate + the statement-position call site
(`dsl_parser.nim`), **`emitStmt`'s round-trip** (`dsl_parser.nim` — the
#162-slice-5 trap: the walker never sees the macro-time `IRStmt`, only the
value rebuilt from those `newCall` nodes, so a field omitted there silently
reverts to its default and the tests stay red *identically* to before the
fix), `canonicalize`'s `;inert=` rider, and the walker's
`if stmt.opaqueInert: return paths`.

Walker 131→132. A real verdict change this time.

### Slice 4's RED was verified after the fact

The slice was implemented before its tests were written. Re-checked against
slice 3's `src/` (`git checkout 0c85b80 -- src/`): both positive tests fail
there, with the classified `feOpaqueCallUnmodelled` naming `echo` visible in
the failure output — which incidentally confirms slice 3 end-to-end. The
var-param and ref-arg pins PASS at slice 3, as they must: they assert
behaviour slice 4 deliberately leaves unchanged. They guard the predicate
against over-reach ("void means inert"), not against the base commit.

## Method note — the oracle is executed, not asserted

Inherited from #162. Every symbolic expectation in the test file is paired
with the same computation run for real in the same file: the oracle test calls
all four instrumented SUTs and checks each raises on `Magic` and only on
`Magic`. A taint bug is exactly the shape where a test can encode the engine's
own wrong model and pass.

## Gates run

| Gate | Result |
|---|---|
| `tsymex_163_opaque_transparent`, `c` | 12/12 |
| `tsymex_163_opaque_transparent`, `cpp` | 12/12 |
| `tsymex_phase15_CR2_cachekey`, `c` | 7/7 (v132 pin) |
| `tsymex_g3fix_walkergap`, `c` | 1/1 — the crash pin guarding the pragma plumbing |
| full `sweep.sh` diff vs `ac507c1` | **see below** |

Sweep baseline taken the way #161's handoff prescribes: a worktree pinned to
the base sha with `_deps` and `nim.cfg` **copied in** (they are
milpa-generated and gitignored; without them every test fails to compile and
the log reads 100% `rc=1`). Baseline and current run strictly sequentially —
concurrent `dt-bounded` runs of the same test file clobber one shared binary.

## Surfaced, not fixed here

- **A module-level global read reports `weInternalWalkerFault` carrying a raw
  `KeyError`.** Measured while establishing slice 4's soundness: a SUT
  branching on a module-level `var` degrades with "KeyError: key not found:
  gLimit" classified as a walker fault. This is the SAME unclassified-degrade
  class as #163's second defect, at a different site (`lower(iekVar)`), and
  it is a common enough SUT shape to deserve its own issue. Not filed —
  deliberately left for Corey rather than widening #163.
- The opaque arm is not the only site that sets `w.sawUnknown` bare; the
  `maxCallDepth` bail and the missing-`ProcSig` bail in the same `isCall`
  dispatch have the same shape. The missing-`ProcSig` one is classified in
  practice (`geInstantiationCapped` rides `prog.parseErrors`); the
  `maxCallDepth` one is worth an audit of its own. Not widened into #163.
- #159 (`recordEdge`'s inferred `.sideEffect` makes `{.cover.}` unusable on
  `func`/`noSideEffect` targets) is adjacent but independent — it is about
  Nim's effect system, not symex's taint.

## Current stage — audit complete, remediating all 13 findings

#163's own five slices are landed and green on both backends. The
`/wiring-audit` over the combined surface is COMPLETE (three lenses: A =
#163 pragma/opaque, B = #161/#162 overflow/range, C =
cache-key/CI-reach/ledger-truth). Corey's call: **push, and fix everything
now.**

### Verdict — the surface did NOT close clean

`wiring` is deliberately NOT set to `proven`, and `/code-review` stays
gated. The load-bearing property is reachable and test-proven for what is
pinned, but three gaps of the SAME defect class #162 slice 5 closed are
still open (seq elements, `ref object` fields, char-bounded aliases), and
until the push below nothing had been verified on the platform all three
handoffs say must verify it.

### Done since the audit

- **W1 closed.** `git push -u origin rfc-161-163-symex-defects`. All three
  Windows legs fired on the combined branch for the first time —
  `symex-mingw` (runs 35308512446), `fuzzer-mingw`, `fuzzer-msvc`. Seven
  walker bumps across three issues had until now been verified only in
  local Linux/podman sweeps.

### In flight — four agents, partitioned by file so they cannot collide

| Agent | Findings | Owns |
|---|---|---|
| 1 | W3 char-range alias, W7 enum domain | `dsl_typebridge.nim`, new `tests/tsymex_164_range_domain_reach.nim` |
| 2 | W11 registration, W12 floors, W13 ledger truth | `nelli.nimble`, pin files, handoffs |
| 3 | W5 pragma-fallback pin | `tests/tsymex_163_opaque_transparent.nim` |
| 4 | W2 seq elements, W4 ref-object fields | `runtime.nim`, `runtime_heap.nim`, new `tests/tsymex_164_range_elem_reach.nim` |

**Wave 2, NOT yet started:** W6, W8, W9, W10 all live in `runtime.nim`,
which agent 4 owns — concurrent edits would lose work. They start when
agent 4 lands.

### Three decisions taken during remediation

- **One version bump, not seven.** Every agent is forbidden to touch
  `symexWalkerVersion`, `canonicalize.nim` or the CR2 pin value; the
  control loop lands a single **132→133** at the end documenting every
  semantic change. Seven agents each editing those two files would conflict
  on every commit, and one increment invalidates the cache as completely as
  seven.
- **W2 asserts at READ sites, not via a quantified constraint on the
  backing array.** A `forall` over the seq array would be exact but drags a
  quantifier into every seq query, against the engine's lazy-materialisation
  style. Cost: an element never read stays unconstrained — sound for
  verdicts, NOT for witnesses, so extraction must clamp too. Both halves
  required or the finding is not closed.
- **The W5 pin must be mutation-tested.** A test that merely passes proves
  nothing for an absent-call finding; agent 3 must delete the fallback
  disjunct, watch its test fail, and restore it.

### Remediation progress

Closed: **W1** (push; all three Windows legs fired, `fuzzer-mingw` green),
**W5** (`7d0ee90` + `d5108de`), **W11/W12/W13** (`a1fc02c`, `9206071`,
`7878212`), **W3/W7** (`05f8e01`). Remaining: W2/W4 in flight; W6, W8, W9,
W10 queued behind them in `runtime.nim`; then the single bump.

**W5's pin was strengthened after the fact.** The delivered version used
`probe(): int = 7`; removing the fallback disjunct made the walker descend
into the literal, solve `x + 7 == Magic`, and answer `sxRaised` — a MORE
precise answer, so the test pinned a precision choice rather than the
property the disjunct exists for. `probe` now reads a module-level var, so
removing the disjunct produces `weInternalWalkerFault: KeyError: key not
found: probeState` — the G3fix crash shape. Re-verified by mutation both
ways. Status is `sxUnknown` either way, so the error-KIND assertions are
load-bearing, not decoration.

### OPEN VERIFICATION — do not mark W3/W7 done until resolved

Two agents reported different counts for `tests/tsymex_162_range_base_width.nim`:
agent 2 said **21/21**, agent 1 (running it as non-regression WITH the
W3/W7 `dsl_typebridge` change applied) said **20/20**. The file contains 21
`test` blocks and agent 2's commit added none, so either agent 1 miscounted
or one test stopped running under the enum/char-range change. Re-run it
directly once agent 4 releases the file (both were told to use it as a
gate, and concurrent runs of one test file clobber a shared binary).

### New defects surfaced by W7's work — NOT fixed, candidates for filing

- **`symexFind` fails to COMPILE for any proc taking an object with a plain
  enum field.** Witness reconstruction rebuilds a nominal object via a real
  `nnkObjConstr`, and an enum-typed field's reader is `readUInt8`/
  `readUInt16` (there is no dedicated enum reader), producing a value Nim
  will not implicitly convert to the enum type. A compile failure, not a
  degrade — strictly worse than `sxUnknown`, and it predates this branch
  (independent of `hasRange`). Lives in `symex.nim`, so it was out of the
  agent's scope; the field route was verified via a compile-time
  `classifyFieldType` probe instead.
- **`c > 'literal'` on ANY char-range value hits an `nnkHiddenSubConv` gap**
  in `dsl_parser.nim` → `feUnsupportedExprKind`, for the inline spelling as
  well as the alias. This blunts W3: the alias now classifies correctly, but
  the most natural thing to write about a char range still does not parse.
  The W3 tests use `ord(c) > ord('m')` to sidestep it via the existing
  `ord`-as-identity case. W3 is still worth having (it stops a whole-run
  degrade) but it does not make char ranges usable on its own.

### Sweep gate — half done, deliberately

Baseline at `ac507c1` COMPLETE: `/home/corey/.claude/jobs/4fd5573d/tmp/base163.log`,
460 entries, from a worktree with `_deps`/`nim.cfg` copied in. The current
side was started and then **killed on purpose** — `sweep.sh` compiles
per-test as it runs, so editing `src/` mid-sweep contaminates the log (the
trap #161 recorded). Re-run the current side ONCE against the final tree:

```
/home/corey/.claude/jobs/4fd5573d/tmp/base163   # pinned worktree, keep it
scripts/sweep.sh <tmp>/cur163final.log && scripts/sweep-diff.sh <tmp>/base163.log <tmp>/cur163final.log
```

### Consolidated audit ledger — 13 findings, none fixed

Covers all three issues (the branch is combined, so the audit was too).
Ranked by blast radius of the GAP, not size of the fix. Every row's default
disposition is **wire it**; there are no deletion candidates in the set.

| # | Kind | Finding | Anchor |
|---|---|---|---|
| **W1** | 6 unreachable-by-default | **Nothing was ever pushed.** `origin` has no `rfc-16*` branch; 27 commits unpushed; newest CI run on any branch is the v0.8.0 release, nine days before these commits. All three handoffs declare the `rfc-*` naming exists so `symex-mingw` verifies seven walker bumps — that verification has never run. VERIFIED by me. | `git branch -r`; `.github/workflows/symex-mingw.yaml:118` |
| **W2** | 2 + 7 | **`seq[range[lo..hi]]` elements never receive their bounds.** `ty.hasRange`'s entire runtime consumer set is ONE site. Seq data is a Z3 array via `allocateSeqDataRaw`; elements never reach that arm, and the `isIndex` read lifts without consulting `seqElemTy.hasRange`. False-SAT plus the slice-5 witness-`RangeDefect` crash class, one container over. Directly falsifies this repo's own written claim that seq elements "inherit the constraint through `allocateSym`'s existing recursion". Arrays genuinely do inherit it. | `runtime.nim:2343` (sole consumer) vs `:2452`, `:9284`, `:6863`; claim at `dsl_typebridge.nim:58`, `docs/issue-0162-…:226` |
| **W3** | 2 | **`type Letter = range['a'..'z']` degrades the WHOLE run.** The alias arm guards both bounds `kind in nnkIntLit..nnkUInt64Lit`; `nnkCharLit` is outside it, so the alias falls to `feUnsupportedParamType` → whole-run `sxUnknown`. The inline spelling has no kind guard and works. Exactly the one-route-fixed-one-route-forgotten shape #162 slice 3 existed to kill. VERIFIED by me. | `dsl_typebridge.nim:568` vs `:484` |
| **W4** | 2 + 7 | **Range-typed fields of a `ref object` drop their bounds.** Heap-modelled fields are materialised by `heapSelect` at deref, never by `allocateSym`'s recursion; no heap reader consults `hasRange`. Every slice-5 test uses a plain VALUE object, so the "object field route is covered" row is true of only half the route. | `runtime.nim:2182` / `runtime_heap.nim` vs `docs/issue-0162-…:185` |
| **W5** | 5 | **The `{.symexTransparent.}` soundness story is unpinned.** The expression-position fallback is the whole "over-claimed pragma costs precision, never soundness" argument; delete that disjunct and a used-result transparent callee body-walks into the G3fix `KeyError` shape with NO red test. The public pragma has no test consumer at all — everything green exercises coverage.nim's private copy. | `dsl_parser.nim:3969`, `symex.nim:1103` |
| **W6** | 4 producer-less consumer | **Range-typed variant discriminator + `else:` arm.** Both disc-domain builders cover else-arm ordinals by fanning out over `vDiscTags`, which the non-enum route never populates — so with an `else:` present the disc is pinned to the explicit `of N:` literals and every else path is falsely unreachable, in both modes. | `runtime.nim:2244`, `:12587` vs `dsl_typebridge.nim:304` |
| **W7** | 6 | **Plain enum params/fields get no domain constraint**, declined for a reason #162 itself retired (the guard is signedness-based now). Out-of-domain ordinals are model-reachable; variant discriminators get their disjunction, plain enum values get nothing. VERIFIED by me. | `dsl_typebridge.nim:578` vs `runtime.nim:12648`, `:12652` |
| **W8** | 2 | The two isIntOffset allocation arms ignore `ty.hasRange` that the parameter arm deliberately rescues. | `runtime.nim:12711` vs `:2323`, `:2374` |
| **W9** | 2 | Overflow-obligation dispatch keys on the LEFT operand's stamp only, so `s.len * x` with a stamped `x` raises no obligation. Pre-existing, but it is a hole in the very invariant #161 declares. | `runtime.nim:4690`, `:4694` |
| **W10** | 2 | **The concolic path never drains the degrade sink.** Two top-level `walk()` drivers; `runConcolicCollectImpl` reads neither `w.walkDegradeErrors` nor `w.sawUnknown`. Slice 3's property holds on `symexFind`, not on `concolicFlip`. Diagnostics, not soundness. | `runtime.nim:10159` vs `:13329` |
| **W11** | 2 | 88 test files unregistered (83 `tsymex_*`), including `tsymex_phase16_R16_4_overflow`, `R16_5_overflow_thru_closure`, `R16_2_rangedefect` — the pre-existing pins most adjacent to what #161/#162 changed. They run in no CI leg. | `nelli.nimble` vs `tests/` |
| **W12** | 7 | Version floors: #161 and #162 compare version STRINGS (false red at "1000"); #163 uses `parseInt`. #161 pins `>= "126"` but contains tests needing 127 and 128. All are `>=` (correct); the CR2 `==` pin is correct. | `tsymex_161_…:179`, `tsymex_162_…:191` |
| **W13** | 7 | Ledger/comment truth: three test headers still call `recordEdge`/`logCmp` `{.symexOpaque.}` and say their calls "become `mkOpaqueCall`" (both false since #163 slice 1); the CR2 file's running ledger skipped five of seven bumps (the pin VALUE discipline held, the narrative didn't); #162's "15/15" predates slice 5's 21 tests; #161's follow-up 5 was fixed by #163 on this branch with no note; #163's own "Gates run" table presents the sweep row as a result when it is still open. | `tsymex_g3fix_walkergap.nim:10`, `tsymex_g4_cmpwalk.nim:3`, `tfuzzcmplog.nim:7`, `tsymex_phase15_CR2_cachekey.nim:732` |

**Verified clean, so nobody re-audits it:** both new cache-key chains are
closed end-to-end (`IRType` bounds and `opaqueInert`, producer → emit
round-trip → consumer → canonical form); `feOpaqueCallUnmodelled` is
genuinely emitted; all seven walker bumps carry real recorded reasons;
`emitIRType` is total (the one unthreaded field has a current, accurate
justification); `IRType.==`'s deliberate exclusion was checked against every
memoisation consumer and bites none; `RawResult.obligations` is genuinely
consumed, not dormant; the `mul32` trip-wire is genuinely retired; no error
kind documented as emitted has silently stopped; `opaque: true` is
constructed in exactly one place; no inertness verdict is wrong across the
whole `OpaqueEffectfulProcs` catalog; #163 slice 1's no-bump argument holds
for every in-repo consumer.

### Lens A findings — detail

| # | Kind | Finding |
|---|---|---|
| F1 | partial consumer set | `feOpaqueCallUnmodelled` is pushed mode-independently (`runtime.nim:10159`) but only ONE of the two top-level `walk()` drivers drains it. `runConcolicCollectImpl` (`runtime.nim:13329`) reads neither `w.walkDegradeErrors` nor `w.sawUnknown`, so slice 3's property holds on `symexFind` and not on `concolicFlip`. Diagnostics, not soundness (Track E re-verifies concretely). Wire: surface a taint counter through `ConcolicYieldCounters`, beside `ambiguousBranches`, which already rides that channel. |
| F3 | consumer-less producer | The expression-position fallback (`dsl_parser.nim:3969`) is the whole "an over-claimed pragma costs precision, never soundness" argument — and NOTHING pins it. Delete that disjunct and a used-result transparent callee falls through to body-walking (the G3fix `KeyError` shape) with no red test. The public `symexTransparent*` (`symex.nim:1103`) likewise has no test consumer; everything green exercises only `coverage.nim`'s private copy via `{.cover.}`. |
| F2 | regressed claim | Three test headers still assert `recordEdge`/`logCmp` are `{.symexOpaque.}` and that their calls "become `mkOpaqueCall`" — both false since slice 1: `tsymex_g3fix_walkergap.nim:10`, `tsymex_g4_cmpwalk.nim:3`, `tfuzzcmplog.nim:7`. Tests still pass (a drop is strictly stronger than opacity), but this handoff leans on the g3fix pin as the proof no route regressed, and its header now describes a mechanism never engaged. Comment-only fix. |
| F4 | confirmed, pre-existing | The `maxCallDepth` bail (`runtime.nim:10236`) still sets `w.sawUnknown` bare — the exact shape slice 3 fixed for the opaque arm. Already in "Surfaced, not fixed here"; confirmed still true at this tree. |

### Two corrections to earlier claims in this doc's own lineage

- There is only ONE `runSymexImpl` — the line earlier believed to be a second
  overload is a forward declaration.
- `mkOpaqueCall`'s omission of `retIntOffsetPositions` from `emitStmt` is
  correct **by construction**, not a silent round-trip drop: only the
  `mkCall` producer computes `calleeIntOffsetReturnPositions`, and an opaque
  callee's body is never analysed, so the closed-form proof cannot exist.

Lens A also cleared the third-route question (`opaque: true` is constructed
in exactly one place, `types.nim:3006`, with exactly the two parser call
sites plus `emitStmt`'s preserve-only round-trip) and found no case where
inertness is wrong across the whole `OpaqueEffectfulProcs` catalog
(`echo`/`print`/`writeFile`/`sleep` become inert; the rest are excluded by
`ntyPtr`/`distinct` handles).

## Resume command

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -6 rfc-161-163-symex-defects
tail -40 /home/corey/.claude/jobs/4fd5573d/tmp/gate163.out     # sweep gate
```

Next actions, in order:

1. Collect the four remediation agents; verify each RED-before-GREEN claim.
2. Wave 2 in `runtime.nim`: W6 (variant-disc else arm), W8 (isIntOffset
   arms), W9 (obligation operand stamp), W10 (concolic drain).
3. Land the single walker bump **132→133**, updating the CR2 pin value, and
   raise the #163 floor pin accordingly.
4. Re-run the current-side sweep against the final tree and diff against
   the completed `base163.log`.
5. Read the three Windows legs.
6. Only then `/code-review`; and set `wiring = proven` only if wave 2 and
   the gates come back clean.
