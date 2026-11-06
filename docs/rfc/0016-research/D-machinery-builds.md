# Lens D — the soundness machinery and build sensitivity (RFC-0016 work-list research)

Snapshot: `83c1d304` (walker 272). Read-only scratchpad `scratchpad/research`; probes ran on eos
`~/nelli/wt-rsD` (same sha, `scripts/dt-bounded.sh c`, Z3 from milpa CAS `9a033beb…`, PCRE per image).
Every claim is tagged `read` (code read, cited) or `ran` (probe executed, output quoted).
Paths: bare `runtime.nim`, `types.nim`, `dsl_parser.nim`, `canonicalize.nim`, `check_options.nim`,
`replayproc.nim`, `soundness.nim` mean `src/nelli/smt/…`; `symex.nim` is `src/nelli/symex.nim`.

Scope reminder: this lens is the cross-cutting machinery (how taint is attached, carried, merged,
cached, and how the build the SUT runs on is read), not per-construct models. Where a finding
touches a construct it is named only as the minimal SUT that exercises the mechanism.

---

## 1. Taint-preservation table

The lattice (`soundness.nim:67-110`): per-path `Path.taint` is written only at degrade sites through
a `Degrade` token; the run coordinate is *derived* at drain from the error sinks (`types.nim:3678
runTaintOf`, severity rule `taintsRun` at `:3667`). `trusted()` (`types.nim:3741-3749`) reads
`trustedSat` (clean path or `rsConfirmed`) and `trustedUnsat` (`scIncomplete notin runTaint`).

| # | Mechanism | Preserves taint? | Evidence (file:line) | Pin test |
|---|---|---|---|---|
| T1 | Ordinary fork (`forkPath`) | yes — propagates `parent.taint`; the primitive `forkPathTaintPrimitive` is reachable only through three wrappers | `runtime.nim:871-935` | `tsymex_rfc0005_s1_lattice` (writer grep-pin) |
| T2 | Degrade fork (`forkPathTainted`) | yes — join `parent.taint + d.path`, never replace | `runtime.nim:910-919` | s1_lattice |
| T3 | Return merge (`forkPathMerged`) | yes — `callee.taint + caller.taint`, plus `nilDeref` or | `runtime.nim:921-935` | s1_lattice |
| T4 | Raw `Path(...)` constructions | yes — only `initialWalkPath` (drains parameter set-up taint, `:16681-16697`), the S1 test probes (`:1005-1019`, `:16794-16822`, `:25627`) and the closure `descentBase` (`:26604`, starts at `{}` by design and is re-joined with the caller's taint at the merge, T3; the call's pending decline is carried by `carriedDegrade` `:16674`) | `runtime.nim` grep `Path(pc` | review R2-01 (`tsymex_rfc0005_r2_walktaint`) |
| T5 | `degrade()` funnel: one call records + returns the token | yes by construction; **but** the token can be `discard`ed. 20 `discard w.degrade(` sites; 3 are S1 test probes, 17 are halts that return `@[]`/`continue` (so the path has no survivor and the run record suffices). Audited: `:16736` leak pin, `:19172` closure-raise fault, `:20253` finally-jump, `:21150` frontier prune, `:22852` variant-on-declined-ctor (`continue`), `:24041/:24057` break/continue outside loop, `:24091` finally-return, `:24246/:25891/:25949` solver undef, `:24301/:24312` bare raise, `:24537` unsafe cast, `:25922` nil-deref-under-setjmp (`return`), `:27037` closure diverged (no continuation, exit-coverage fact `false`), `runtime_heap.nim:1360` depth exhausted (`return true`, caller drops). All consistent with their `classOf` row (`dcOmitted`/`dcNoAnswer`) | `runtime.nim:16613-16670` | `tsymex_rfc0005_s6a_budget` pins the prune only; no pin that every `discard`ed token is a halt (see §6) |
| T6 | Lowering sink (`lowerDegrade` → `loweringPendingTaint` threadvar → `drainPendingLowerEffects`/`lowerInExpr`/`initialWalkPath`), leak pin at walk end | yes; a residue at walk end is stamped `weInternalWalkerFault` (whole run ⊤) | `runtime.nim:16660-16740` | s1_lattice, `r2_walktaint` (R2-01, R3-10) |
| T7 | Closure sink (`closureDegrade`) | yes — joins `loweringPendingTaint` | `runtime.nim:16699-16720` | `tsymex_rfc0005_s7_closure` |
| T8 | Short-circuit join (`mergeJoinPaths`) | yes — declines the join (returns the paths unmerged) if any survivor's taint differs from the skip path's | `runtime.nim:20619-20672` | S8w/S8aa tests |
| T9 | Call-cache summary (`CallCacheEntry`) | yes — a summary is stored only when every exit path has `cp.taint == {}`, no escaped raise, no `var` formal, no guarded outer, heap unchanged, same defect-survivor facts; the hit forks with `forkPath` so the *caller's* taint rides; context-dependent drops are re-checked (`pruneFactsHold`). A callee path dropped by a halt during the first walk is recorded on the run once; the hit replays the same survivors | `runtime.nim:16578-16611` (type), `:23274-23292` (hit), `:23600-23640` (store) | S8ax/S8be tests |
| T10 | Loop unroll exit (`maxLoopUnwind`) | yes — survivors forked with `beBudgetExhausted`/`…AssumedBound` (`dcFabricated`: ⊤ path, `{scIncomplete}` run) in both explore and concrete modes | `runtime.nim:20944-20961`, `:23979-24031` | `tsymex_rfc0005_s6a_budget`, `tsymex_r6_n20_boundedloop` |
| T11 | Frontier prune (`maxFrontierSize`) | yes — halt, `beBudgetExhaustedPrune` (`dcOmitted`, run `{scIncomplete}`); evicts tainted paths first | `runtime.nim:21128-21155` | s6a_budget |
| T12 | Call-depth / recursion caps | yes — `weRecursionCycleCut` survivors are `forkPathTainted` (`:23262-23268`); `maxRecursionDepth`/native stack set `rdNativeStack` and an `sxUnknown` with it is not cached (`symex.nim:736-746`) | `runtime.nim:23262`, `:28395` | S8ax, S8ca tests |
| T13 | Halted paths generally | yes for the *run* coordinate (every halt records a `sevError`); the path coordinate is `{}` because no survivor exists. **Sound only while the halt really drops the path** (T5) | `types.nim:3643-3660` (`pathTaint(dcOmitted) = {}`) | none generic |
| T14 | Parse-time anchored declines never reached (S9 `reachJoinParseErrors`) | preserved when reached; **downgraded to `sevHint` when no walked path reached the marker**. Sound because a Class-A decline is a marker *in the IR* (`declineAtSite` `dsl_parser.nim:1411-1421`) and a marker that did not survive into the emitted program is rescoped `dskUnplaced` and kept (`:21864-21867`). Safe as long as nothing substitutes a value *and* emits no marker — that invariant is pinned ("Nothing else writes ctx.parseErrors") | `runtime.nim:28630-28653` | S8/S9 totality pins |
| T15 | Exception routing across try/except/finally | caught entries are stamped by park serial (R3-01/R3-02 fix); `finally` on a raised exit with `return`/`break`/`continue` halts (`eeFinally*`, `dcOmitted`); a bare `raise` outside a handler halts. The backend difference (c re-raises, cpp does not) is a decline, not a model | `runtime.nim:20253`, `:24091`, `:24301-24315`; `smt/exits.nim` | `r2_walktaint` (`handlerInnerTry`) |
| T16 | Walker fault (`weInternalWalkerFault`), Z3 error, lost Z3 API error | whole run `sxUnknown` (`dcNoAnswer`); a found `sxSat` is *not* returned after a fault (the catch replaces the result) | `runtime.nim:28280-28340`, `:28349-28366` | S8m |
| T17 | First-`sxSat` stop (`shouldStop`) | the walk stops at the first `sxSat` (or first `sxRaised` for raise targets); if that candidate is later refuted by replay the run is `sxUnknown`, never promoted — sound, precision cost (the remaining frontier is never walked) | `runtime.nim:17308-17318` | S10 settle tests |
| T18 | Run boundary promotion | an `rsUnsettled` record is promoted to `rsNotNeeded` only for `sxUnsat`/`sxUnknown` or a winner with no `scSpurious` (R2-11) | `runtime.nim:28373-28383` | `r1_rundependence` |
| T19 | Replay settle | `rsConfirmed` only on `roConfirmed`; refuted/inconclusive candidates leave `sxUnknown`; `witnessUnsafe`, `runDependence` carried on the record; zero `ReplayResult` is `reRefused/roDeclined` (R3-04) | `replayresult.nim`, `symex.nim:3230-3420` | `w2_settle`, `r1_replaychild` |
| T20 | Verdict cache save/load | soundness is encoded on the sentinel (`encodeSoundness`, 5-6 single-digit fields, ordinals statically pinned) and *load-bearing*: a sentinel without it is a miss; an `sxUnknown` with any `runDependence` is not saved; a claim whose `witnessUnsafe`/`rsUnconfirmed` may be the run's (`rdReplay`) is not saved (`cacheable`) | `symex.nim:345-370`, `:683-746`, `:772-793`, `soundness.nim:150-170` | `r1_findingapi`, `r1_rundependence`, `phase15_E2a_cascade` |
| T21 | `assertCoveredBy` / `symexForAll` | act on `trusted()`; a `witnessUnsafe` claim is not splatted/seeded. **Gap (INT-22):** a clean faithful winner is never replayed, so a witness that ends the process after the target is run in the host; the splat catches only `AssertionDefect`, `IndexDefect`, `FieldDefect`, `NilAccessDefect`, `CatchableError` (`symex.nim:4104-4118`) — an `OverflowDefect`/`DivByZeroDefect`/`RangeDefect` witness kills the test process | `symex.nim:4057-4120`, `:982` | `r1_findingapi` |
| T22 | `eeUnknownExnType` (unknown exception type in an `except`) | recorded at `sevWarning` but counted by `taintsRun`'s carve-out | `types.nim:3667-3676` | S6b |
| T23 | `sevHint` records (`heFreshnessCapExceeded`, `hePtrFamily`, `geDistinctBijectivitySkipped`, `eeUninterpRefExtraction`) | by design verdict-neutral; `eeUninterpRefExtraction` is a *witness* extraction hint on `getCurrentException()` fields — the lossy-witness path (`wfLossy` → `rsUnconfirmed`) must own it; not re-verified here | `runtime.nim:11506`, `runtime_heap.nim:171,4157…` | none specific |

Verdict on §1: with the sites above, no path merge, fork, cache hit, loop exit, prune, halt, replay
or cache load loses taint by *mechanism*. Every remaining way to a wrong verdict is a **model that is
wrong while clean** (no degrade emitted at all) — the same class as the five Criticals. §2–§4 are
where those come from.

---

## 2. Catch-all inventory

Counts (`read`, grep over the parser and walker; exact regexes in the lens notes):

| File | `else: discard` | `else:` (any) | `else: nil` / `@[]` / `()` | bare `except:` | `except CatchableError/Exception/Defect` |
|---|---|---|---|---|---|
| `dsl_parser.nim` | 20 | 240 | 36 | 1 | 11 |
| `runtime.nim` | 16 | 274 | 5 | 0 | 9 |
| `runtime_heap.nim` | 9 | 53 | 1 | 0 | 1 |
| `runtime_strings.nim` | 1 | 20 | 0 | 0 | 1 |
| `runtime_closures.nim` | 0 | 3 | 1 | 0 | 0 |
| `runtime_floats.nim` | 1 | 9 | 0 | 0 | 0 |
| `dsl_typebridge.nim` | 1 | 18 | 3 | 0 | 0 |

The 47 `else: discard` sites were each read in context. Classification:

| Site | What it maps to | Dangerous? Why |
|---|---|---|
| `dsl_parser.nim:16574-16600 nodeWritesHeap` (S8cn: "writes through a `ptr`/`ref`, or calls a routine that does") | unknown node kind → recurse children → `false` | **yes (fail-open analysis predicate).** Only `nnkAsgn/nnkFastAsgn/nnkHiddenAddr` and calls are writes. Not seen: `nnkAsmStmt`, `{.emit.}` (`nnkPragma`), `nnkCast` (all three are handled by the *other* scanner `scanOpaqueEffects` `:3861-3890`, not here), and a non-user routine with a `var` formal fed a dereference (`inc(p[])`, `swap(p[], x)`, `setLen(p[], n)`: the arg's `typeKind` is the pointee's, not `ntyPtr`, so `:16596` says no). Consumer: the S8cn `let`-cursor / lent-loop decline (`:16650-16653`), i.e. a decline that is *not* emitted → clean path |
| `dsl_parser.nim:22418-22460 routeStoresThroughDeref` (S8cs route) | unknown → recurse → `false` | **moderate.** Same shape; it *does* treat any non-user call as "may store" when an argument holds a pointer, and a non-sym head as `true`, so the hole is narrower: a write expressed by a node that is neither asgn/addr/call (`nnkAsmStmt`, `nnkPragma emit`) |
| `dsl_parser.nim:22505-22540 check` (hook copy-field proof, S8cs) | unknown → recurse → `true` (field copied) | **moderate.** `result = true` default: a hook body that moves the field by a construct other than `nnkAsgn` (a `swap`, a `move`, `copyMem`) proves "copied" for free |
| `dsl_parser.nim:6546-6584 ptrUsesStayLocal` | unknown → recurse | moderate: "uses stay local" default `true` after the case; escape via `nnkAsmStmt`/`emit`/`cast` unseen |
| `dsl_parser.nim:2032-2541 irVars` (IR reads/defined collector) | unknown IR stmt kind → no vars | moderate: feeds alias guards; an IR kind added later without a row silently reads nothing |
| `dsl_parser.nim:9583-9586` (`potentialWrites` collector `pfAdd`) | `nnkTypeSection/TypeDef/Pragma/CommentStmt` → return; else recurse | low: an `emit` pragma inside the scanned body is *skipped* (`nnkPragma → return`) — check that the caller's other scanner covers it |
| `dsl_parser.nim:14704-14707`, `:16487-16522 mentionsSym`, `:2946`, `:3113`, `:3569`, `:5741`, `:11638`, `:11889`, `:16071`, `:21864`, `:22204`, `:22220` | structural helpers; else → "no match" | low: each is a shape matcher whose caller declines on no-match (`:11889 ensureMove` falls through to the generic call path) |
| `runtime.nim:2986-2999 svWithRaw` | kind not scalar/string → **returns `sv` unchanged** (the new term is silently dropped) | **yes if reached with a seq/tuple/ref:** the only caller is the loop-arm alternative at `:15838` (S8bz item 3, scalar or string by contract). A future caller with a composite value gets the stale value with no record. Make it `doAssert`/decline |
| `runtime.nim:17408-17430 groundedLike` | kind mismatch → `sym` | low (precision only: a grounded leaf is an optimisation) |
| `runtime.nim:21020-21049 bindsViewWhole` | unknown stmt kind → `false` | moderate (fail-open view guard, S8cn): a view bound by an `isCall` with a view argument or an `isAsgn` is "not bound" |
| `runtime.nim:11257-11261`, `:11665-11669`, `:12016-12020` (witness extraction / render) | unknown kind → nothing extracted | low *if* the lossy-witness channel sees it (`feExtractionFailed`/`wfLossy` → `rsUnconfirmed`); not re-verified |
| `runtime.nim:6022`, `:9273` (Z3 AST walks), `:5835`, `:8597` (interval), `:15548`, `:15839`, `:18350 armHeavy`, `:27236`, `:2983 stampHeapSteps`, `:6210` | bookkeeping / budget heuristics | low |
| `runtime_heap.nim:308/347/593/639/1693/1751/2602/3512/3982` | variant/heap plumbing; `:1693 locGet` else → none → caller declines; `:3512 tabValueOf` else → falls through to the 64-bit cell path | low-moderate: `:3512` reads any non-string/float pointee through the int2bv cell path (`itInt` of width ≠ 64, `itBool`, enums) — correct only if `ptrTabCellRead` handles the width |
| `runtime_strings.nim:365`, `runtime_floats.nim:96` | string/float op dispatch; else → continue to the generic decline | low |
| `symex.nim:2649 isThreadvarSym`, `:2732 isImportedVar` | `getImpl` raises → `false` ("not a threadvar", "not imported") | **moderate (fail-open at macro time):** an `importc` global whose impl cannot be read is treated as program storage; the replay footprint and the S8bo threadvar decline both read these |
| `symex.nim:4104-4118` splat catches | 4 Defects + `CatchableError` | see T21: `OverflowDefect`, `DivByZeroDefect`, `RangeDefect`, `ObjectConversionDefect`, `FloatingPointDefect` escape and kill the host |
| `runtime.nim:28280-28340` run-boundary catch-alls | `CatchableError`, `Defect` → `weInternalWalkerFault` → `sxUnknown` | **safe (fail-closed)** |
| `check_options.nim` "fails closed" rules (unread file, undecided `when`, non-literal value, unplaceable position → check *off*) | decline | safe |

Dangerous count: 3 clear (`nodeWritesHeap`, `svWithRaw`, hook-copy `check` default-true), 5 moderate.
The pattern is one: **a syntactic predicate that proves "no write / no escape / copied" by
enumerating the node kinds that write and defaulting to the safe-looking answer for the rest.**
That is a denylist, and RFC-0016 §2.1 asks for allowlists.

---

## 3. Build matrix

What the walker *reads* about the build (`read`; `grep compileOption|defined|querySetting` over
`src/nelli/smt` and `symex.nim`):

- `check_options.nim:106-121` `commandLineChecks` (field/overflow/range/bound/obj/nan/inf/assertions)
  plus the per-routine source scan of `{.push.}`/`{.pop.}` — **read at nelli's own compilation**.
- `canonicalize.nim:6548-6604` cache-key segment `|bf=`: checks on, `danger`, `release`, `mm`,
  backend, `--exceptions`, `--threads`, `--stackTrace`, `--lineTrace`; `|rm=`: fork/reexec/none and
  `+panics`; `|pcre=` engine+version; `|z3=`; `|nim=`; `|w=` walker 272.
- `runtime.nim:25916` `when compileOption("exceptions","setjmp")` (nil deref under `try`).
- `dsl_parser.nim:5282`, `:17376` `defined(gcArc|gcOrc|gcAtomicArc)` (argument temporaries; move = zeroing vs havoc).
- `dsl_parser.nim:18386`, `:18996` `compileOption("assertions")` for a *stdlib iterator's* assert; a
  user `assert` is faithful by construction (it is gone from the typed AST when off; `doAssert` stays).
- `symex.nim:2343` `defined(nimPanics)` — **replay only** (`replayInScope` returns false).
- `dsl_typebridge.nim:1787-1798`: `int`/`uint`/`Natural`/`Positive` → **hard-coded 64 bits**.

| Setting | Walker reads it? | Native can diverge silently? | Evidence | Existing row |
|---|---|---|---|---|
| `--overflowChecks/rangeChecks/boundChecks/fieldChecks/objChecks:off` (cmd line or `{.push.}`) | yes: source scan → `feCheckOption` decline for the routine | no, **except** the overflow marker is skipped untainted when the settings model the wrap (`runtime.nim:24500-24502`): then unchecked signed arithmetic is modelled as 2's-complement wrap, which C does not promise (`ran`, D-02/D-03) | `check_options.nim`; `runtime.nim:24495-24510` | PRC-07, PRC-08, PND-11 |
| `--nanChecks/--infChecks:on`, `--floatChecks:on` | yes → decline (`deviation` includes `maybeOn * defaultOff`) | no | `check_options.nim:123-125` | PRC-07 |
| `--assertions:off`, `-d:danger` for `assert` | typed AST already has no `assert`; `doAssert` kept | no | `dsl_parser.nim:4567` | — |
| `-d:danger` | key + every routine declines (all defaults off) | no (declines everything) | `check_options.nim:106-121` | PRC-08 |
| `-d:release` / `--opt:speed|size` | `release` keyed; `--opt` **not keyed, not read** | **yes together with any unchecked arithmetic**: the optimiser's UB folding changes control flow (`ran`, D-02) | `canonicalize.nim:6596-6613` | INT-31 (`--opt` unkeyed) |
| `--passC:-fwrapv / -ffast-math / -ftrapv`, `--cc:` | **not read, not keyed** | yes: `-fwrapv` makes D-02's wrap real; `-ffast-math` changes float semantics the walker models exactly (IEEE) | — | INT-31 (`--cc`) |
| `--panics:on` | key (`+panics`) and `replayInScope` only; **the walker's `except Defect` model is unchanged** | **yes — confirmed** (`ran`, D-01): clean trusted `sxSat` for a label in `except DivByZeroDefect`/`except Defect`/`finally` after a defect, and clean `sxRaised` for a Defect the process dies on instead | `symex.nim:2343`; `runtime.nim` try arms do not consult it | INT-27 (precision only) — the soundness half is **new** |
| `--mm:refc` / `markAndSweep` / `boehm` / `go` / `none` | keyed only | **n/a — nelli/symex does not compile under `--mm:refc`** (`ran`: nim-z3 `src/z3/ast.nim(63)` "signature for '=destroy' must be proc[T: object](x: var T)"); a consumer on refc gets a compile stop, not a decline. The mm-gated arms (`dsl_parser.nim:5282`, `:17376`) take the havoc branch there and are unreachable in practice | probe `p_refc` | none |
| `--mm:arc` vs `orc` | keyed; cycle collection differences not modelled (`=trace`, INT-11) | low (no cycle-dependent verdict found) | — | INT-11 |
| `--exceptions:goto` (default) vs `setjmp` vs `cpp` | keyed; `setjmp` read for nil deref under `try`; cpp-vs-c `finally` difference declines | `setjmp` on Windows crashes the fiber (INT-12); `--exceptions:cpp` on the c backend is a compile error, n/a | `runtime.nim:25916`, `:20253`, `:24091` | INT-12 |
| c vs cpp backend | keyed; no walker read | known: `finally` re-raise differences are declines; cpp spend drift (INT-04) | — | CI-02, INT-04 |
| `--cpu:i386` / 32-bit `int` | **not read, not keyed**; `int` is BV64 | **yes by reading:** `OverflowDefect` at 2^31, `high(int)` witnesses that do not exist, `sizeof(int)`/pointer-cell widths; no 32-bit toolchain to run (declined to probe) | `dsl_typebridge.nim:1787-1798` | INT-31 (`--cpu`) |
| Windows (`int` 64, `clong` 32) | `clong`/`cint` resolve through `getTypeImpl` per target; `defined(windows)` only in replay/PCRE | no evidence of divergence; PRC-01/02 are replay declines | `dsl_typebridge.nim` (no `clong` special case) | PRC-01, PRC-02 |
| `--threads:on/off` | keyed | no (threadvar sinks are per thread either way) | `canonicalize.nim:6601` | — |
| Z3 4.13.4 vs 5.1 | `z3FullVersion()` keyed; version-gated ops decline (`seZ3VersionMissing`, `dcFreshSymbol` + replay gate) | rlimit spend differs (PRC-27, PRC-32, INT-04) — budgets decline, never truncate | `runtime.nim:9885-9901` | PRC-27, PRC-32, PND-09, PND-10 |
| PCRE build (JIT, version) | keyed (`pcreEngineName`) and `VerifiedLib` list | unverified builds decline (S8bt) | `pcre_engine.nim:129-141` | PND-01, PND-02, INT-19 |
| `-d:useMalloc` | not read | replay OOM hook not reached (INT-23) | `replayproc.nim:145,328` | INT-23 |
| `-d:nimOldCaseObjects`, `--experimental:strictCaseObjects` | not read, not keyed | changes whether a discriminator reassignment is a `FieldDefect` at run time; the walker models the 2.x default; **unprobed** | — | none |
| `{.push.}` inside `fn` itself | invisible to `|bf=`; covered by the `feCheckOption` decline **unless** the wrap setting skips it (D-02) | see above | `canonicalize.nim:6552-6556` | INT-31 |
| Host runtime hooks (`globalRaiseHook`, `outOfMemHook`, …; `setControlCHook`) | replay declines when set, except `setControlCHook` | replay only | `replayproc.nim` | INT-13, INT-15 |

---

## 4. Defect table

`DefectKind` (`types.nim`): `dkAssertionDefect dkDivByZeroDefect dkFieldDefect dkIndexDefect dkOverflowDefect dkRangeDefect dkOutOfMemoryDefect dkStackOverflowDefect dkOther`. Default `defectExclusions = {dkOutOfMemoryDefect, dkStackOverflowDefect}` (`types.nim:3192`). The hierarchy table (`exn_hierarchy.nim`) is pinned against `system.nim`; a user `object of Defect` is resolved through `userExnHierarchy` (`ran`: `Boom of Defect` is **not** caught by `except CatchableError`, `pSoftDefect of CatchableError` is — faithful).

| Defect | Modelled as a raise fork? | Where | `sxRaised` correctness | Note |
|---|---|---|---|---|
| `IndexDefect` | yes (seq/string/array/openArray index, slices; `symexSliceNoOobFork` define can disable the slice fork) | `runtime.nim` 9 sites; `:9793-9799` | correct under default build; **under `--panics:on` it is a process exit, reported as a catchable raise** (D-01) | |
| `OverflowDefect` | yes (`acOverflow`), incl. `succ/pred` since R1-02 | `types.nim:2880`; parser `:12583` | correct with checks on; wrap mode is C UB (D-02, D-03) | `-low(int)`, `abs(low(int))`, `low(int) div -1`: see D-03 |
| `DivByZeroDefect` | yes (`acDivByZero`) | `types.nim:2881` | same panics caveat | AUD-02: off-with-overflow-on leaves the zero divisor unconstrained |
| `RangeDefect` | yes (`acRange`, conversions, negative `setLen`) | parser 4, walker 3 sites | same | |
| `FieldDefect` | yes (variant read; discriminator assignment) | walker 8 sites | same | `nimOldCaseObjects` unprobed |
| `NilAccessDefect` | **not a raise**: an uncatchable crash routed through frame exits (`crash: true`), finding at the SUT boundary; declines under `setjmp`+`try` | `runtime.nim:25905-25940` | correct for goto builds (S8cu); replay never runs it | AUD-10 closed |
| `AssertionDefect` | yes (`symexAssert`, user `assert`/`doAssert` via `failedAssertImpl`) | parser `:4567` | correct; `--assertions:off` faithful by construction | |
| `ObjectConversionDefect` | yes (`mkRaise("ObjectConversionDefect")` on a checked downcast) | parser `:10488` | not natively pinned in this lens | `--objChecks:off` declines |
| `FloatDivByZeroDefect`, `FloatOverflowDefect`, `FloatInvalidOpDefect`, `FloatUnderflowDefect`, `FloatInexactDefect` | **no** — off by default natively; a build with `nanChecks`/`infChecks` on declines the routine | `check_options.nim`, parser `:4158-4159` | n/a (decline) | |
| `KeyError` (CatchableError) | yes (Table `[]` on a missing key) | `runtime.nim:21492` | | |
| `ReraiseDefect` | no — bare `raise` with nothing in flight halts the path (`eeHandlerReraiseUnmodelled`) | `runtime.nim:24312` | n/a (decline) | |
| `AccessViolationDefect` / SIGSEGV (raw `ptr`) | no — `heUnsafeCast` halt; nil deref as above | `runtime.nim:24537` | n/a | |
| `StackOverflowDefect` | excluded by default; deep recursion is `maxRecursionDepth` → `rdNativeStack` decline | `types.nim:3192` | n/a | |
| `OutOfMemDefect` | excluded by default | | n/a | INT-23 for replay |
| `DeadThreadDefect`, `ObjectAssignmentDefect` | not modelled, no construct reaches them | | n/a | |
| Any Defect under `--panics:on` | **modelled as catchable** | all try arms | **wrong**: D-01 | |

---

## 5. Findings

| ID | Item | Class | Minimal SUT | Evidence | Suggested pin | Effort |
|---|---|---|---|---|---|---|
| **D-01** | **`--panics:on`: the walker models every Defect as a catchable exception.** A label inside `except DivByZeroDefect`, `except Defect`, or a `finally` entered on a defect gets a clean trusted `sxSat` (`rsNotNeeded`, no replay: clean path), and a Defect target gets a clean `sxRaised`; natively the process ends (`Error: unhandled exception: division by zero [DivByZeroDefect]`, rc 1) and no handler runs. `nimPanics` is read only by `replayInScope` (`symex.nim:2343`) and the cache key. Severity vs 0.9.0: same (pre-existing), but it is a **clean false verdict on a plain build flag a consumer can set**; the engine already warns about panics (`engine.nim:60`) | soundness (false `sxSat`, false `sxRaised`) | `proc f(v:int) = try: (if v==5: discard 10 div (v-5)) except DivByZeroDefect: symexTarget("hit")` with `--panics:on` | `ran`: `~/nelli/wt-rsD/probes/p_panics.nim` (+`.cfg`): `pDivCaught/label: sxSat pathTaint={} runTaint={} replay=rsNotNeeded witness (5,)`; `pIdxCaught/label: sxSat`; `pFinally/label: sxSat`; `pRaised/tRaisedExn(DivByZeroDefect): sxRaised`; then `NATIVE: calling pDivCaught(5)` → `Error: unhandled exception: division by zero [DivByZeroDefect]`, rc=1 | a `--panics:on` suite (`tests/..._panics.nim.cfg`): every `except <Defect>` handler body and every `finally`-after-defect declines (`feCheckOption`-style, or a new `fePanicsBuild`), `tRaisedExn(<Defect>)` under panics decides `sxUnknown` or a new "process exit" status; native column by child-process exit code | S: under `defined(nimPanics)` treat a Defect raise as a `crash: true` escaped exit, exactly as S8cu's nil deref (`runtime.nim:25931`); bump walker; cfg suite |
| **D-02** | **Unchecked signed overflow is modelled as two's-complement wrap; C makes it undefined and gcc at `-O3` folds the comparison.** With `{.push overflowChecks: off.}` and the documented wrap mode (`SymexSettings(arithChecks: {acDivByZero, acRange})`, S8w; `-d:release`), `v + 1 > v` gives clean trusted `sxSat` at `v = high(int)`; natively the label is unreachable. The untainted `return paths` at `runtime.nim:24500-24502` is the mechanism. The same wrap mode is also reached by `-d:danger` users who set `arithChecks` to match. `--opt`, `--cc`, `--passC` are not keyed or read (INT-31), so a `-fwrapv` build and a `-O3` build share one verdict | soundness (false `sxSat`), opt-in setting | `{.push overflowChecks: off.}` `proc g(v:int) = if v+1 > v: discard else: symexTarget("hit")`, `symexFind(g, tLabel("hit"), SymexSettings(arithChecks: {acDivByZero, acRange}))`, `-d:release` | `ran`: `probes/p_ub.nim` (+`.cfg -d:release`): `pWrapGt: sxSat pathTaint={} runTaint={} witness (9223372036854775807,)`, `NATIVE pWrapGt(witness) = ran`; `pWrapNeg` same; `pWrapMul` happens to hit natively (gcc did not fold `v*2 < v`); default settings decline (`feOverflowCheckOption`) | pin in `tsymex_rfc0005_s8cu_cl_over`'s wrap test: the wrap decision must be replay-confirmed or declined when `-d:release`/`--opt:speed`; native column `native(pWrapGt(high(int))) == "ran"` | M: either (a) drop the wrap mode for *signed* `int` (keep it for `uint`, where C wraps), or (b) key and read `--opt`/`--passC` and decline wrap mode unless `-fwrapv`; (c) at least replay-gate the wrap survivors (`scSpurious`) instead of `return paths` |
| D-03 | D-02 sibling, **not confirmed**: `low(int) div -1` / `low(int) mod -1` under the same wrap mode. Walker: clean `sxUnsat` for the label, for `tRaisedExn(OverflowDefect)`, and for `m == 0 and v == low(int)`; natively gcc folded the constant divisor (`x / -1` → `-x`, `-x < 0` → `x > 0`) so no SIGFPE and no hit — native and walker agree on this build. Two notes for the construct lens (truncDivInt): (i) on the pure BV model `low(int) sdiv -1 = low(int) < 0`, so a clean `sxUnsat` means the walker's `div` is not plain `bvsdiv` here — whichever it is, it matched gcc's folding, not the x86 trap a non-constant divisor produces; (ii) with a *symbolic* divisor (`v div d`, `d == -1`) gcc emits `idiv` and the process dies — unprobed | build sensitivity (unverified) | `{.push overflowChecks: off.}` `proc h(v, d:int) = if v<0 and d<0: (let q = v div d; if q<0: symexTarget("hit"))` | `ran`: `probes/p_ub2.nim` (+`.cfg -d:release`): `pDivNeg1 (wrap modelled): sxUnsat`, `pModNeg1: sxUnsat`, `tRaisedExn(OverflowDefect): sxUnsat`; `NATIVE: returned; hits={}` rc=0 | same suite as D-02, symbolic-divisor variant | with D-02 |
| **D-04** | **`--mm:refc` is not a build nelli/symex can be used on**: nim-z3 fails to compile (`src/z3/ast.nim(63)`), so the `+mm=refc` key segment and the non-ORC branches of `dsl_parser.nim:5282`/`:17376` (havoc) are dead code, and a refc consumer gets a compile stop with no decline. Either fix nim-z3's hook signature for refc (then the hook/move model must be re-pinned on refc: S8cn's `ll_*`/`lg_*` differed by mm) or document refc as unsupported and make `symexFind` `error()` with a named reason | crash (compile stop), build | any `import nelli/symex` with `--mm:refc` | `ran`: `probes/p_refc.nim` (+`.cfg --mm:refc`): `Error: signature for '=destroy' must be proc[T: object](x: var T)` at nim-z3 `ast.nim(63,1)`, rc=1 | a `--mm:refc` cfg suite that either runs the hook pins or asserts the named compile-time refusal | S (refuse) / M (support) |
| **D-05** | `nodeWritesHeap` (`dsl_parser.nim:16574-16600`) is a fail-open denylist: `nnkAsmStmt`, `{.emit.}`, `nnkCast`, and a stdlib `var`-formal routine fed a dereference (`inc(p[])`, `swap(p[], x)`, `setLen(p[], n)`, `+=` through a `ptr`) are "no heap write". It is the predicate behind the S8cn `let`-cursor / `lent`-loop decline (`:16650-16653`), so the decline is not emitted and the path stays clean. `scanOpaqueEffects` (`:3861-3890`) handles asm/emit/cast correctly — two scanners, one rule | soundness risk (unemitted decline); construct-specific SUT belongs to the memory lens | `var gs = @[1,2]; var gp: ptr int` (set elsewhere) `proc f(k:int) = let c = gs; inc(gp[]); if c[0] == 2: symexTarget("hit")` | `read`: `dsl_parser.nim:16574-16600`, `:16650-16653`; compare `:3861-3890` | a pin that `nodeWritesHeap`, `routeStoresThroughDeref` and `scanOpaqueEffects` agree on a corpus of write shapes (asm, emit, cast, `inc(p[])`, `swap`, `setLen`, `copyMem`, `zeroMem`, `moveMem`) | M: invert to an allowlist of *read-only* node kinds; share one "may write memory" oracle |
| **D-06** | Hook copy proof `check` (`dsl_parser.nim:22505-22540`) defaults `result = true` ("field copied") for every node kind it does not enumerate; a `=copy`/`=dup` hook that moves a field by `swap`/`move`/`copyMem` is proved to copy it | soundness risk (unemitted decline) | `proc =copy(d: var D; s: D) = swap(d.buf, cast[var seq[int]](s.buf))` shape | `read` | same corpus pin as D-05 | S with D-05 |
| **D-07** | `svWithRaw` (`runtime.nim:2986-2999`) returns the *old* value for a composite kind — a silent substitution with no record. One caller today (`:15838`, scalar/string by contract) | latent soundness (no SUT today) | n/a | `read` | `doAssert`/decline in the `else` arm, unit test | S |
| **D-08** | `assertCoveredBy`'s host splat catches only `AssertionDefect`/`IndexDefect`/`FieldDefect`/`NilAccessDefect`/`CatchableError` (`symex.nim:4104-4118`). A clean, never-replayed winner (INT-22) whose witness raises `OverflowDefect`/`DivByZeroDefect`/`RangeDefect`/`ObjectConversionDefect` after the label kills the test process; under `--panics:on` any Defect does | crash (host), same as 0.8.0 | `proc f(v:int) = symexTarget("hit"); discard v + 1` with `v = high(int)` | `read` | `tsymex_rfc0005_r1_findingapi`: a witness that raises each Defect after the label is reported, not fatal | S: catch `Defect` in the splat; with D-01 for panics |
| **D-09** | `--cpu:i386` (and any 32-bit target): `int`, `uint`, `Natural`, `Positive` are hard-coded BV64 (`dsl_typebridge.nim:1787-1798`); pointer cells are 64-bit. Overflow at 2^31, `high(int)` witnesses, `sizeof` are wrong; `--cpu` is not keyed (INT-31) and not read. No 32-bit toolchain to probe | soundness (unverified, by reading) | `proc f(v:int) = if v == high(int): symexTarget("hit")` on `--cpu:i386` | `read` | `when sizeof(int) == 4` `error()` in `symexFind`, or `tInt(sizeof(int)*8)` plus a `--cpu:i386 --compileOnly` leg; key `--cpu`/`--os` | S (refuse) / M (model) |
| **D-10** | `isThreadvarSym` / `isImportedVar` (`symex.nim:2644-2651`, `:2727-2734`): a `getImpl` failure reads as "not a threadvar / not imported", so a C global reads as program storage for the replay footprint and the S8bo decline | precision/soundness risk at macro time | `var cg {.importc, nodecl.}: cint` reached through a generic alias | `read` | unit pin on an unreadable impl → `error()` or decline | S |
| **D-11** | `-d:nimOldCaseObjects` / `--experimental:strictCaseObjects` change discriminator-assignment semantics; not read, not keyed | unverified build sensitivity | `o.k = kC` on a live variant | `read` | cfg probe; key the define | S |
| **D-12** | Default `defectExclusions` drops a raise of `StackOverflowDefect`/`OutOfMemDefect` with no record (`runtime.nim:25851`, `:25936`): the path "just terminates". A user who adds `dkIndexDefect` to the set silently converts an `IndexDefect` path into "unreachable" and an `sxUnsat` stays trusted | policy / soundness-by-setting | `defectExclusions: {dkIndexDefect}` with `s[k]` before the label | `read` | an excluded defect records `dcOmitted` (run `{scIncomplete}`) so `sxUnsat` declines | S |
| **D-13** | The 17 `discard w.degrade(` halt sites are correct today, but nothing pins "a discarded token means no survivor". A future site that discards and continues is a clean path with a recorded run error — `sxUnsat` would decline but `sxSat` would be trusted | structural | n/a | `read`: §1 T5 | the allowlist test in §6 | S |
| D-14 | Refuted suspicion (recorded so it is not re-hunted): a user `object of Defect` without the `Defect` suffix is resolved through `userExnHierarchy` and is not caught by `except CatchableError`; `tRaisedExn("Boom")` decides `sxRaised` | n/a | `type Boom = object of Defect` | `ran`: `probes/p_userdefect.nim`: `pUserDefect: sxRaised`, `pUserDefectBare: sxRaised`, `pSoftDefect: sxSat`, native agrees | existing E4a pins | — |
| D-15 | Refuted suspicion: `symexAssume(cond)` evaluates `cond` natively (it is a `proc`, `engine/markers.nim:127`), and the walker surfaces raises from evaluating `cond` (`runtime.nim:24140-24160`) | n/a | `symexAssume(s[k] > 0)` | `read` | existing SND-2 pins | — |

---

## 6. How to make this closed

The §1 audit shows the carrier is sound: taint cannot be dropped by a fork, merge, cache or
save. Every finding above is a **clean model that disagrees with the build** — the same class as
R1-01..R1-04, R3-01 and B1–B26. "Closed" therefore means: the set of things that can make a clean
verdict wrong is enumerated, and each element is either keyed+read, declined, or proved by a pin.
Concretely:

1. **A build fingerprint that is both keyed and *consulted*.** Today `canonicalize.nim`'s
   `buildFlagsSegment` keys `panics`, `mm`, `exceptions`, backend, checks — but the walker consults
   only the checks, `setjmp` and the gc defines. Make one `BuildProfile` object (checks, panics, mm,
   exceptions, backend, `--opt`, `--cc`, `--cpu`/`sizeof(int)`, `--os`, relevant `--passC`
   fragments, `nimOldCaseObjects`) computed at nelli's compile, hashed into the key, **and** carried
   on `WalkCtx`; every arm that depends on a member reads it from there. The allowlist rule (§2.1):
   a profile member outside the verified set (today: goto exceptions, ORC/ARC, c/cpp, 64-bit, panics
   off) makes `symexFind` decline the whole SUT with a named kind (`feBuildUnverified`), the way
   S8bt declines an unverified PCRE build. D-01, D-04, D-09, D-11 become one row each in that
   allowlist, and a new flag is declined before it can be wrong.

2. **No clean path leaves a site that returns `paths` unchanged on a build condition.**
   `runtime.nim:24500-24502` is the one site that consumes a check-option marker *without* a
   token. Rule: a marker is consumed by `forkPathTainted` or by a halt; "model the wrap" must be a
   `dcFreshSymbol`-class degrade (replay-gated) or a native-proved allowlist (unsigned only).
   A grep-pin like the `forkPathTaintPrimitive` writer pin enforces it: every `of isUnsupported`
   exit forks with a token.

3. **A discarded `Degrade` token is a declared halt.** Make the halt explicit in the type:
   `w.halt(kind, msg)` that records and returns `seq[Path]()` (so the site cannot `continue` with a
   survivor), and a test that greps `discard w.degrade(` and asserts the only occurrences are the
   S1 probes. D-13.

4. **One memory-effect oracle, allowlist-shaped.** Replace `nodeWritesHeap`,
   `routeStoresThroughDeref`, `ptrUsesStayLocal`, the hook-copy `check`, `bindsViewWhole` with one
   `mayWrite(n): WriteSummary` that enumerates the node kinds proved *read-only* and answers "may
   write anything" for the rest (asm, emit, cast, non-user `var`-formal routines, proc values).
   Pin it on a corpus of write shapes with the native oracle (D1's generator can emit them). D-05,
   D-06, and the "no `else`" discipline for analysis predicates: `case n.kind` with no `else` and a
   `{.warning[...]:error.}`-style exhaustiveness is not available for `NimNodeKind`, so the test
   corpus is the enforcement.

5. **Defect semantics are a function of the profile, in one place.** `routeRaise`'s "is this
   catchable" answer should come from `profile.panics` (`false` for every Defect under panics,
   `crash: true` escape as S8cu's nil deref), and `isDefect` already resolves user types correctly
   (D-14). The splat in `assertCoveredBy` catches `Defect` (D-08).

6. **Width from the target.** `tInt(sizeof(int)*8)` in the type bridge, pointer cells likewise,
   and a `--cpu:i386 --compileOnly` CI leg (the same shape as `dt-crosswin.sh`) until a 32-bit
   runner exists; until then the profile allowlist refuses 32-bit (D-09).

7. **Build-matrix suites, not one build.** Every pin in §2.2's sense needs the build it ran on:
   add cfg-driven suites for `--panics:on`, `-d:release`, `--mm:arc`, `--exceptions:setjmp` (Linux),
   `--mm:refc` (asserting the refusal), and run them on the Linux leg; today no `tests/*.cfg` sets
   any of `panics`, `mm`, `exceptions`, `cpu`, `release`.

8. **The verdict carries its profile.** `SymexResult.soundness` (or `bounds`) should include the
   profile hash so a finding renders "decided on goto/orc/c/64-bit/-O0, panics off"; a consumer
   that reads a verdict into a different build can see it.

With 1–3 in place a wrong-while-clean verdict needs a *model* bug on a *verified* profile, which is
what D1's differential fuzzer searches for; without them each new flag, backend, width or optimiser
is a fresh D-01.

---

## Appendix — probes

All under `~/nelli/wt-rsD/probes/` on eos; each run as `scripts/dt-bounded.sh c probes/<p>.nim 400`.

| Probe | cfg | Result |
|---|---|---|
| `p_panics.nim` | `--panics:on` | D-01 confirmed (4 walker verdicts clean; native process dies) |
| `p_ub.nim` | `-d:release` (+ `{.push overflowChecks: off.}`) | D-02 confirmed (2 of 3 shapes; default settings decline) |
| `p_ub2.nim` | `-d:release` | D-03 not confirmed (walker `sxUnsat`, native no hit, no trap: gcc folded the constant divisor) |
| `p_refc.nim` | `--mm:refc` | D-04: nim-z3 compile stop |
| `p_userdefect.nim` | default | D-14 refuted (walker faithful) |

Not probed (no host): `--cpu:i386` (D-09); `--panics:on` on cpp (same mechanism as D-01, by reading).
