# nelli / symex

Symbolic execution for branch-targeted coverage proof. Shape B of
[nelli #100](https://github.com/coreyleavitt/nelli/issues/100).

> Given a Nim proc and a labelled point inside it, find a concrete
> input that drives execution to that point — or prove no such input
> exists.

The walker is a path-frontier interpreter over a small Nim-IR that
the parser builds at macro time. Each surviving path carries a Z3
formula; the target is encoded as a query to that formula. The
output is `SymexResult[ParamTuple]` carrying the witness when
satisfiable.

## Where to start

| If you want to… | Read |
|---|---|
| See it work | [examples/symex_simple.nim](../../examples/symex_simple.nim) |
| Walk through the model from first principles | [tutorial.md](tutorial.md) |
| Verify your random test covers a hard branch | [examples/symex_assert_covered.nim](../../examples/symex_assert_covered.nim) |
| Bring your own opaque proc under symex | [extending-stdlib.md](extending-stdlib.md) |
| Understand why the answer is what it is | [abstraction-internals.md](abstraction-internals.md) |
| Reason about Z3-version drift | [determinism.md](determinism.md) |

## The four target kinds

| Target | What it asks | Where to use |
|---|---|---|
| `tLabel("name")` | Find an input that reaches `symexTarget("name")`. | Coverage of arbitrary named branches. |
| `tAssertionViolation()` | Find an input that fails any `symexAssert(cond)`. | Bug-hunting for invariants. |
| `tIndexError()` | Find an input that drives any `arr[i]` out of bounds. | Memory-safety witnesses. |
| `tFieldDefect()` | Find an input that drives a variant arm-field access whose discriminator is outside that field's arm set. | Memory-safety / soundness witnesses on variant types. Phase 11. |
| `tUndefined(kinds)` | Find an input that reaches undefined behaviour of one of the listed `UbKind`s (default: all). | The input a halted `ub*` operation hides. The witness is never run in the host. RFC-0016. |

## Public surface

The single import:

```nim
import nelli/symex
```

re-exports the supported Nim type bridge (`nelli/smt/dsl`),
the choice IR (`nelli/choice`), the example DB
(`nelli/db`), and the engine `SymexFinding` type.

### Driver

```nim
macro symexFind*(fn: typed, target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): SymexResult[ParamTuple]
```

### Verifier (Phase 7)

```nim
macro assertCoveredBy*(fn: typed, target: static SymexTarget,
                       testFn: typed = nil, settings = …)
macro assertCoveredBy*(fn: typed, targets: static openArray[SymexTarget], …)
```

### Markers (dual-mode procs — usable in random PBT too)

| Marker | Outside symex | Inside symex |
|---|---|---|
| `symexTarget(name)` | feeds capture hit-set (if active) | label the parser recognises |
| `symexAssert(cond)` | `doAssert cond` | fork point under `tAssertionViolation` |
| `symexAssume(cond)` | no-op | conjoin into path condition |

### Extension pragma

```nim
proc myFFI(): int {.symexOpaque.} = ...
```

Tells the walker not to enter the body: fresh symbolic return, path
marked uncertain. See [extending-stdlib.md](extending-stdlib.md).

### Witness ↔ choice-IR + DB (Phases 7 + 10)

```nim
proc renderAsChoices*[T](w: T): seq[ChoiceNode]

# Content-addressed persistence (Phase 10) — key is derived from the
# SUT IR, target, witness-relevant settings, Z3 / Nim / walker
# versions. See determinism.md for the full contract.
macro saveSymexWitness*(db, fn, target, settings, finding, maxEntries = 64)
macro loadSymexWitnesses*(db, fn, target, settings): seq[seq[ChoiceNode]]

# Pure, testable key derivation
proc symexCacheKey*(prog: SymexProgram, target: SymexTarget,
                    settings: SymexSettings,
                    z3Version, nimVersion, walkerVersion: string): string
```

See [determinism.md](determinism.md) for the content-addressed
persistence contract and the proof-obligation table for every input
that does (or does not) participate in the cache key.

## Settings

```nim
SymexSettings(
  integerSemantics:        isOptimised,  # ADR-0001
  queryTimeoutMs:          5000,
  maxFrontierSize:         256,
  budget.walkRLimit:       1_000_000_000, # total Z3 units per walk; 0 = unbounded (cap ckWalkWork)
  maxCallDepth:            3,
  maxLoopUnwind:           5,
  acceptUnknownAsCovered:  false)
```

Constructors: `defaultSymexSettings()` / `optimisedSymexSettings()` /
`looseSymexSettings()`.

## Supported Nim fragment

### Types (`IRTypeKind`)

| Kind | Nim source shape | Phase | Notes |
|---|---|---|---|
| `itInt`    | `int`, `int8..int64`, `uint8..uint64`, `Natural`, `Positive`, `range[lo..hi]`, enums | 2 | BV[W] + selective Z3Int (ADR-0001) |
| `itBool`   | `bool` | 1 | |
| `itString` | `string` | 5 | Z3 string theory |
| `itTuple`  | tuples, plain objects (no `nnkRecCase`) | 4 | flat positional + named fields |
| `itArray`  | `array[N, T]` (any element type) | 4 | nested arrays via rectify round 1 |
| `itSeq`    | `seq[T]` | 5 | `len + Z3Array data` |
| `itTable`  | `Table[K, V]` | 5 | `data + present + size` |
| `itSet`    | `HashSet[T]`, `set[T]` | 5 | `members + size` |
| `itVariant` | Nim variant objects (`case kind: …`) | 11 | first-class sum type: per-arm fields, walker forks at access, witness via case-dispatch construction; literal- and symbolic-discriminant EXPRESSION construction landed Round 6 (ADR-0029, see below) |

### Float widths

`float32` and `float64` are separate IEEE sorts and `float32` arithmetic is
exact at its own width. A conversion between the two is exact (RFC-0016 K2b):
an explicit `float32(x)` / `float64(y)` (and `float(y)`) and the conversion
Nim inserts where a `float32` is passed, assigned or returned as a `float64`
lower to `fp.to_fp` at the target width in round-to-nearest-even. Narrowing
rounds (a tie goes to the even neighbour, an overflow gives infinity, NaN
stays NaN); widening is exact. So `float64(float32(x)) == x` is false for
`x = 0.1` and true for `x = 0.5`, as natively. Conversions between an integer
and either float width are unaffected.

### Statements (`IRStmtKind`)

| Kind | Nim source shape | Phase |
|---|---|---|
| `isBlock` / `isIf` / `isLet` / `isAssign` | block/if/elif/else, `let`, `=` | 1 / 5 |
| `isWhile` / `isBreak` / `isContinue` | `while`, `break`, `continue` | 6 |
| For loops | `for i in a..b`, `for x in arr`, `for x in seq` | 6 (desugared) |
| `case` | `case … of …` | 6 (if-elif lowering) |
| `isReturn` | `return [expr]` | 1 |
| `isAssert` | `symexAssert(cond)` | 1 |
| `isCall` | user-proc + stdlib-model calls | 3 / 5 |
| `isIndex` | `arr[i]`, `s[i]`, `t[k]` | 4 / 5 |
| `isVariantField` | A-normalised `let x = obj.field` on a variant arm field | 11 |
| `isVariantReassign` | `obj.kind = staticTag` | 11 |
| `isVariantConstructSym` | A-normalised `Type(kind: expr, ...)` with a symbolic (non-constant) discriminant | Round 6 |
| `isTargetLabel` | `symexTarget(name)` | 1 |
| `isUnsupported` | macro-time diagnostic for unmodelled AST | — |

### Container mutations

| Op | Source | Phase |
|---|---|---|
| seq `add`/`del`/`insert`/`pop` | `s.add(v)`, etc. | 5 / rectify round 1 |
| Table `[]=`/`del` | `t["k"] = v`, `t.del("k")` | 5 / rectify round 1 |
| HashSet `incl`/`excl` | `s.incl(x)`, `s.excl(x)` | 5 / rectify round 1 |

### Variant-object specifics (Phase 11)

| Feature | Phase 11 cycle |
|---|---|
| `nnkRecCase` lowered to first-class `itVariant` | 2 |
| Discriminator-only field access | 3 |
| Arm-field access (single & multi-arm via ite-chain) | 4 |
| `tFieldDefect()` target | 5 |
| Discriminator reassignment `obj.kind = staticTag` | 6 |
| Witness via case-dispatch construction (drops `default(Object)` stub) | 7 |
| `renderAsChoices` for variants (positional: disc + active-arm fields) | 8 |
| Discriminator interval `[min, max]` in `r.abstractions` (under `isOptimised`) | 9 |
| Nested variants (recursive composition) | 10 |

Walker version `"2"` (was `"1"` for Phases 0-10); persisted witnesses
from the old flat-tuple representation are correctly invalidated by
the content-addressed cache key.

### Variant-object construction (Round 6, ADR-0029)

Phase 11 covered reading an existing `itVariant` value (a param, a
callee's return, a field). Round 6 adds *constructing* one as an
expression — `Type(kind: tag, field: expr, ...)` — which previously had
no case in the walker's expression path at all (every constructor
declined; see `docs/rfc/0001-chapulin-hardening.md` ADR-0029).

| Feature | Kind | Walker ver |
|---|---|---|
| Literal-discriminant construction (`Type(kind: someTag, ...)`, `someTag` a compile-time constant) → `svVariant`, inactive arms fresh-unconstrained | `iekVariantLit` | 75 |
| Symbolic-discriminant construction (`Type(kind: expr, ...)`, `expr` genuinely symbolic) → fork-per-feasible-tag, every declared arm's fields fresh per fork | `isVariantConstructSym` | 77 |
| `maxVariantConstructorForks` budget (default 8) on the symbolic-disc fork count; past it, classified `beBudgetExhausted`, never a crash | `isVariantConstructSym` | 77 |
| A callee's `svVariant` return value binds into the caller (`discEq ∧ (⋀ arms: disc==tag → per-field eq) ∧ plain-field eq` — sound for both a literal-pinned construction and a pass-through of a variant-typed parameter) | `retBindEq` | 76 |

Declined, cleanly (classified `sxUnknown`, never a crash):

- A multi-`case` object (`itMultiVariant`) constructor — ships as its
  own slice only if a consumer needs it first (ADR-0029).
- A ref-object-aliased variant constructor (`type Node = ref object;
  case kind: …`) — `itVariant` value-modeling stays scoped to
  non-ref-aliased constructors (ADR-0022 sub-decision #1).

Nim itself (not a symex restriction) only accepts a non-constant
(symbolic) discriminant in constructor syntax when **no** arm-specific
field is set alongside it — a construction site with a symbolic disc
and an arm field is rejected by the Nim compiler before symex ever
sees it, regardless of walker capability.

## Input-source seeding (Phase 12)

Symex has a second role beyond verification: lifting its witnesses
into the random-PBT loop as **forced seeds**. The user writes one
SUT proc; symex auto-discovers every target the SUT exposes, runs
Z3 per target, and replays each SAT witness through the engine —
where the shrinker minimises it the same as any random
falsification.

### Auto-discovery

The macro scans the SUT's IR (transitively through
`parseProc.procs` for `isCall` bodies — same Phase-3 cross-module
limit applies) and includes a target per IR construct it finds:

| IR construct in the SUT | Auto-included target |
|---|---|
| `symexTarget("name")` (one per occurrence) | `tLabel("name")` |
| `symexAssert(cond)` (any `isAssert`) | `tAssertionViolation()` |
| `arr[i]` / `s[i]` / `t[k]` (any `isIndex`) | `tIndexError()` |
| variant arm-field read (any `isVariantField`) | `tFieldDefect()` |

No defect-triggering construct and no markers → exactly one
`SymexFinding(status: sfNotApplicable, targetDesc:
"no-targets-discovered")` audit entry is produced; no Z3 calls.

### Escape hatch — `excludeTargets`

```nim
symexForAll(integers(), handle, db = db,
            excludeTargets = @[tIndexError(), tFieldDefect()])
```

Filter is by `SymexTargetKind`. Excluding `tLabel(...)` suppresses
all label targets; label-by-name suppression is a deferral (see
[PHASE12_PLAN.md](PHASE12_PLAN.md) deferrals table).

The constructor-form spelling is the same vocabulary as
`assertCoveredBy(..., tIndexError())`. The seq-literal form
(`@[…]` rather than `[…]`) is required because a bare static
openArray default crashes Nim 2.2's macro evaluator — see the
plan-doc deferrals for the toolchain bug.

### Three-layered API

```nim
# Layer 1 — primitive. Macro-scans fn's IR for every auto-target,
# runs symex per target (cache-first via the Phase 10 content-
# addressed key), returns one SymexFinding per. Also deposits
# each finding into the per-thread sink so finalizePhase can
# drain them into Report.symexFindings.
macro symexFindAllWitnesses*(fn: typed,
                              db: ExampleDatabase,
                              symexSettings: static SymexSettings =
                                defaultSymexSettings(),
                              excludeTargets: seq[SymexTarget] = @[]
                             ): seq[SymexFinding]

# Layer 2 — engine entry. Custom pipeline that slots
# `symexSeedPhase(seeds)` between `explicit` and `random`.
proc forAllWithSymexSeeds*[T](seeds: seq[seq[ChoiceNode]],
                              s: Strategy[T], prop: proc(x: T),
                              settings: Settings = defaultSettings()
                             ): Report[T]

# Layer 3 — sugar. fn doubles as the property AND as the IR-scan
# target. Multi-arg fns + `map(s1, s2, ...)` strategies are
# supported via a macro-emitted tuple-splatting wrapper.
macro symexForAll*(s: typed, fn: typed,
                   db: ExampleDatabase,
                   symexSettings: static SymexSettings =
                     defaultSymexSettings(),
                   forAllSettings: Settings = defaultSettings(),
                   excludeTargets: seq[SymexTarget] = @[]
                  ): untyped
```

### Pipeline order

```
dbReuse → explicit → symexSeed → random → targeted → shrink → explain → finalize
```

The `symexSeed` phase consumes the seed list end-to-end on each
seed via `evalReplay`:

- `ekFalsified` → set `rawFalsification` with the replayed choice
  sequence so `shrinkPhase` can minimise the witness.
- `ekRejected` (Overrun from a shape-mismatched seed OR property
  `reject`/`assume`) → deposit one `sfNotApplicable` audit entry
  and continue.
- `ekPassed` → continue silently.

Self-gates when an upstream source phase (e.g. `dbReuse`) already
set `rawFalsification`.

### Warm-run note

When the DB already holds a stored failure for the SUT,
`dbReusePhase` runs first and sets `rawFalsification` → the
self-gate in `symexSeedPhase` skips it on that run. This is the
common case in active development. Callers who want a symex audit
even when dbReuse falsifies should call `symexFindAllWitnesses`
directly (Layer 1) and inspect the returned findings — Layer 1's
sink-deposit behaviour is independent of the engine pipeline.

### Cold-cache latency

On a fresh DB the worst-case cost for one
`symexFindAllWitnesses` invocation is

```
N targets × per-target solver cost (bounded by SymexSettings.queryRLimit
                                    if set; unbounded if 0)
```

where `N` is the number of auto-discovered (post-`excludeTargets`)
targets and per-target solver cost is measured in Z3 logical
steps (`queryRLimit`), not wall-clock ms — Phase 13 wired the
field to Z3's `rlimit` parameter for deterministic resource
bounds. Default `queryRLimit = 0` means unbounded; opt in by
setting a positive value.

**Total work per walk.** `budget.walkRLimit` bounds the sum of Z3
resource units (`rlimit`) every solver check of one walk spends, which the
per-query bounds do not (thousands of fast checks over multiplying unrolled
paths). The default is `1_000_000_000` (about 5.7x the largest decided walk
in the suite); `0` opts out. At the limit the walk stops and records the cap
`ckWalkWork` (`beBudgetExhaustedPrune`): paths not yet decided are
`sxUnknown`, while a target already reached with a sound witness stays a hit.
Deterministic and part of the cache key. To measure it, set the environment
variable `NELLI_WALK_UNITS_LOG` to a file: each finished walk appends one line
`<units>\t<target>\t<status>` (target `label:<name>`, `raised:<type>` or the
target kind). That is how the default is re-measured over the corpus.

**Warm-run cost** (after Phase 13's verdict caching): one DB
load per target. SAT, UNSAT, and UNKNOWN findings all cache
under the content-addressed key. `SymexFinding.fromCache` flags
the load-vs-derive provenance so consumers can audit the cache
hit rate:

```nim
let report = symexForAll(s, fn, db)
let hits = report.symexFindings.countIt(it.fromCache)
echo "cache hit rate: ", hits, "/", report.symexFindings.len
```

### Upgrade note from Phase 12 → Phase 13

Phase 13 rotates the cache key once across two axes:

1. `SymexSettings.queryTimeoutMs` (uint, ms — never wired) was
   renamed to `queryRLimit` (uint, Z3 logical steps — now wired
   via `Z3_solver_set_params`). The canonical-form tag prefix
   changed from `";to="` to `";rl="`. Every Phase 12 cache
   entry rotates.
2. SAT witnesses moved from the bare `"sx:" & H` key to
   `"sx:" & H & ":sat"` to make room for the new sibling slots
   `:unsat` and `:unk`.

On upgrade: **first run after Phase 13 re-derives every
previously cached SAT witness**; one-time cold cost. From the
second run onward, UNSAT/UNKNOWN verdicts cache too — net win
even for cache-warm SUTs that previously paid `N × queryTimeoutMs`
on every UNSAT-prone target.

See [determinism.md § Verdict caching](determinism.md#verdict-caching-phase-13)
for the full contract.

### Upgrade note from Phase 11

`renderAsChoicesVersion` bumped `"1"` → `"2"` in Phase 12 to
invalidate the latently-broken length-prefix encoding of
`seq[T]` / `HashSet[T]` / `Table[K, V]` witnesses (the old
encoding could not be replayed through `lists`/`tables`/`sets`
strategies; the new continue-boolean encoding matches what those
strategies actually consume). Effect on existing DBs:

- **Collection witnesses** persisted under `renderAsChoicesVersion
  = "1"` become invisible on the next run and re-derive once.
- **Non-collection witnesses** (int / bool / string / tuple /
  object / variant) are unaffected — their choice encoding did
  not change.

Walker version stays at `"3"`; non-collection witnesses across
the Phase 12 upgrade keep their cache entries.

## Declines, taints and undefined behaviour

A run that cannot model something does not guess. It records a classified
`SymexErrorInfo` (`SymexResult.errors`, `SymexFinding` through `gaps`), and the
kind tells you what the walker did in place of the real behaviour. Every kind
below is a member of `SymexErrorKind`; read them off the result, never by
matching message text. The four classes (`classOf`) decide what the verdict
may claim:

| Class | What the walker did | What it costs the verdict |
|---|---|---|
| no answer | the walk stopped; there is no path | `sxUnknown` |
| substituted | a forced value, a stale environment or a fabricated continuation took the real behaviour's place | a `sxSat` or `sxUnsat` through the path is not trusted; the path's claim is `sxUnknown` or an untrusted verdict |
| fresh symbol | the result became an unconstrained value of its sort, a superset of the real behaviours | an `sxUnsat` stands; an `sxSat` is replayed on the real function before it is reported |
| omitted | the path was dropped (a halt, a crash, or a pruned side) | the omission is recorded; a trusted `sxSat` needs the omission to be benign |

`trusted(result)` is the test for "may I act on this verdict"; `gaps(result)`
is the per-cause view.

### Undefined behaviour (`ub*`, `UbKind`)

Nim leaves some operations to C, and C leaves them undefined: the compiler may
assume they never happen and rewrite code around them, including code before
them. The walker does not pick one build's outcome. The path ends at the
operation (it is neither a `Defect` nor a value) and the omission is recorded.
These are all in the *omitted* class.

Two things can happen to the omission, by kind:

- Only `ubIndeterminateRead` (a `{.noinit.}` local read before any write) rides
  a witness. The path continues past the read, so a witness that reaches the
  target past it carries the kind in `Soundness.witnessUndefined`
  (`undefinedKinds()`), which a replay cannot lift: the witness is not
  `trusted()` and is not run in your process by `assertCoveredBy` or
  `symexForAll`.
- The arithmetic kinds (`ubUnsignedDivZero`, `ubIntMinModMinusOne`,
  `ubSignedOverflow`, `ubSignedDivZero`) and `ubFloatToIntRange` halt the path
  at the operation. The
  halted side reaches no label and no Defect; the omission shows in the
  verdict's gaps, so an `sxUnsat` is not trusted past it. A witness found
  through a different, defined path is unaffected. To ask for the input that
  reaches the operation, search for it: `tUndefined()` (or
  `tUndefined({ubUnsignedDivZero})`) returns `sxSat` with that input, which is
  never `trusted()` and never run in your process; `sxUnsat` means none of the
  *listed* kinds is reachable. Under any other target the same inputs are
  listed on `SymexResult.undefined` (`UndefinedFinding`: kind, site, witness;
  `SymexFinding.undefined` as `FindingUndefined`), at most eight per run,
  and the halt names `tUndefined()` as the next query.
- Every kind is read from the definedness table (`smt/definedness.nim`):
  `(operation, operand class)` to *defined*, *Defect* or *undefined* by build
  profile. A float to int conversion (`int(f)`, `int32(f)`, `uint8(f)`) of NaN,
  an infinity or a value whose truncation does not fit the target is
  `ubFloatToIntRange` under every profile: Nim emits a plain C cast and no
  check raises. In range the truncation toward zero is exact. (A `range`
  target such as `Natural(f)` still raises `RangeDefect` for a converted
  value outside the range.) It no longer records `feConvFloatToIntUndefined`,
  which nothing produces now.
- Three cases stay declines, not kinds: `<` over `ptr` (the order of two
  addresses is the allocator's), a use of `addr s[i]` after `s` may have
  resized, and a routine that declares a `{.noalias.}` parameter beside another
  pointer-like one (C `restrict` makes an alias of the two undefined). Each is
  a `feUnsupportedOp` decline naming its `defined:` cell.

| Kind | The operation | What to do |
|---|---|---|
| `ubUnsignedDivZero` | `x div 0` or `x mod 0` on an unsigned type. Nim has no check; the C division traps (SIGFPE on x86-64). Not a `DivByZeroDefect`. | Guard the divisor, or keep the property off inputs where it can be zero. |
| `ubIntMinModMinusOne` | `low(T) mod -1` (and `low(T) div -1` with overflow checks off) at 32 and 64 bits. The C division is undefined and traps on x86. | Guard the divisor against `-1` for the minimum. |
| `ubSignedOverflow` | signed `+`, `-`, `*` or negation that overflows, in a build with overflow checks off (`--overflowChecks:off`, `-d:danger`, `-d:release`) at 32 and 64 bits and no `-d:nelliFwrapv` (8 and 16 bit wrap). The compiler may assume it never happens (`v + 1 > v` folds to true). | Build with overflow checks on, or bound the operands. (Or build with `-d:nelliFwrapv`, which passes `-fwrapv` to every C unit, so signed `+`, `-`, `*` and negation wrap at every width and the walker models the wrap; `low(T) div -1` and `mod -1` stay undefined. Not available under `vcc`, which is refused.) |
| `ubIndeterminateRead` | a read of a `{.noinit.}` local before any write. | Initialise it. |
| `ubSignedDivZero` | `x div 0` or `x mod 0` on a signed type in a build with overflow checks off (`--overflowChecks:off`, `-d:danger`, `-d:release`). Nim emits its zero check under `overflowChecks` alone, so the C division is reached and is undefined (SIGFPE on x86-64). With the checks on it is a `DivByZeroDefect`. | Guard the divisor, or build with overflow checks on. |
| `ubFloatToIntRange` | a float to int conversion whose operand is NaN, infinite or whose truncation does not fit the target type. Nim 2.2.10 emits a plain C cast and range-checks the cast value, so no check profile raises and the cast is undefined (the value differs by platform). | Bound the operand before the conversion. |

### Build and check taints

| Kind | Meaning | What to do |
|---|---|---|
| `feCheckOption` | A routine is compiled without a check the walker models (`fieldChecks`, `rangeChecks`, `boundChecks`, `objChecks`), or with a float check it does not; or `SymexSettings.arithChecks` was set to something other than what the build compiles in. The routine's raises and values are not the model's. | Compile with the checks on. Do not set `arithChecks`: the build decides it (see the 0.9.2 migration note). |
| `feOverflowCheckOption` | `{.push overflowChecks: off.}` (or `{.overflowChecks: off.}`) on a routine while the settings model overflow. A pushed-off routine in a checking build always declines. | Remove the pragma, or build the whole program with overflow checks off. |

A `{.push overflowChecks: on.}` routine in a checks-off build is modelled as a
checked routine: its signed overflow and division by zero raise.

### Constructs the walker declines

Path-scoped: only the paths that reach the construct are affected, and the
rest of the run is unchanged.

| Kind | Meaning | What to do |
|---|---|---|
| `feLocalPragma` | A local `var` or `let` carries a pragma the walker neither models nor can ignore. Admitted: `noinit`, `global`, `inject`, `gensym`, `used`. Any other (`cursor`, `align`, `volatile`, `codegenDecl`, ...) declines on every path that reaches the declaration. `{.cursor.}` in particular makes the local share the source's memory, which the walk models as a copy. | Move the pragma off the analysed routine, or restructure. |
| `feHostUnadmitted` | The host half of the build profile is not a verified one: the loaded libz3 is not 4.13.4 or 5.1, or no build row covers this build under it. Read once, at the first run (`symexFind`, `symexFindAllWitnesses`, `symexForAll`, `concolicCollect`, `concolicFlip`); the run decides nothing and is `sxUnknown` (a concolic collect carries it in `parseErrors`). It is not a raise. The message names the field and the value (`z3 4.12.2 is not a verified Z3 (4.13.4, 5.1)`). A libpcre outside the verified builds does not raise it: each regex call declines on its own (`psUnverifiedLib`). | Run against Z3 4.13.4 or 5.1. |
| `feUnadmitted` | A cell with no row in its admission table: the code reached a construct, type, pragma, magic or build cell that the axis was never asked to classify. It declines, never a silent model, with `dcOmitted`: the path is dropped, so no target past the cell is claimed and a run that needed it is not trusted. sevError. Produced today by the magic axis for a `var`-parameter magic with no row. | Add the cell's row to its admission table, or avoid the construct. |
| `feDefectExcluded` | A `Defect` raised on a feasible path reached the SUT boundary, and its `DefectKind` is in `settings.defectExclusions` (the default excludes `OutOfMemDefect` and `StackOverflowDefect`). The path ends with no finding, `dcOmitted`, so a search that raise could have answered is `sxUnknown`, never a trusted `sxUnsat`. sevError. | Remove the kind from `defectExclusions` to have the raise reported as a finding, or keep the exclusion and accept that runs reaching it are not trusted. |
| `feConvFloatToIntUndefined` | No longer produced (K10a-float): an out-of-range float to int conversion is `ubFloatToIntRange`. | Bound the operand before the conversion. |
| `feUnsupportedOp` | An unmodelled operation; its result is a substituted value. | Mark the callee `{.symexOpaque.}` or `{.symexTransparent.}`, or extend the model. |
| `feUnsupportedOpHavoc` | As above where the result is a fresh unconstrained symbol (a superset). | None needed for an `sxUnsat`; an `sxSat` is replayed. |
| `feUnsupportedOpAborted` | An unmodelled `math.<name>` or float operation aborted the whole walk. `sxUnknown` with no path. | Avoid the operation under analysis, or wrap it in an opaque callee. |
| `feFloatWidth` | A `float32` <-> `float64` conversion the walker could not model exactly. No site produces it since K2b: both directions are exact (`fp.to_fp`, round-nearest-even). | None; report it if it appears. |
| `feUnsupportedExprKind` | The parser met an expression shape outside the supported fragment. It used to stop the compile; it now declines. | Rewrite the expression, or see the supported fragment. |
| `feUnsupportedStmtKind` | The same for a statement position (unmodelled assignment shapes, iterator forms, an uninitialised declaration the model cannot place). | As above. |
| `feUnsupportedParamType` | A parameter type outside the supported scalar and container set. | Take a supported type at the analysed boundary. |
| `feUnsupportedWitnessType` | The witness reader cannot render a `seq`, `Table` or `HashSet` element shape. | Use a renderable element type. |
| `feEnumOrdinalUnresolved` | An enum constant's ordinal could not be resolved from its declaration. | Reference the constant through its type. |
| `feExtractionFailed` | The solver's model value for a float could not be read back, so the witness renders lossily. A lossy witness is replayed or not trusted. | Treat the witness as an approximation. |
| `feEvalOrderUnmodelled` | An operand Nim checks where it stands but reads after a later operand's call (`a[i] + f()`) where that call changes what the operand reads. | Bind the operand to a `let` first. |
| `feGlobalReadUnmodelled` | A read of a module-level name the walk could not bind. | Pass the value as a parameter. |
| `feGlobalRouteUnproved` | A read of a module-level `var` that a store the walk does not see may reach (a lifetime hook, code the analysis cannot read). The held value may be stale. | Pass the value as a parameter. |
| `feOpaqueCallUnmodelled` | A call classified as a black box (`echo`, `readLine`, `writeFile`, ..., or a `{.symexOpaque.}` proc) whose result or effects the walker cannot model. | Mark an inert callee `{.symexTransparent.}`, or accept the taint. |

### Over-approximations (fresh symbols)

Nothing is forked away and no effect is dropped, so an `sxUnsat` holds for
every real behaviour and an `sxSat` is replayed before it is reported.

| Kind | Meaning |
|---|---|
| `feGlobalHavoc` | A module-level variable the walk does not know takes a fresh value (a read before any write, or a global an opaque call's summary says it may write). |
| `feOpaqueEffectHavoc` | An inert opaque call's other effects: heap cells it reaches take fresh contents, and a raise of each type it declares is forked. |
| `feUncheckedDiscBytes` | A discriminator written under `{.cast(uncheckedAssign).}` to a different value takes the old bytes or zero. |
| `feTableIterOrder` | A `for` over a `Table` with two or more entries on the path: the walker visits the keys in a free order, which covers the real hash order. |

### Replay hints

A candidate `sxSat` is run on the real function. These record why it did not
become a confirmed claim. They are `sevHint`s on an `sxUnknown` result, never
part of the taint.

| Kind | Meaning |
|---|---|
| `feReplayRefuted` | The real run completed without reaching the target: a confirmed model gap on that witness. |
| `feReplayTimedOut` | The replay outlived `SymexSettings.replayTimeoutMs`. Neither confirmed nor refuted. |
| `feReplayCrashed` | The replay ended its child process (an exit, a signal, a system exception) before, or after, reaching the target. The message says how. |
| `feReplayDeclined` | No child could run the replay (it could not start, or the state the SUT may reach cannot be handed to one). |

Retired kinds (`feConvDomainExcluded`, `feTransparentArgNotInert`,
`feTransparentResultUsed`) keep their ordinal and are never emitted; they stay
in `SymexErrorKind` so cached entries and consumer `case` statements keep their
meaning.

`scripts/check-readme-kinds.sh` fails if a `fe*` or `ub*` member of
`SymexErrorKind` (other than a retired one) is not named in this file.

### C flags the walker cannot see

`querySetting` does not report `--passC`, so the walker cannot tell which C
flags a build passes. `BuildProvenance.assumedAbsent` (`smt/buildprofile.nim`)
lists what it assumes absent, and an undefined-behaviour halt says so in its
message (`assumedAbsentNote`):

| Flag | What the walker assumes | Evidence |
|---|---|---|
| `-fwrapv` | absent, except under `-d:nelliFwrapv` (which passes it) | K5b cfg suite; K10c UBSan sweep of the `-fwrapv` profile |
| `-ftrapv` | absent: signed overflow does not abort | not pinned |
| `-ffast-math` | absent: float operations are IEEE | not pinned |
| `-fsanitize=*` | absent: a sanitizer only makes an undefined operation fault, so the definedness table holds under UBSan | K10c: every arithmetic row of `definednessTable` checked against `-fsanitize=undefined` on Linux (`tests/tsymex_0016_k10c_ubsan.nim`); no UBSan runtime on mingw or MSVC |
| `-ffp-contract=fast` | present as gcc's default but inert on baseline x86-64 (no fused multiply-add), so `a * b + c` is two roundings | K10c: a `-ffp-contract=off` build equals the default build, and `-mfma` differs (`tests/tsymex_0016_k10c_fma.nim`); a build with `-march=native` or `-mfma` is outside the row |
| `-fno-strict-aliasing` | absent: strict aliasing is on | not pinned |

## Local variable pragmas

A pragma on a local `var` or `let` is either admitted or declined. Admitted:
`noinit` (the local reads as an indeterminate value until written, see
`ubIndeterminateRead`), `global`, `inject`, `gensym` and `used`. Any other
(`cursor`, `align`, `volatile`, `codegenDecl`, ...) is declined with
`feLocalPragma` on every path that reaches the declaration. The declaration is
still lowered so later uses resolve. To analyse the routine, move the pragma
off it. The catalogue row is under "Constructs the walker declines".

## Out of scope for v1 (diagnosed at macro time)

- Unbounded loops without invariants (k-unwind exhaustion → `sxUnknown`)
- Cross-module private callees (Nim `getImpl` returns empty)
- Concurrency / threads / channels
- Closures with environment capture (single-pointee `ref T` works)
- Floats (planned later)
- Generics beyond simple typedesc substitution
- Variant object **inheritance** (`type Foo = object of Bar`)
- Variant **`else:` branches** in `nnkRecCase` (use exhaustive `of`)
- Variants with **multiple `nnkRecCase` members** per object
- **Symbolic** discriminator reassignment (`obj.kind = someVar`)
- **Composite arm-field types under reassignment** (only primitives zero-init on `obj.kind = staticTag`)

A SUT outside the fragment is rejected with a macro-time error
naming the offending node — never silently elided.

## Architectural decision records

| | Title | Status |
|---|---|---|
| [ADR-0001](ADR-0001-integer-semantics.md) | Integer semantics — BV[W] floor with selective `Z3Int` abstraction | Accepted 2026-05-31 |
| [ADR-0002](ADR-0002-dsl-factoring.md) | Predicate-DSL factoring — three-layer `nelli/smt/` split | Accepted 2026-05-31 |
| [ADR-0030](ADR-0030-boundary-normalization.md) | Boundary normalization — the walker's input language is defined by what the boundary emits, not what the compiler can produce | Accepted 2026-08-14 |

An ADR is a short document recording one architectural decision:
the context that forced the choice, the options considered, the
resolution, and the consequences. When revisited, the ADR is
amended in place with a "Superseded by …" header. Reference:
[Michael Nygard, *Documenting Architecture Decisions*, 2011](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions).

## Status

Phases 0-13 shipped: full SUT fragment, four target kinds, the
content-addressed DB (now with three sibling slots for SAT /
UNSAT / UNKNOWN verdicts), first-class variant soundness, the
input-source role lifting witnesses into the random-PBT loop via
the three-layered `symexFindAllWitnesses` / `forAllWithSymexSeeds`
/ `symexForAll` API, Z3 `rlimit` wired for deterministic UNKNOWN
caching, and `SymexFinding.fromCache` provenance for cache-hit
audit. See [../SYMEX_PLAN.md](../SYMEX_PLAN.md) for
the live plan and commit references.
