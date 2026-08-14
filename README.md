# nelli

> *nelli* — Nahuatl: "truth; that which is true"

Property-based testing, coverage-guided fuzzing, and SMT-backed symbolic
execution for [Nim](https://nim-lang.org) — one engine, one API.

At its core, nelli is a property-based testing library built on a
**choice-sequence engine**, the architecture behind Python's
[Hypothesis](https://hypothesis.works): generators are parsers over a recorded
sequence of typed primitive choices, so **shrinking is automatic, composable,
and survives `map` / `filter` / `flatMap`** — no hand-written shrinkers, ever.
Around that core it layers the rest of the input-generation spectrum: targeted
and coverage-guided generation, corpus-based fuzzing of both properties and
external binaries, stateful model testing, linearisability checking, bounded
model checking, bisimulation, and a symbolic-execution engine that uses Z3 to
find inputs, prove unreachability, and audit test adequacy.

```nim
import std/[unittest, algorithm]
import nelli

suite "list properties":
  property "reversing a list twice is the identity":
    given xs in lists(integers(0, 9))
    ensure xs.reversed.reversed == xs

  property "addition commutes":
    given a in integers(-50, 50), b in integers(-50, 50)
    ensure a + b == b + a

  property "reserved-keyword names round-trip":
    with Settings(maxExamples: 7, seed: 42,
                  testId: "kdl-keywords", dbPath: ".nelli-db")
    given keyword in sampledFrom(["true", "false", "null", "inf", "-inf", "nan", "0"])
    ensure roundTrip(keyword) == keyword
```

That compiles. That runs. That **shrinks**. And `nimble test` reports the
results natively through `std/unittest`.

## Highlights

- **Automatic shrinking** that composes through every combinator — a property
  of the recorded choice sequence, not the type.
- **Strategy auto-derivation**: `arbitrary(T)` for primitives, containers,
  tuples, objects, enums with holes, object variants, ref objects, generics,
  `distinct`, `range`/`Natural`/`Positive` refinements, and directly-recursive
  types.
- **Stateful testing**: rule-based state machines with per-step invariants,
  typed value flow between rules, and shrinking that respects dependencies.
- **Search beyond random**: targeted PBT (hill-climb + simulated annealing on
  user scores) and coverage-guided PBT (coverage delta as an objective).
- **Fuzzing**: every property doubles as a libFuzzer/AFL target; a built-in
  coverage-guided loop fuzzes properties in-process or external binaries
  (C/C++/Rust/Nim) with pluggable delivery, crash oracles, differential
  targets, and persistent corpora.
- **Verification tools**: Wing-Gong linearisability checking, a thread-based
  parallel runner with shrinkable schedules, bounded model checking for state
  machines, and observational-equivalence bisimulation.
- **Symbolic execution** (opt-in, Z3-backed): solve for inputs that reach a
  label, raise an exception, or violate an assertion; prove targets
  unreachable up to bounds; verify that your tests actually exercise a
  target; feed solver witnesses into the property runner as seeds.
- **Higher-order tooling**: algebraic law packs, metamorphic testing,
  Daikon-style property mining, mutation testing of your properties, and
  JSON Schema → strategy compilation.
- **Reproducibility and observability**: an example database that replays
  failures across runs, one-paste `repro()` strings, per-example notes,
  cross-example event statistics, automatic distribution labels, and
  text / JSON / JUnit / GitHub-annotation report formats.

## Installation

With [milpa](https://github.com/coreyleavitt/milpa):

```kdl
deps {
    "nelli" git=(url)"https://github.com/coreyleavitt/nelli.git" ref="main"
}
```

The package also ships a standard `.nimble` file. Releases are published to
the [tianguis](https://github.com/coreyleavitt/tianguis) registry as signed
OCI artifacts.

Requirements:

| Feature | Needs |
|---|---|
| Everything except symex | Nim ≥ 2.0.0, no external dependencies |
| `nelli/symex` | Nim ≥ 2.2.10, [nim-z3](https://github.com/coreyleavitt/nim-z3), and the Z3 shared library at runtime |

`import nelli` never touches Z3 — symbolic execution lives behind the
separate `import nelli/symex`.

## Writing properties

**Strategies.** Built-ins: `integers` (full `uint64` range via an owned 128-bit
primitive; optional weighting), `floats`, `booleans`, `lists`, `strings`
(ASCII default, or any Unicode `IntervalSet`), `tables`, `sets`, `enums`,
`sampledFrom`. Combinators: `just`, `map` (unary and variadic-product forms),
`filter`, `flatMap`, `oneOf` (with swarm-testing branch muting), `frequency`,
`recursive`, `sampledFromWhere`, and `displayWith` for custom counterexample
rendering. Distribution biasing is built in: small-magnitude bias, boundary
injection (`0`, `±1`, `min`, `max`, `NaN`, `±Inf`, `±0`), and
replay-deterministic swarm testing.

**Derivation.** `arbitrary(MyType)` synthesizes a strategy for nearly any Nim
type, including object variants, generics, `distinct` types, and
directly-recursive shapes (trees, linked lists, JSON-like ASTs). Refinement
types derive to typed strategies: `arbitrary(range[1..10])` is a
`Strategy[range[1..10]]`, so the constraint survives `map`/`flatMap` without
casts. Mutual recursion is detected at compile time with a pointer to the
manual `recursive(...)` combinator.

**Rejecting examples.** Use `Strategy.filter(pred)` when the predicate needs
only the generated value; use `assume(cond)` inside the property body when it
depends on state computed after the draw:

```nim
property "doc with removable prop preserves structure":
  given src in sampledFrom(corpus)
  let parsed = parse(src)
  assume parsed.isOk
  let doc = parsed.get
  assume doc.hasRemovableProp
  ensure isStructurallyValid(doc.removeProp())
```

`assumeOk(expr)` / `assumeSome(expr)` collapse the common
"assume it parsed, then unwrap" two-liner, duck-typed over any
Result-shaped type or `Option[T]`. For finite corpora,
`sampledFromWhere(items, pred)` filters eagerly at construction instead of
burning the rejection budget at runtime.

**Custom strategies.** `newStrategy(...)` plus the exported `DataSource` draw
API (`drawInteger`, `drawFloat`, `drawBytes`, `drawString`, spans) is the
documented escape hatch — everything you need is reachable from
`import nelli` alone.

## Failure reporting and reproducibility

`forAll` returns a deterministic `Report` carrying the outcome, the
**shrunk** counterexample, the recorded choice sequence, seed, notes, events,
and more. Crashes (`Defect`s like `IndexDefect`) are caught as falsifications,
and a two-layer flakiness detector separates nondeterminism from real bugs.

- `repro(report)` formats a one-paste reproduction string: seed, outcome,
  counterexample, choice sequence.
- The **explain phase** perturbs each recorded choice after shrinking and
  tags it necessary or free, so `repro()` shows which choices the failure
  actually depends on.
- `note(label, value)` attaches debug values to the current example; the
  shrunk counterexample's notes survive into the report.
- `event(label[, numericValue])` accumulates cross-example statistics
  (categorical counts, min/max/mean/p50/p90/p99).
- `Settings.autoLabels` makes built-in strategies emit distribution labels
  (`auto.int:near-lo`, `auto.list-len:empty`, …) — free histograms of which
  corners of the input space your generators actually visit.
- `renderReport(r, format)` emits text, JSON, JUnit, or GitHub annotations.

**Example database.** Failures persist per test id and replay first on the
next run. The default is a directory-based store with atomic writes, a
multi-entry LRU corpus, and automatic pruning of stale entries; factories
include `inMemoryDatabase`, `multiplexedDatabase(local, shared)` for
shared-CI setups, and `readOnlyDatabase`. A secondary corpus of high-scoring
non-failures lets targeted runs resume where they left off.

## Stateful testing

Rule-based state machines: an `initial: Strategy[S]`, rules with argument
strategies and preconditions, and an optional per-step `invariant` that
catches transient mid-sequence violations a final-state check would miss.
The initial state is part of the recorded choice sequence, so the shrinker
minimizes it alongside the rule selections.

- **Bundles** (`Bundle[S, V]`) give rules typed value flow — rules produce
  into and consume from a pool, with auto-preconditions when the pool is
  empty and shrinkable consumption.
- **Symbolic refs** (`producingRule` / `consumingRule` / `SymRef[V]`) add
  identity-preserving, dependency-respecting value flow: a consumer is
  auto-disabled until its producer has run, and shrinking respects the
  dependency with no extra shrinker work.
- Model-based comparison against a reference implementation falls out of the
  same mechanism.

## Verification toolkit

- **`isLinearisable`** — a Wing-Gong linearisability checker over recorded
  concurrent histories, with memoization, a best-partial-witness (the longest
  valid prefix of any attempted ordering), and the first diverging operation.
- **`parallelCheck`** — a thread-based runner over the linearisability
  checker where jitter delays are drawn from the choice sequence, so the
  shrinker pulls the *schedule* toward the minimal pattern that exposes the
  race. Racy failures are reported as flaky — the correct diagnosis for
  nondeterminism.
- **`bmcCheck`** — bounded model checking for stateful machines: enumerates
  every enabled rule firing breadth-first to a depth bound. A pass is a
  *verification* claim ("the invariant holds for every plan of length ≤ d"),
  not a sampling result.
- **`bisim`** — observational equivalence between two state machines by
  lock-step BFS over state pairs, returning a distinguishing plan when they
  diverge. The use case: a reference implementation vs. an optimized one, up
  to the depth bound.

## Targeted and coverage-guided generation

`target(score)` inside a property turns random testing into search: after the
random phase, a hill-climber (log-scaled deltas) and a simulated-annealing
escape drive the score upward, and the Pareto front persists across runs.
Set `Settings.coverageGuided = true` and per-example **coverage delta**
becomes another objective through the same machinery — instrument procs under
test with the `{.cover.}` pragma (an 8192-edge AFL-style bitmap; zero cost
unless coverage recording is switched on).

## Fuzzing

Three layers, all sharing the typed choice IR — the default mutation mode is
schema-aware (structure-preserving), with raw byte mutation available.

**In-process.** `fuzzOnce(s, prop, bytes)` makes any property a
libFuzzer/AFL entry point; `fuzzWith(s, prop, settings)` runs the built-in
coverage-guided loop over it.

**External binaries.** `fuzzBinary` is the one-liner:

```nim
let report = fuzzBinary(
  bytes(),
  @["./parser"],
  FuzzSettings(maxIterations: 100_000),
  ResourceLimits(perRunTimeout: initDuration(seconds = 1)))

echo report.coverageHits, " edges; ", report.irCrashes.len, " crashes"
exportCrashes("./crashes", report, bytes())
```

Under it sits a composable `Target[T]`: pluggable input delivery (`stdin`,
argv file, env var), crash oracles (signals, sanitizers, exit codes, stderr
patterns), per-run resource limits, and `differentialTarget` to fan one input
across N implementations and compare. Coverage comes from a small vendored C
runtime (`nelli_cov.c`) linked into the target — clang and gcc sancov
backends, atomic dump on exit *and* on fatal signals, with recipes for
C/C++, Rust, and Nim targets in `docs/fuzz/USAGE.md`.

**Corpus management.** Corpora persist through the example database, keyed by
a persist key plus a target id — rebuild the binary and the corpus re-keys
cleanly instead of replaying against a stale coverage map. `importCorpusDir` /
`exportCorpusDir` / `exportCrashes` interoperate with AFL- and
libFuzzer-style corpus directories; every crash exports as exact
replayable bytes.

## Symbolic execution

```nim
import nelli/symex

proc classify(n: int) =
  if (n mod 3) == 0 and n > 0:
    symexTarget("triple")

let r = symexFind(classify, tLabel("triple"))
doAssert r.status == sxSat
echo r.witness[0]           # e.g. 3 — a solver-found input reaching the label
```

`symexFind` compiles the proc's body to SMT and asks Z3 for an input that
reaches a **target**: a named label, an assertion violation, an index error,
a field defect, a nil dereference, or a raised exception (optionally filtered
by type). Answers are honest four ways: `sxSat` (with a concrete witness),
`sxUnsat` (a proof of unreachability up to the configured bounds),
`sxRaised` (the path raises before reaching the target), or `sxUnknown`.

**Language coverage.** The walker handles a large fragment of Nim:
bit-precise integers (with overflow, div-by-zero, and range checks modeled as
targets), IEEE floats including `NaN`/`Inf`/`-0.0` with bit-exact witnesses,
strings under a byte-faithful model (indexing, slicing, search, split/join,
case conversion, `parseInt`, regex membership), arrays, seqs, tables, sets,
tuples, objects and variants, exceptions (`raise`, `try`/`except`/`finally`,
the exception hierarchy, defects), generics (per-instantiation caching,
`distinct` with borrowed operators, concept constraints, `static` params),
closures and bounded higher-order functions, and `ref`/`ptr` with a logical
heap (allocation freshness, aliasing, nil-dereference detection, bounded
recursive-structure walks). Templates and macros are walked post-expansion.
Loops and recursion are k-bounded (`maxLoopUnwind`, and related budgets).

**Routine coverage.** `func` walks identically to `proc` everywhere the
walker resolves a callee: borrowed operators (`{.borrow.}`), proc-as-value
captures (`let g = someFunc`), and string-typed first-parameter
disambiguation all accept a `func` symbol, not just `proc`. There is one
routine-kind vocabulary underneath, so a future routine kind is a one-line
change rather than a fresh audit.

**Operand shape invariance.** Compound operands of comparison, arithmetic,
bitwise, and unary operations — `(pos and capMask) <= pos`, `not (x and y)
== 0`, a call result feeding either side — prove to the identical verdict
and witness as the same expression with the operand let-hoisted first. The
parser atomizes operands through one chokepoint ahead of SMT lowering, so
`lower`/`lowerBool` only ever see atoms; short-circuit `and`/`or` and
`while`-guard conditions are the two deliberate exceptions (short-circuit
evaluation order and loop-guard re-evaluation semantics require the
compound form). Practically: any defensive `let tmp = expr` you added around
a compound operand to work around shape-sensitive lowering is no longer
necessary — it still works, with the identical verdict, but you can drop it.

**Soundness stance.** Anything the walker cannot model degrades to a
*classified* `sxUnknown` — never a native crash, never a silent wrong answer.
Mark deliberately-opaque procs with `{.symexOpaque.}`: the walker treats them
as uninterpreted, keeps the path, and reports uncertainty instead of an
unsound proof. Budgets are tuned through `withSymexSettings`:

```nim
const budget = withSymexSettings() do (s: var SymexSettings):
  s.maxClosureInlineCount = 1
let r = symexFind(myProc, tLabel("captured"), budget)
```

**Test adequacy.** `assertCoveredBy(fn, target, testFn)` verifies that a test
actually exercises a target — if symex proves the target reachable but your
test never hits it, the assertion fails with the target's name. Use it to
keep "this test covers the overflow branch" true as the code evolves.

**Symex × property testing.** The two engines meet at the runner:

```nim
let report = symexForAll(integers(0, 1000), handle, db)
```

runs symex over the property first — auto-discovering every target in the
body, solving each (cache-first, content-addressed by the proc's IR), and
injecting the witnesses as seeds ahead of the random phase — then falls
through to normal PBT, so a solver-found failure still gets shrunk to
minimal by the same shrinker. Findings appear on the report as
`symexFindings`, with provenance. The layers are also available separately:
`symexFindAllWitnesses` (discover + solve + cache, audit trail only) and
`forAllWithSymexSeeds` (inject explicit seeds).

Worked examples live in `examples/` — the basics (`symex_simple.nim`),
out-of-bounds discovery (`symex_oob.nim`), solver-constructed tables
(`symex_table.nim`), loop bounding and the three honest responses to
`sxUnknown` (`symex_loops.nim`), the `{.symexOpaque.}` extension seam
(`symex_stdlib_model.nim`), and test-adequacy checking
(`symex_assert_covered.nim`).

**Upgrading.** The witness/verdict cache and `symexCacheKeyForFn` are
content-addressed by the walker's canonical form, so a walker version that
changes canonicalization changes cache keys, not verdicts. Version 73's
operand shape-invariance guarantee (above) is one such change: it renumbers
positional local slots for any program with a compound operand of a
non-short-circuit operation, which is most programs with more than a trivial
expression — expect broad, one-time cache staleness the first time you run
against walker 73 or later, resolved automatically by re-solving and
re-caching. No verdict or witness content changes.

## Higher-order tooling

- **Law packs** — `eqLaws`, `ordLaws`, `semigroupLaws`, `monoidLaws` return
  named properties, so a failure points at the exact broken law.
- **Metamorphic testing** — `metamorphic(s, prop, transform, relation)`,
  the `unchangedUnder` equality specialization, and `metamorphics` for
  multi-transform fan-out.
- **Property mining** — supply inputs, a function under test, and a template
  library of candidate invariants; the miner reports which invariants always
  held, for human review (Daikon-style).
- **Mutation testing** — `mutantsOf(...)` walks a proc body and emits one
  mutant per mutation site (`<` → `<=`, flipped booleans, zeroed literals,
  …); the scoring loop counts which mutants your property kills. Survivors
  are test gaps.
- **JSON Schema** — `strategyFromJsonSchema(schema)` compiles a schema
  (`type`/`enum`/`const`/bounds/`properties`+`required`/`items`/`oneOf`) to
  a `Strategy[JsonNode]`.

## Development

```bash
nimble test        # full suite
# or, in the project's dev container (Nim + Z3 preinstalled):
scripts/runtest.sh tests/tsmoke.nim
scripts/dt-bounded.sh c tests/tsymex_phase1_arith.nim   # hard-kills hung solver queries
```

`milpa fetch` materializes dependencies and generates `nim.cfg`.
Design notes and ADRs live under `docs/`.

## License

Apache License 2.0 © Corey Leavitt
