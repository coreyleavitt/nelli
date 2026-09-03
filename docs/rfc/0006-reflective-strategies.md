# RFC — reflective strategies: give `Strategy[T]` an inverse

- **Status:** draft — seeded 2026-09-03 from the post-0005 architecture survey;
  `/architect` round 1 applied 2026-09-03. §7 carries the one open fork; §8 is
  the slice plan. Not yet cleared for `/tdd`.
- Category: core
- Size: L
- Value: critical
- **Depends on:**
  - RFC-0010 (config-discipline) — soft. §8's S0c and S1 both add `Settings`
    fields; 0010 is rewriting the defaults policy those fields must follow.
    0006 can start before 0010 lands, but the settings-touching slices should
    not.

Size was `M` in the seed. Round 1 raised it to `L`: the seed's propagation
story covered `strategy.nim`'s combinators only, and the two surfaces that
actually produce most user strategies — `derive.nim`'s `arbitrary(T)` and the
`given` DSL's multi-binding macro — need parse *synthesis*, not field
propagation (§3.2). That is roughly half the work and it was invisible.

## §0 — Thesis

`Strategy[T]` is `{run, display, constraintDigest}` (`strategy.nim:76-91`).
It knows how to turn choices into a value. It has no idea how to turn a value
back into choices.

That single missing direction is the root cause of four documented defects and
one blocked capability. They have been fixed, worked around, or given their own
enum value one at a time.

**Round-1 correction.** The seed claimed "none of them is independently
fixable." That is too strong and the RFC does not need it: the *diagnostic*
halves of symptoms 2 and 4 are independently fixable today (the DB's F6
per-entry metadata, `db.nim:54-70,167-170`, can carry the strategy's
`constraintDigest` and turn a silent prune into a reported one). What is not
independently fixable is the *repair* — turning a stale witness back into a
live one — which is the inverse and nothing else.

## §1 — The symptoms

### 1. Explicit examples cannot shrink

`engine.nim:229-232` states it plainly: *"we don't shrink them (no choice
sequence to shrink)"*, and `phases.nim:89-91` reports `choices: @[]`. A user
pins the one input that matters most and gets the *least* engine support for it.

Note this is documented **intent**, not merely a capability gap — the comment
reads "the user said 'this exact input matters'." An inverse makes shrinking
*possible*; whether to do it is then a policy question, resolved in §6.6.

### 2. The regression corpus degrades on a generator edit — three ways, and the worst one is silent

The seed described a single mechanism (replay raises `Overrun`, `dbReusePhase`
prunes). **That is wrong, and the truth is worse.** `drawInteger`'s replay arm
is `value = clamp(ds.takeReplay(ckInteger).intVal, min, max)`
(`datasource.nim:247`); floats coerce (`:201`). Replay validates admissibility
only for strings and bytes (`:307-310`, `:359-368`). So a generator edit lands
in one of three regimes:

| Edit | What actually happens |
|---|---|
| **Widen a bound** | Every stored value stays admissible. Replay reproduces it exactly. **The witness survives.** The seed's headline example was false. |
| **Narrow a bound; reorder two same-kind `given` bindings** | No `Overrun` — kind matches, value clamps. The witness replays as a **different value**, silently, through the wrong clamp window. If it still falsifies, it is *kept and reported as a reproduced regression* — built from a garbage read. **Silent corruption.** |
| **Add or remove a draw; change a draw's kind; break a string's charset or a byte-run's length** | `Overrun` (`datasource.nim:120-127`). `dbReusePhase` reads that as staleness and calls `removeMany` (`phases.nim:66-84`), with no diagnostic. **Silent deletion.** |

The third regime is the seed's story and it is real. The second is the one that
should worry us more: the engine reports a green replay of a witness it has
quietly reinterpreted. Note also that `ekRejected` counts as stale alongside
`ekPassed` (`phases.nim:80`), so a `filter` that rejects on replay prunes too.

**This costs a consuming team more than it looks.** Generator churn is not an
occasional event in an application under active development — it is continuous,
because generators track types that are still being designed. So the "failures
replay across runs" promise degrades exactly when the application is moving
fastest, and recovers only once the code stops changing. The regression DB is
weakest in the phase it was built for.

An inverse fixes all three regimes the same way: store the *value*, re-parse it
through the *live* strategy, and prune only when the value is genuinely no
longer generatable — with a diagnostic saying so. (§7 is the fork about what it
costs to store a value.)

### 3. An outside typed value cannot enter the shrinker

A production payload, a customer bug report, a value pasted from a log — there
is no door. The shrinker only minimizes sequences it recorded itself.

**Round-1 correction.** A *byte-level* door already exists and the seed's AFL
example was wrong: `newReplaySourceFromBytes` / `bytesMode`
(`datasource.nim:67-75`) feeds externally-mutated raw bytes into typed draws,
and `importCorpusDirAsIR` (`fuzz.nim:2605`) ingests AFL/libFuzzer corpora
through it. The missing door is for **typed values**, which is the one the
production-payload and pasted-log cases need.

For a consuming team this is the single most-wanted workflow nelli does not
have: *production handed us this input, minimize it.* Today the answer is to
hand-write a strategy that happens to reproduce the value, which is the manual
shrinker the library's whole thesis exists to abolish.

### 4. Symex witnesses replay positionally, and the guard rail is dormant

Witnesses are linearised via `renderAsChoices` (`symex.nim:69-144`) and re-fed
positionally.

**Round-1 correction, twice over.** First, the seed cited `sfReplayMiss`
(`engine/types.nim:29-36`) as a failure mode "first-class enough to have its own
status." It has a *declaration*, one no-op case arm (`symex.nim:282`), and a
test asserting the enum constants are distinct. **It is never emitted anywhere
in `src/`** — B5 explicitly descoped the emitter
(`tests/tsymex_phase14_b5_replaymiss.nim:3-11`). It is a reserved status, not
evidence of a diagnosed defect.

Second, the seed said an inverse means "the skew cannot arise." Too strong: the
symex cache stores `witnessChoices`, not values (`symex.nim:232`,
`engine/types.nim:51`), so parse output goes stale on the next strategy edit
exactly as `renderAsChoices` output does — the skew moves to cache-save time.
Eliminating it needs value-level *symex-cache* entries, which §5 scopes out.
What the cache key already covers is `constraintDigest` +
`renderAsChoicesVersion` (`symex.nim:289-293`); the residual class is a
draw-shape change with an unchanged digest — reachable through `filter`, which
drops the digest entirely (`strategy.nim:261-265`).

**But the real finding here is not a symptom at all.** `renderAsChoices` *is a
value→choices function that already exists* — type-directed over bool, floats,
ints, string, array, seq, HashSet, Table, tuple, enum, object and variants, with
the continue-boolean protocol and its own version constant. Its defect is that
it is **strategy-blind**: it hardcodes `sxIntMin..sxIntMax` for every integer
(`symex.nim:82`), `p = 0.5` for every bool, full-Unicode intervals for every
string. It duplicates the strategy's structure instead of deriving from it, and
*that duplication is the skew*.

So symptom 4 reframes: `parse` has an existence proof, a working reference
implementation to port, and a deletion target. `renderAsChoices` is also the
right parity oracle for testing parse on derived shapes (§8, S4).

### 5. The fuzzer cannot recombine at the value level — an enabler, not a fix

Crossover operates on choice IR (`fuzzir.nim`). Structure-aware, but blind to
the value; splicing two valid values is not expressible. `parse` *enables* this;
it does not deliver it, and §5 scopes it out. The honest count for §9 is
therefore **three fixes, one partial fix, one enabler** — not "five defects."

## §2 — Mechanism

Add an optional fourth field:

```nim
Strategy*[T] = object
  run*: proc(src: var DataSource): T {.closure.}
  parse*: proc(t: T, sink: var seq[ChoiceNode]): bool {.closure.}   # new
    ## Append the canonical choice encoding of `t` and return true, or
    ## return false with `sink` restored to its entry length. `nil` means
    ## this strategy has no inverse. See §4 for the laws.
  display*: proc(t: T): string {.closure.}
  constraintDigest*: string
```

The seed wrote `sink: var ChoiceRecorder`. **`ChoiceRecorder` does not exist
anywhere in the tree** — the seed invented a type without flagging it as new.
It is not needed: the output is exactly what the DB stores, what `evalReplay`
takes and what `shrink` takes, namely `seq[ChoiceNode]`. Spans are *not* part
of parse's output — the shrinker re-derives them by replaying (`tryFalsifies`
returns `ds.spans`, `shrinker.nim:87-115`), so `deleteSpansPass` works on
parse-origin sequences for free. That deletes most of the imagined recorder.

**Failure must restore the sink.** `oneOf`'s parse tries branches in turn and a
declined branch may have half-written. The contract is one sentence and the
implementation is `let mark = sink.len` / `sink.setLen(mark)`.

### 2.1 The transposition, stated

Goldstein & Pierce's construction needs the generator to be *reified syntax* an
interpreter can walk in both directions. nelli deliberately compiled that away:
`run` is an opaque Nim closure, and `newStrategy` is a public escape hatch. Full
reification is off the table without abandoning both.

So the transposition is: **the combinator constructor is the reified level.**
Each constructor builds `run` and `parse` in lockstep over the same captured
constraints, so the two directions cannot drift structurally. A "matching-mode
`DataSource`" — the tempting alternative — cannot work: when `lists.run` calls
`drawBoolean(0.9)` for a continue-bit, only the *combinator* knows the answer is
`residual.len > 0`. That decomposition knowledge is not visible to the source.

The unification the seed was reaching for lives one level down. Every `drawX`
records a node with constraints; every parse must emit a node with *identical*
constraints or replay misaligns. Centralize that parity in an emit family
mirroring the draw family:

```nim
proc emitInteger*(sink: var seq[ChoiceNode], v, min, max, shrinkTowards: Int128): bool =
  ## Append exactly the node `drawInteger` would have recorded for `v`, iff legal.
  let c = IntConstraints(min: min, max: max,
                         shrinkTowards: clamp(shrinkTowards, min, max))
  if not c.permits(v): return false
  sink.add ChoiceNode(kind: ckInteger, intVal: v, intC: c)
  true
# emitBoolean, emitFloat, emitBytes, emitString — same shape.
```

`choice.nim:59-139` already has the legality half (`permits` per kind) and the
validated constructors; parse is where that machinery finally earns its keep.
Five chokepoints enforce constraint parity instead of ~30 combinators each
getting it right by hand.

**Metadata fidelity is load-bearing, not cosmetic.** Shrink passes read
constraint windows off the candidate nodes themselves — `lowerIntegerAt` uses
`intC.shrinkTowards`, `lowerStringAt` uses `strC.intervals`
(`shrinker.nim:117-151`). `renderAsChoices` is the cautionary precedent: its
degenerate full-range windows would make "shrinkable explicit examples" shrink
measurably *worse* than random-phase ones — the exact metric §8's S0 introduces.
Parse must emit real windows, and unforced nodes wherever the constraints admit
shrinking (weighted `integers` records `wasForced = true`, which the shrinker
skips; parse must not copy that).

### 2.2 The `display` precedent is real but weaker than the seed claimed

`display` is the right shape — an optional type-indexed per-strategy function
that combinators carry forward where they can and drop where they cannot
(`strategy.nim:79-85`). But the seed cited it as a *discipline that works*, and
the record says otherwise:

- `filter` propagates `display` and silently **drops `constraintDigest`**
  (`strategy.nim:261-265`).
- `oneOf` inherits the **first non-nil** branch's display
  (`strategy.nim:171-177`) — tolerable for rendering, a correctness bug if
  mirrored for `parse`.
- The variadic `map` macros drop everything.
- **`constraintDigest` was never wired into `derive.nim` at all** — every
  derived strategy has an empty digest today (`command grep -c constraintDigest
  src/nelli/derive.nim` → 0; all 10 hits in the tree are in `strategy.nim`).

That last one is the strongest single piece of evidence in this RFC: the
previous optional field went in, missed the largest surface, and nobody noticed.
`parse` will meet the same fate unless derive-side synthesis is an explicit,
scheduled slice. Hence §3.2 and §8's round 3.

## §3 — The inverse surface

### 3.1 Combinator inventory

"Every built-in combinator either propagates it or explicitly declines" is 27
public surfaces in `strategy.nim` plus four more elsewhere — and three of them
are **macros that must generate parse code**, not copy a field.

| Constructor | Site | Decision |
|---|---|---|
| `newStrategy` | strategy.nim:97 | **decline** — opaque; public escape hatch |
| `displayWith` | :102 | propagate (object copy) |
| `just` | :130 | invert; needs `==` on `T`; emits nothing |
| `sampledFrom` | :134 | invert; needs `==`; duplicate items → first index is canonical |
| `sampledFromWhere` | :143 | invert; index into the *filtered* subset |
| `oneOf` | :160 | **hard** — synthesize swarm mask, then branch-trial with rollback |
| `frequency` | :191 | **hard** — re-synthesize unbiased selector inside the chosen weight bucket; weight-0 branches → false |
| `map` (unary) | :236 | **decline** (no general inverse of `T → U`) |
| `map` macro (positional product) | :303 | **synthesize** — macro must emit a parse lambda |
| `map` macro (named product) | :360 | **synthesize** |
| `mapWithDisplay` | :246 | decline |
| `filter` | :254 | **easy** — `s.parse(t, sink) and pred(t)` |
| `recursive` | :267 | propagate iff `extend` does; beyond `maxDepth` → false |
| `enums` | :287 | invert via `sampledFrom` |
| `flatMap` | :390 | **decline** — cannot recover the left `T` from the final `U` |
| `flatMapWithDisplay` | :402 | decline |
| `integers` (± weights) | :410 | invert; emit **unforced** nodes (§2.1) |
| `lists` | :451 | invert; mirror the documented 2N+1 protocol |
| `bytes` | :520 | **broken by default** — it is `lists(integers).map(...)`, so it inherits `map`'s decline. Must be reimplemented or given `mapInv`. This is the fuzzer's flagship input type. |
| `booleans` | :528 | trivial |
| `tables` | :534 | invert; canonical order required (hash order is undefined) |
| `sets` | :562 | as `tables` |
| `bitsets` | :586 | trivial |
| `arrays` | :595 | trivial |
| `strings` (ASCII / IntervalSet) | :608, :619 | invert with range check; **invalid UTF-8 → false** (see §4.4) |
| `floats` | :632 | invert; bit-pattern fidelity (`choice.nim:229` compares by bits) |
| `arbitrary(T)` | derive.nim:350 | **synthesize** — see §3.2 |
| `stateful` | stateful.nim:99 | **decline, permanently** — final state `S` does not determine the command sequence |
| `strategyFromJsonSchema` | jsonschema.nim:20 | mostly invertible; object case uses `newStrategy` |
| `given` N≥2 tuple | dsl.nim:90-119 | **synthesize** — see §3.2 |
| `rule` / `producingRule` / `consumingRule` | stateful.nim:42,78; symbolic.nim:28,49,73 | decline — arg strategies are swallowed into `runStep` |

Genuinely un-invertible: `map`, `flatMap`, `newStrategy`, `stateful`, and
rule-embedded strategies. Everything else is mechanical.

### 3.2 The two synthesis surfaces — half the work, absent from the seed

Field propagation does not reach the two places most user strategies come from:

**`derive.nim` (511 lines).** `arbitrary(T)` emits raw `Strategy[T](run: ...)`
literals down ~10 paths, and routes range/`Natural`/`Positive`, `distinct`,
`float32` and `Option` through **`map`** (`derive.nim:365-458`) — which
declines. So under propagation-only, every refinement type and every derived
type gets `parse = nil`. The macro must emit an un-builder per path: field-wise
decomposition, discriminator-first for variants, nil-check for ref leaves. Note
the derive `map` paths are all *invertible* maps, so `mapInv` (§6.4) must exist
before derive can use it — an ordering constraint on §8.

**`dsl.nim` (`given` with N≥2 bindings).** Emits an inline `newStrategy` tuple
closure (`dsl.nim:90-119`). No field to propagate. This matters because §1.2's
own worked example — "reorder two `given` bindings" — flows through exactly this
macro, and §1.1's `examples` clauses are DSL surface too. Without DSL synthesis,
the two symptoms the RFC leads with are unfixed for DSL users, who are all users.

## §4 — Laws and contracts

### 4.1 The round-trip law, stated precisely

For all `t` in parse's domain:

> `parse(t, cs)` returning true implies
> `run(newReplaySource(cs)) == t`.

Three qualifications the seed left implicit:

- **Replay mode, not generation.** `run` is not a pure function of choices in
  generation mode: weighted `integers` consumes `nextRoll`, which is drawn from
  the RNG and deliberately *not recorded* (`datasource.nim:104-109`). Replay is
  independent of bias, weights and RNG, so the law is well-formed there and only
  there. This is also why parse targets the *replay* shape — which every
  combinator already documents.
- **Direction.** The converse is **false and must not be asserted**: encoding is
  many-to-one (swarm masks, weight buckets, forced positions, duplicate
  `sampledFrom` items), so `parse(run(cs)) ≠ cs` in general. Parse emits one
  *canonical* preimage.
- **Equality.** The law needs `==` on `T`, which `Strategy[T]` does not
  currently require, and which `just`/`sampledFrom` parse need independently.
  For `ref` types Nim's `==` is identity, so round-trip is unstatable for them
  as written — see §4.4.

### 4.2 Canonicality is a requirement, not a nicety

DB dedup is structural `==` on choice sequences (`db.nim:400-424`) and the symex
cache is content-addressed. Two encodings of one value break both — the sorted
iteration in `renderAsChoices` (`symex.nim:108-123`) exists for exactly this
reason. Parse must therefore emit a *stable, shrink-friendly* preimage:

- `oneOf`: all-branches-enabled mute mask, then the first branch whose parse
  succeeds.
- `frequency`: lowest selector value inside the chosen branch's bucket.
- `tables` / `sets`: iterate in sorted key/element order.
- everywhere: unforced nodes where constraints admit, real constraint windows.

This gives the stronger idempotence `parse ∘ run ∘ parse = parse`.

### 4.3 A wrong `parse` is silent — so verify at the door

Because integer replay clamps and float replay coerces (§1.2), a buggy `parse`
replays to a *different value with no error*. The failure mode is: ingest
production payload `t`, engine actually runs `t' ≠ t`, property passes, user is
told their production input is fine. Unacceptable.

**Contract:** every ingestion and every DB save runs the round-trip check once
and raises on mismatch. Cost is one replay per call — negligible at these call
sites, and it is the only thing standing between a parse bug and a false green.

### 4.4 Values that cannot round-trip

Named so they get a designed answer rather than a surprise:

- **`ref` types** — `==` is identity; a rebuilt value is never `==` the
  original. Derived ref strategies are common. Structural comparison for the law
  is required, or refs are declared out of parse's domain.
- **Cyclic / aliased values** — generated refs are acyclic by construction, but
  an *ingested* value can be cyclic or a shared DAG. Parse must not loop, and
  aliasing is not reconstructible.
- **Invalid UTF-8** — unrepresentable by the `strings` strategies, so a
  production payload containing it parses to false. Note symex uses a
  byte-faithful string model while `strings` is codepoint-based: two string
  models, one inverse.
- **Depth** — an ingested value deeper than derive's `maxDepth` (default 4)
  parses to false.
- **Floats** — NaN payload bits and −0.0 must survive; `choice.nim:229` compares
  by bit pattern.

## §5 — Scope

**In scope.** The `parse` field and the `emitX` primitive family; propagation
through every combinator in §3.1; synthesis in `derive.nim` and `dsl.nim`
(§3.2); `mapInv` / `flatMapInv`; the round-trip and canonicality laws as nelli's
own acceptance properties; shrinkable explicit examples; the typed-value
ingestion door (`minimize`); replacing `renderAsChoices` with strategy-derived
parse.

**Out of scope, named so the boundary is explicit.** Value-level fuzz crossover;
value-level entries in the *symex* cache (§1.4); the assurance record's
value-level evidence; a shrinker representation change (§8's S0 may spawn one).

**Conditionally in scope — see §7.** Value-level persistence in the example DB,
which is what actually fixes symptom 2, and which needs a `T` codec that does
not exist.

## §6 — Design decisions closed in round 1

**6.1 Partiality: best-effort nilable field.** The seed called this "the central
design fork." It is closed. `parse: proc(...): bool`, nil when absent, plus
`invertible*[T](s: Strategy[T]): bool = s.parse != nil` and curated errors at
the ingestion door. Every type-level alternative was considered and fails:

- *`Strategy[T; Inv: static bool]`* — viral through `forAll`, all of
  `engine/phases.nim`, stateful, fuzz, symex and the DSL's `typeof(valueType(s))`
  recovery; and it breaks heterogeneous composition, since
  `oneOf(openArray[Strategy[T]])` could no longer mix an invertible branch with
  a non-invertible one — which is exactly what real suites contain.
- *`InvertibleStrategy[T]` distinct* — doubles the combinator matrix (what does
  `map` on it return?).
- *concept* — concepts constrain types; invertibility is per-*value* here.
- *variant object* — isomorphic to the nil check, plus construction churn at
  every literal.

The decisive argument: **the static claim would be false anyway.** `filter`'s
parse is `pred(t) and inner.parse(t, sink)` — dynamically partial by nature. A
type asserting "invertible" cannot promise parse succeeds on a given value. The
guarantee that matters is the round-trip *law*, which is dynamic and checkable
where it actually lives (§4.3 and the acceptance suite).

**6.2 The hard cases are `flatMap` and `oneOf`, not `filter`.** The seed had
this backwards. `filter` inverts trivially — acceptance rate is irrelevant
backwards, since no rejection sampling happens in that direction. §3.1 records
the corrected classification.

**6.3 Two fields, plus a written facet convention.** §4 of the seed asked "two
ad-hoc fields or one extension mechanism?" Answer: two fields. A generic facet
table in Nim means `Table[string, RootRef]` plus casts — dynamic lookup, string
keys, no static typing, strictly worse than fields at N=2. The *mechanism* is
the convention `display` already follows, which should be written down once in
`strategy.nim`'s module doc: a facet is an optional type-indexed closure; nil
means absent; combinators propagate where a lawful lifting exists and drop with
a documented reason where none does; `xWith`-style re-attachment downstream.
Then fix the three propagation bugs §2.2 found, since the convention is only
worth writing if it is followed.

**Corollary that stops the next round of field creep: serialization never
becomes a `Strategy` field.** A codec must be *strategy-independent* to survive
generator edits — that is the entire point of symptom 2. Putting it on the
strategy would re-key the stored value to the thing that keeps changing. It
belongs in a `Codec[T]` sibling of `arbitrary(T)`.

**6.4 `mapWithParse` → `mapInv`.** The user does not supply a parse
(`U → choices`); they supply the inverse of `f` (`U → T`), from which the
combinator derives parse. Name it for the argument:

```nim
proc mapInv*[T, U](s: Strategy[T], f: proc(x: T): U,
                   inv: proc(y: U): Option[T]): Strategy[U]
proc flatMapInv*[T, U](s: Strategy[T], f: proc(x: T): Strategy[U],
                       proj: proc(y: U): Option[T]): Strategy[U]
```

`Option[T]` rather than `bool` + out-param: partial inverses are the norm, and
at this arity purity is free. Users will write these by hand constantly.

**6.5 No error-detail return on `parse` for v1.** During `oneOf`/`recursive`
backtracking, failure is *expected control flow*; building reason strings per
declined branch is wasted work producing misleading diagnostics ("branch 0
failed" when branch 2 succeeded). The diagnosis users need lives at the door
(§6.7): "this strategy has no inverse" vs. "this value is outside its range."
If field-level detail is ever wanted, furthest-failure-point tracking is the
right design and is a compatible later addition.

**6.6 Explicit examples: shrink, and say so.** §1.1's no-shrink is documented
intent, so the policy needs a decision rather than a silent reversal. Report the
**shrunk** value, with the message naming the pinned original — the user pinned
an input to assert something about it, and "your pinned input fails, here is the
smallest input in its neighbourhood that also fails" strictly dominates. Strategies
without parse degrade to exactly today's behaviour.

**6.7 The three workflows, and their API cost.**

- *(a) Shrinkable explicit examples — zero new API.* `examples 42` and
  `forAllWithExamples` are unchanged. `explicitExamplesPhase`
  (`phases.nim:87-127`) tries `s.parse(ex, cs)`; on success it evaluates via
  `evalReplay` and sets `RawFalsification(choices: cs, fromPhase: "explicit")`
  so `shrinkPhase` minimizes it, instead of today's `pcTerminate` with
  `choices: @[]`.
- *(b) Ingestion — one new entry point.*
  ```nim
  proc minimize*[T](s: Strategy[T], value: T, prop: proc(x: T),
                    settings = defaultSettings()): Report[T]
  ```
  Nearly free once (a) lands: it is `forAllWithExamples([value], s, prop)` with
  the random and targeted phases skipped, and the seed-phase pattern already
  exists (`symexSeedPhase`, `runForAllPipelineWithPhases`).
- *(c) Durable DB — zero new API*, behaviour change in `dbReusePhase`. Contract
  sentence: *a stored witness survives any generator edit that keeps the witness
  value in range; it is pruned, with a diagnostic, only when the value is no
  longer generatable.* Gated on §7.

**6.8 Compatibility.** Adding a field to a value `object` with public fields is
**source-compatible** — Nim literals zero-fill, so existing
`Strategy[T](run: ...)` literals in the library, tests and downstream keep
compiling with `parse = nil`. The breaking change is the DB format (v4 → v5),
which older nelli cannot read; chapulin shares corpus directories and runs on
Windows, so that break needs a release note and a version bump, not silence.

**6.9 Two integration points that will otherwise rot.** `concolic.nim:254`
(`classifyStrategyExpr`) classifies strategy *expressions by combinator name* —
`mapInv`/`flatMapInv` are invisible to it and silently degrade symex
transparency to `dkOpaque` unless taught. And replacing `renderAsChoices`
invalidates cached witnesses, so it must bump the version constants that
participate in the cache key (`symex.nim:289-293`) and follow the CR2 pin-test
discipline in `CLAUDE.md`.

**6.10 Citation.** The seed cited "Goldstein & Pierce's reflective generators
(POPL 2023)". Neither the venue nor the pairing is right. The two relevant
papers are Goldstein & Pierce, *Parsing Randomness* (**OOPSLA 2022**), which
gives the free-generator / generator-as-parser duality this RFC transposes, and
Goldstein et al., *Reflecting on Random Generation* (**ICFP 2023**), which gives
reflective generators proper. Falsify (de Vries, 2023) is cited correctly in §8.

## §7 — The open fork — awaiting Corey

**Value-level DB persistence needs a `T` codec, and the codec is plausibly
bigger than this RFC.**

The seed framed the schema question as "store the value alongside choices, or
derive choices on demand from a stored value? The second is smaller but requires
a `T` serializer the library does not have." **That asymmetry is false — both
options require the serializer**, because storing a value alongside choices is
meaningless unless it can be encoded. `serialize.nim` (182 lines) handles
`ChoiceNode` sequences only; `db.nim` entries are `toBytes(seq[ChoiceNode])`
(`db.nim:384`).

And a general `T` codec is a *second full derive macro* mirroring
`arbitrary(T)`: its own versioning, float bit-fidelity, Table-order
canonicalization, `requiresInit` and variant handling, and cross-platform
stability under the Windows legs. That is comparable in size to `parse` itself.

This matters because **symptom 2 is the one this RFC leads with** and it is the
only symptom the codec gates. Symptoms 1, 3 and 4 need no codec at all.

Three ways to go:

1. **Split the codec into its own RFC (0013), make 0006 depend on it, and ship
   0006 without value-level DB persistence.** 0006 delivers symptoms 1, 3 and 4
   end-to-end and stays `L`. Symptom 2 gets the *diagnostic* half now (§0 — F6
   metadata turns silent prunes into reported ones) and the repair half when the
   codec lands. A codec also has an independent second consumer in 0008's
   value-level evidence, so it would be designed against N=2 rather than frozen
   onto this one caller.
2. **Absorb the codec into 0006.** One coherent story, symptom 2 fixed properly,
   but the RFC goes `L → XL` and the load-bearing slice (§8's S1b) ships much
   later behind a large serializer round.
3. **Drop symptom 2 from 0006 entirely** and reframe the RFC around ingestion
   and explicit-example shrinking. Smallest and cleanest, but gives up the
   symptom with the strongest consuming-team argument.

*Recommend (1).* It keeps 0006's load-bearing property first, gives the codec a
second consumer before its interface freezes, and the piece symptom 2 loses in
the interim is the piece that is independently fixable anyway. It does mean
adding an RFC to the 0006–0012 set and re-deriving the board's order, which is
why this is your call and not mine.

## §8 — Slice plan

The seed named slice 1 and then nothing — which meant **no slice produced
`parse`**. Everything in §1 is a consumer of a producer that appeared on no
slice: the definition of a feature that ships green and inert. The plan below
puts the producer and one real consumer in the same round.

**Load-bearing property:** *a typed value that the engine never generated enters
through the real entry point, parses against the live strategy, and shrinks.*
Definition of done for round 1 is an end-to-end run of that through `property` /
`forAllWithExamples`, not a passing unit suite.

### Round 0 — the instrument

The seed made slice 1 a shrink-quality benchmark and asserted step-count budgets
before any baseline existed, which is guessing numbers, not a RED. Split:

- **S0a — evaluation counter.** RED: `ShrinkResult` reports the number of
  `tryFalsifies` calls for a hand-crafted sequence. *Blast radius:*
  `shrinker.nim`, `tests/tshrinker.nim`.
  **Correction to the seed's premise:** `maxShrinks = 500` (`shrinker.nim:411`,
  `<= 0` unbounded, `Settings` default at `engine/types.nim:188`) caps *outer
  fixpoint iterations*, and the loop almost always exits via `best != prev` far
  below 500. The unbounded cost is *inside* one iteration — `deleteSpansPass`
  restarts after every accepted deletion, `lowerIntegerAt` binary-searches per
  node, `lowerFloatAt` runs up to 60 probes per node — and **nothing counts
  property evaluations anywhere.** That, not `maxShrinks`, is the gap.
- **S0b — shrink-quality corpus.** Characterization tests over low-acceptance
  `filter`, dependent `flatMap`, mixed-length `oneOf`, `recursive` at depth.
  Golden minima plus eval-count ceilings recorded from the first measured run.
  Feed hand-crafted sequences straight to `shrink` in the existing
  `tshrinker.nim` style — **not** through `forAll` — which makes every case
  RNG-free, deterministic and fast under podman. Lives in `tests/`; the repo has
  no bench-target infrastructure and inventing one is unjustified scope.
  *Drop the seed's "stateful sequences with bundle dependencies" case* — stateful
  is permanently un-invertible (§3.1), so it is not on this RFC's path.
- **S0c — count-based eval budget** (only if S0b shows pathology). Must be
  count-based, **not wall-clock**: wall-clock is nondeterministic across podman
  and the Windows legs and would violate the repo's determinism discipline.
  *Blast radius:* `shrinker.nim`, `engine/types.nim`, `engine/phases.nim` — and
  it adds a `Settings` field, so it wants 0010 first.

*Honest scoping of the seed's "no measurement, therefore instrument first"
argument:* 0006 does not modify shrink passes, it changes what *enters* the
shrinker. So the baseline's real payloads are (i) the Falsify linear-vs-tree
question, which stands on its own, and (ii) comparing shrink quality of
parse-origin against generation-origin sequences — and (ii) can only be written
*after* parse exists. The benchmark therefore grows in two stages, and the
seed's "all of slice 1 before any of §2" is overstated.

### Round 1 — producer + one consumer, end to end

- **S1a — `parse` field, `emitX` primitives, primitive inverses**
  (`integers`, `booleans`, `floats`, `strings`, `bytes` — the last needs the
  §3.1 fix). Round-trip law test per primitive. *Blast radius:* `strategy.nim`,
  `choice.nim` (read-only), tests.
- **S1b — explicit-example shrinking end-to-end** (§6.7a). *Blast radius:*
  `engine/phases.nim`, `engine/types.nim`, tests. **DoD:** a real `property`
  block with `examples 77`, `given x in integers(0, 100)`, failing, reporting a
  counterexample *below* 77.
- **S1c — `minimize` door** (§6.7b) with the §4.3 round-trip verification and
  the two curated errors. Symptoms 1 and 3 are the *same slice* mechanically —
  an outside value enters as an explicit example — so this is small once S1b
  lands.

### Round 2 — combinator propagation

S2a containers (`lists`/`tables`/`sets`/`arrays`, canonical order per §4.2) ·
S2b choice combinators (`sampledFrom`, `oneOf`, `frequency` — the rollback and
mask-synthesis work) · S2c `filter`, `just`, `recursive`, and the documented
declines · S2d `mapInv`/`flatMapInv`. One module plus tests each.

### Round 3 — synthesis (`derive.nim`, `dsl.nim`)

The round §3.2 exists for, and the one most likely to be skipped. Without it
symptoms 1 and 3 are dead in practice. Needs S2d first (derive's range/distinct/
`Option` paths route through `mapInv`). *Blast radius:* `derive.nim` (511 lines)
+ `derive/detect.nim`, then `dsl.nim` — two slices, not one.

### Round 4 — symex witness re-parse (a round, never a slice)

Replace positional `renderAsChoices` with `strategy.parse`. *Blast radius:*
`symex.nim` (1936 lines), `engine/types.nim`, cache-key version constants, the
CR2 pin-test discipline, `concolic.nim`'s classifier (§6.9), and it crosses the
`symex-mingw` Windows leg. The six `tsymex_r6_*` Linux-hang suites complicate
any red/green read — see the `symex-r6-linux-hangs` memory.

### Round 5 — value-level DB persistence

**Gated on §7.** If (1) is chosen this becomes RFC-0013's consumer round.

### Proof-spike

`parse` is a shared abstraction with four consumers (explicit examples, the
ingestion door, symex replay, later fuzz crossover), so its interface must not
freeze against consumer one. **Spike symex witness re-parse (round 4) during
round 2, throwaway.** It is the right second consumer because it exists today
with real tests, a versioned contract, and a genuinely different call context
(macro-generated, tuple-shaped `given` values) — whereas the DB consumer
additionally needs the nonexistent codec, so it cannot validate anything yet.
`renderAsChoices` doubles as the parity oracle for parse's output on derived
shapes.

### Branch naming

Must be `rfc-*` or the three Windows legs never trigger (`CLAUDE.md`).

## §9 — Why this

Of everything on the post-0005 board, this is the only item that is
simultaneously: a fix for three documented defects plus a partial fix for a
fourth, a prerequisite for value-level evidence in 0008, an enabler for
value-level fuzz crossover, and a single optional field on a type that already
has the precedent for it.

It is also the item peers cannot copy. Hypothesis has the identical
explicit-examples-cannot-shrink limitation and cannot retrofit an inverse onto
its generator model; its 2023–24 typed-IR work and the crosshair backend are the
closest living relative of nelli's model and still route around the problem
rather than through it.

**And the transposition is already half-built in this repo.** `renderAsChoices`
proves a type-directed value→choices function works over nelli's choice IR; its
only defect is that it guesses at constraints instead of asking the strategy
(§1.4). This RFC is that function, done right, and then deleted from symex.
