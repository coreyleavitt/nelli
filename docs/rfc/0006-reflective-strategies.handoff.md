# RFC-0006 reflective-strategies — handoff

- **Stage:** 2 (design review). **Round 1 done** 2026-09-03, on `fable`, four
  lenses (depth, breadth, design & ergonomics, feasibility+liveness).
- **Status:** seed → **draft**. Size raised **M → L**.
- **Blocked on:** the §7 fork — the `T` codec question. One decision, three
  options, recommendation is option (1). Nothing else awaits Corey.
- **Resume:** answer §7, then either `/architect rfc-0006 round 2` or, if you
  want the plan pressure-tested rather than the design, go straight to
  `/tdd` on §8's S0a.
- **Branch:** must be named `rfc-*` or the three Windows legs never trigger.

## What round 1 changed

The seed was structurally right — the missing inverse is real and it is the
right next core RFC — but four of its load-bearing factual claims were wrong,
and roughly half the implementation surface was invisible.

### Premise corrections (verified against the code, not taken on report)

| Seed claim | Reality | Where |
|---|---|---|
| Generator edits make replay `Overrun`, so witnesses get pruned | Integer replay **clamps**; floats coerce. Widening a bound *keeps* the witness; narrowing/reordering silently replays a **different value** and may report it as a reproduced regression. Only add/remove-draw and kind/charset changes overrun. | `datasource.nim:247`, `:201`, `:120-127` |
| `sfReplayMiss` is "first-class enough to have its own status" | **Never emitted anywhere in `src/`.** Declaration + one no-op case arm + a test asserting enum distinctness. B5 descoped the emitter. | `engine/types.nim:29-36`, `symex.nim:282`, `tests/tsymex_phase14_b5_replaymiss.nim:3-11` |
| `filter` is the hard inverse case | `filter` is the *easy* case (`s.parse(t) and pred(t)`). `flatMap` and `oneOf` are hard. | `strategy.nim:254`, `:390`, `:160` |
| "Five defects fixed" | Three fixed, one partially (symex skew moves to cache-save time), one merely enabled (fuzz crossover, scoped out). | §1.4, §1.5 |
| "No door for outside values" | A **byte-level** door exists (`bytesMode`, `importCorpusDirAsIR`). The missing door is for *typed* values. | `datasource.nim:67-75`, `fuzz.nim:2605` |
| `ChoiceRecorder` (in the §2 sketch) | **Does not exist in the tree.** Invented without flagging. Correct sink is `seq[ChoiceNode]` + a rollback contract. | — |
| "The only guard is `maxShrinks = 500`" | That caps *outer fixpoint iterations*, which almost always exit early. The unbounded cost is *inside* an iteration, and **nothing counts property evaluations at all**. | `shrinker.nim:411`, `:396-426` |
| Citation: "reflective generators (POPL 2023)" | *Parsing Randomness* is OOPSLA 2022; *Reflecting on Random Generation* is ICFP 2023. | §6.10 |

### The reframe worth remembering

`renderAsChoices` (`symex.nim:69-144`) **is already a working value→choices
function** — type-directed over bool/float/int/string/array/seq/HashSet/Table/
tuple/enum/object/variant, with the continue-boolean protocol and its own
version constant. Its defect is that it is **strategy-blind**: hardcoded
`sxIntMin..sxIntMax`, `p = 0.5`, full-Unicode intervals. It duplicates the
strategy's structure instead of deriving from it, and *that duplication is the
skew*. So `parse` has an existence proof, a reference implementation to port,
a parity oracle for testing, and a deletion target. The seed filed this under
"symptom" and missed all four.

### The scope that was invisible

Field propagation does not reach the two surfaces that produce most user
strategies:

- **`derive.nim`** — `arbitrary(T)` routes range/`Natural`/`Positive`,
  `distinct`, `float32` and `Option` through **`map`**, which declines. Every
  refinement and derived type would get `parse = nil`.
- **`dsl.nim`** — `given` with N≥2 bindings emits an inline `newStrategy` tuple
  closure. No field to propagate. This is the surface the seed's *own* worked
  example ("reorder two `given` bindings") runs through.

Both need parse **synthesis** in the macro, not propagation. That is round 3 and
about half the work — the reason size went M → L.

**The evidence that this will be skipped if not scheduled:** `constraintDigest`,
the previous optional Strategy field, was never wired into `derive.nim` at all.
All 10 occurrences in the tree are in `strategy.nim`; every derived strategy has
an empty digest today, and nobody noticed.

### Forks closed (do not reopen without new information)

- **Partiality** — best-effort nilable field + `invertible()` + curated door
  errors. Every type-level alternative refuted in §6.1; the decisive argument is
  that a static "invertible" claim would be *false anyway*, since `filter` is
  dynamically partial.
- **Two fields vs. one extension mechanism** — two fields plus a written facet
  convention. A generic facet table in Nim is `Table[string, RootRef]` + casts:
  strictly worse at N=2. Corollary: **serialization never becomes a `Strategy`
  field** (a codec must be strategy-*independent* to survive generator edits).
- **`mapWithParse` → `mapInv`** — the argument is `f`'s inverse, not a parse.
- **Explicit-example policy** — report the shrunk value, naming the pinned
  original. (This reverses documented intent, so it needed a decision.)
- **Canonicality** — a hard requirement, not a nicety: DB dedup is structural
  `==` on choice sequences and the symex cache is content-addressed.

### Still open — the one thing awaiting you

**§7: the `T` codec.** Both DB options need it (the seed thought only one did),
and it is a second full derive macro — plausibly larger than `parse` itself.
It gates symptom 2 *only*; symptoms 1, 3 and 4 need no codec.

1. **Split it into RFC-0013, 0006 depends on it, ship 0006 without value-level
   DB persistence.** ← *recommended*
2. Absorb it into 0006 (→ XL, load-bearing slice ships much later).
3. Drop symptom 2 from 0006 entirely.

(1) keeps the load-bearing property first and gives the codec a second consumer
(0008's value-level evidence) before its interface freezes. It costs an extra
RFC in the 0006–0012 set and re-derives the board order, which is why it is your
call. Symptom 2's *diagnostic* half is independently fixable today regardless,
via the DB's F6 per-entry metadata.

## Liveness

**Load-bearing property:** a typed value the engine never generated enters
through the real entry point, parses against the live strategy, and shrinks.

The seed named slice 1 (a benchmark) and then nothing — **no slice produced
`parse`**. Every symptom in §1 was a consumer of a producer scheduled nowhere.
§8 now puts producer (S1a) and a real consumer (S1b) in round 1, with an
end-to-end DoD: a real `property` block with `examples 77`,
`given x in integers(0, 100)`, failing, reporting a counterexample below 77.

**Proof-spike:** symex witness re-parse, spiked throwaway during round 2. It is
the right second consumer — it exists today with real tests, a versioned
contract, and a different call context. The DB consumer cannot validate anything
until the codec question closes.

## Slice ledger

| Round | Slice | State |
|---|---|---|
| 0 | S0a eval counter | not started |
| 0 | S0b shrink-quality corpus | not started |
| 0 | S0c count-based eval budget (contingent on S0b) | not started |
| 1 | S1a `parse` + `emitX` + primitive inverses | not started |
| 1 | S1b explicit-example shrinking (end-to-end DoD) | not started |
| 1 | S1c `minimize` door | not started |
| 2 | S2a–S2d combinator propagation | not started |
| 3 | derive synthesis, then dsl synthesis | not started |
| 4 | symex witness re-parse (a **round**, not a slice) | not started |
| 5 | value-level DB persistence | **gated on §7** |

Notes for whoever picks this up:

- S0c and S1 add `Settings` fields → they want RFC-0010 first (soft dep,
  recorded in the header).
- Round 4 crosses the `symex-mingw` Windows leg, touches cache-key version
  constants, and must follow the CR2 pin-test discipline. The six
  `tsymex_r6_*` Linux hangs will muddy any red/green read — see the
  `symex-r6-linux-hangs` memory.
- Round 3 needs S2d (`mapInv`) first: derive's range/distinct/`Option` paths
  route through it.
- `concolic.nim:254` (`classifyStrategyExpr`) classifies strategies by
  combinator *name* — new combinators silently degrade symex transparency to
  `dkOpaque` unless taught.
- DB v4 → v5 is a real downstream break; chapulin shares corpus dirs and runs
  on Windows.

## Review ledger

| Round | Model | Lenses | Findings applied | Forks raised |
|---|---|---|---|---|
| 1 | fable | depth, breadth, design, feasibility+liveness | 8 premise corrections, 5 forks closed, inventory table added, slice plan added, size M→L | 1 (§7 codec) |

Round 1 findings were cross-verified against the source before being applied —
the clamp-on-replay, `sfReplayMiss`-never-emitted, `bytes`-via-`map`,
`constraintDigest`-absent-from-derive and `ChoiceRecorder`-nonexistent claims
were each checked directly rather than taken on the agents' word.

**Is round 2 warranted?** Not on the same axis. Round 1 rewrote the premises,
the scope and the plan; a second pass over the same document would mostly
re-litigate closed forks. The useful next reviews are (a) after §7 closes, a
short round on the revised §8 slice boundaries, or (b) skip to `/tdd` S0a, which
is independent of the fork and of nearly everything else in the RFC.
