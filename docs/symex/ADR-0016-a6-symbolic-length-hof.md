# ADR-0016 — A6: symbolic-length `filter`/`map` — model the decidable, soundly degrade the rest

- **Status:** ACCEPTED (2026-06-29)
- **Cluster:** A6 (Phase 16 — language fragments part 2)
- **Feasibility:** decided by a both-backend Z3 probe (5 probes, c+cpp); the
  filter-axiom encoding **hangs** (rc=137), the map-axiom encoding is decidable.
- **Net code change to the engine:** none. A6 is a *scope-confirming* slice —
  documentation + a regression pin. No `symexWalkerVersion` bump (no verdict or
  cache-key change).

## Context

RFC §A6 asks whether the closure-taking HOFs `filter`/`map` over a
**symbolic-length** `seq[T]` can be modeled rather than degraded. The
concrete/bounded case already ships (C4 inline path, length ≤
`seqInlineThreshold` = 8, quantifier-free). The open question is the *symbolic*
length case, where the seq has no numeral length after `simplify`.

Engine representation matters here: `seq[T]` is stored as
`Z3Array[Z3Int, T_sort]` + a `Z3Int` length — **not** `Z3Seq`. Strings are the
only `Z3Seq`-native values (`Z3Seq[Z3Char]`, ADR-0006). This array/seq split is
the crux of every A6 finding.

## Decision

Model only what is decidable and hang-free; keep the sound degrade for the rest.

| Case | Verdict | Mechanism |
|---|---|---|
| `filter`, concrete/bounded | **MODEL** (ships) | C4 inline keep-mask, QF |
| `map`, concrete/bounded | **MODEL** (ships) | C4 inline per-element store, QF |
| `map`, symbolic, capture-free `int→int` | **MODEL** (ships) | `mapArray` (`Z3_mk_map`) — decidable array-map, no ∀ |
| `map`, symbolic, **capturing** closure | **DEGRADE** | `ceUnsupportedHof` → `sxUnknown` (`mapArray` needs a unary FuncDecl; a captured env-leaf has no such decl) |
| `map`, symbolic, non-`int` element via axiom path | **BOUNDED-ONLY** | inline only; axiom path would need `mapArray` sort dispatch (out of A6 scope) |
| `filter`, symbolic length | **DEGRADE** | `ceUnsupportedHof` → `sxUnknown` — see below |

A6 ships **no new encoding**: every MODEL row above already shipped under C4,
and every DEGRADE/BOUNDED row is the correct outcome under Invariant 3.

## Why symbolic-length `filter` stays a degrade (the hang evidence)

The natural encoding is `seqFoldlBody` — a direct-body `seq.foldl`
(`Z3_mk_seq_foldl` + a 2-bound-var `Z3_mk_lambda_const`, the filter body being
`ite(pred(elem), acc & unit(elem), acc)`), the foldl analog of A9's
`seqMapBody`. The probe implemented it inline and measured:

- **Easy-SAT** (`s.len>0 ∧ s[0]>0 ∧ filtered.len>0`): `sat` fast — but only
  because pinning element 0 hands Z3 a near-trivial length-1 witness.
- **Hard-SAT** (`s.len≥2 ∧ filtered.len≥2`, no element hints): **rc=137 (hang)**
  on c AND cpp — `solver.check()` never returns.
- **UNSAT** (`filtered.len > len(s)`, impossible): **rc=137 (hang)** on c AND cpp.

Z3's `seq.foldl` is incomplete for the filter shape the instant the length is
underconstrained — both SAT and UNSAT directions diverge. This is a genuine
solver-incompleteness wall, not a tuning issue.

Two independent blockers, either sufficient:
1. **Solver incompleteness** — proven by the hard-SAT and UNSAT hangs above.
2. **Representation mismatch** — `seqFoldlBody`/`seqMapBody` consume `Z3Seq[E]`,
   but the engine stores `seq[int]` as `Z3Array`. There is no Z3 primitive to
   lift a `Z3Array` to a `Z3Seq`. Bridging would mean rewriting
   `allocateSeqDataRaw`, `seqElemAt`, `storeSeqElem`, `concreteSeqLen` and every
   downstream consumer — a representation change far outside A6.

The probe DID confirm `seqMapBody` over a freshly-built `Z3Seq[BV64]` with a QF
body is hang-free (`sat`, correct witness `s[0]=0x15 → 42`), so the A9 building
block generalizes — but only at the `Z3Seq` level the engine does not use for
`seq[int]`.

## Soundness (Invariant 3)

Every non-modeled case returns `ceUnsupportedHof` → `sxUnknown` — a classified
non-answer, never a false defect and never a hang. Shipping `seqFoldlBody` would
be strictly *worse* than the status quo: it converts an honest `sxUnknown` into a
137 hang, the worst Invariant-3 outcome. Refusing to add it is the sound choice.

## FFI helper — specified, NOT added

For the record (and for a future cycle that changes the seq representation to
`Z3Seq` for specific type slices), the foldl analog of `seqMapBody` would be:

```nim
proc seqFoldlBody*[E, A](accVar: A, elemVar: E, body: A,
                          init: A, s: Z3Seq[E]): A
  ## (seq.foldl (lambda ((accVar A) (elemVar E)) body) init s)
  ## Same shape as seqMapBody but a 2-bound-var lambda + Z3_mk_seq_foldl.
```

It is **not** added to nim-z3 for A6: the hang evidence makes it unsafe for the
general query, and the representation mismatch makes it unusable in the current
engine. `seqMapBody` (nim-z3 `7d11468`) remains the available building block.

## Scope / perturbation

- **In (newly *pinned*, already *behaving*):** symbolic capture-free `int→int`
  map is decidable; symbolic capturing map degrades; symbolic filter degrades.
- **Out (still degrade):** symbolic filter (any element), symbolic capturing
  map, symbolic non-`int` map via axiom path.
- **SUT perturbation:** ZERO. No existing test changes; C4-2/C4-3 stay green.
  A6 adds one new regression file (`tsymex_a6_symlen_hof.nim`) pinning the
  capturing-map degrade that C4 did not cover explicitly.
- **Walker version:** unchanged at "34" (no verdict flip, no new IR, no
  cache-key input change).

## Alternatives rejected

- **Add `seqFoldlBody` and encode symbolic filter** — hangs (rc=137, both
  directions, both backends) and needs a `Z3Array→Z3Seq` rewrite. Rejected.
- **Bounded-unroll symbolic filter at a fixed cap** — would silently truncate at
  the cap (unsound for `filtered.len` reasoning beyond it) and duplicates the
  inline path's job. Rejected; the honest `sxUnknown` is better.
