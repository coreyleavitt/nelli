# SYMEX_PLAN — Phase 15 (language fragments) cycle tracker

> Authored in cycle **Z3f** (RFC-phase15-language-fragments.md; reconciled per
> RFC-phase15-reconciliation.md). One row per implementation cycle across the 9
> clusters (Z, L, F, S, H, E, G, C, R), ordered cheapest-infra → deepest.
>
> **Status** is one of `SHIPPED` (committed + green on `nim c`/`nim cpp`),
> `pending`, or `folded` (absorbed into another cycle). `commit` is the short SHA.
>
> **Reconciliation note:** the RFC's single `Z3` cycle was sub-sliced into
> `Z3a`–`Z3f` (8 mutually-referential changes split for TDD testability); those
> rows replace the monolithic `Z3` row. All cycle homes/paths are corrected per
> the reconciliation doc — consult it before implementing any row.

## Cluster Z — nim-z3 v2.0.0 pin + carryover + cross-cutting infra

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| Z | Z0  | Phase 14 carryover close-out (named-field `map`, constraintDigest) | SHIPPED | 9dd4181 |
| Z | Z1  | nim-z3 v2.0.0 pin bump + grep verification + canary | SHIPPED | 9e7deea |
| Z | Z2  | regression smoke under v2.0.0 (0 drift) | SHIPPED | 9e7deea |
| Z | Z3a | error/severity/settings enum scaffolding | SHIPPED | f195a1f |
| Z | Z3b | `svUninterpRef` + `itUninterp`/`tUninterp` | SHIPPED | b523345 |
| Z | Z3c | `classifyType` char branch + sink/lent strip | SHIPPED | 308a8e7 |
| Z | Z3d | `withSymexSettings` builder + `+` merge | SHIPPED | a473666 |
| Z | Z3e | `cacheKeyRaised` + cache-suffix standardization | SHIPPED | fcecd96 |
| Z | Z3f | author this plan doc | SHIPPED | (this cycle) |
| Z | Z4  | `WalkCtx.found` Option→seq + WalkerStatics/CallFrameCtx records + ADR-0007 | SHIPPED | (this cycle) |

## Cluster L — templates and macros

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| L | L1 | boundary audit — template/macro/`{.dirty.}` SUTs symex soundly | SHIPPED | (this cycle) |
| L | L2 | `untyped` template params — faithfully walked (constraint honored) | SHIPPED | (this cycle) |
| L | L3 | `getAst`/`quote do` — round-trip identity; generic monomorphization; Z smoke | SHIPPED | (this cycle) |

## Cluster F — float

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| F | F0-ADR | author ADR-0005-float-nan-inf.md | SHIPPED | (on disk) |
| F | F1 | type-bridge: float/float32/float64 IR kinds, svFloat32/64 | SHIPPED | (this cycle) |
| F | F2 | float literal lifts (Inf, NaN, -0.0, finite) | pending | |
| F | F3 | arithmetic ops (+ - * / unary-) | pending | |
| F | F4 | comparison ops (< <= == != > >=) | pending | |
| F | F5 | int↔float conversions with range overflow | pending | |
| F | F6 | math-module ops + FP predicates | pending | |
| F | F7 | eval-side bit-exact float witness round-trip | pending | |
| F | F8 | regression smoke; walker `"4"→"5"`; withSymexSettings wiring | pending | |
| F | F9a | array[N, float32/64] element type-bridge audit | pending | |
| F | F9b | seq[float32/64] param: allocate → extract → emitTyAndReader | pending | |
| F | F9c | object-variant arm fields of float32/64 | pending | |

## Cluster S — full strings

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| S | S0-ADR | author ADR-0006-string-codepoint-indexing.md | pending | |
| S | S1 | type-bridge: string → full Z3 String walker; iekStr* stubs | pending | |
| S | S2 | string literal lifts; codepoint/byte divergence | pending | |
| S | S3 | s.len, s[i], s[a..b]; s.high/for-c-in-s classified errors | pending | |
| S | S4 | find, contains, startsWith, endsWith | pending | |
| S | S5 | replace, replaceAll, split, join; maxSplitParts | pending | |
| S | S6a | regex_parser.nim standalone | pending | |
| S | S6b | walker integration: iekStrMatch/iekStrFindRe | pending | |
| S | S7a | bytes(s) UTF-8 BMP encoding; maxBytesEncodingLen cap | pending | |
| S | S7b | Z3-string-theory regression smoke (L+F+S1–S7a) | pending | |
| S | S8 | `&` string concatenation → Z3_mk_seq_concat | pending | |
| S | S9 | toLower/toUpper → seUnsupportedStringOp | pending | |
| S | S10a | $int/parseInt digits-path; explicit unsoundness window | pending | |
| S | S10b | parseInt raises-path fork (depends on E1) | pending | |
| S | S11 | string mutation classified; walker `"5"→"6"` | pending | |

## Cluster H — heap preparation

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| H | H1 | Path refactor (heaps/heapDepth/allocCounters) + ADR-0010 | pending | |

## Cluster E — exceptions

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| E | E1 | IR extension + walker handler-stack plumbing | pending | |
| E | E2a | structural sxRaised cascade (stub arms, cache key, sfRaised) | pending | |
| E | E2b | real walk(isRaise) semantics + InternalVerdict | pending | |
| E | E3 | try/except matching by type + inter-proc propagation stub | pending | |
| E | E4 | exception type hierarchy (subtype catch, static ExnTypeTable) | pending | |
| E | E4a | dynamic user-exception hierarchy (getImpl walk) | pending | |
| E | E5 | finally semantics | pending | |
| E | E6 | Defect modeling (isDefect; defectExclusions; OQ4) | pending | |
| E | E7 | regression smoke; walker `"6"→"7"` | pending | |
| E | E8 | getCurrentException/Msg (uses svUninterpRef from Z3b) | pending | |

## Cluster G — generics

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| G | G0-ADR | author ADR-0008-generic-instantiation.md | pending | (file on disk) |
| G | G1a | IR: isGenericCall, mkGenericCall, dispatch stubs | pending | |
| G | G1b | parser: gatherTypeSubst, parseCalleeImpl, emitGenericCall | pending | |
| G | G1c | walker dispatch + instantiation cache + cap (folds G2+G9) | pending | |
| G | G2 | ~~instantiation cache~~ | folded | →G1c |
| G | G3 | type-substitution path through classifyType; auto return | pending | |
| G | G4 | distinct T as fresh uninterpreted sort + inject/eject/bijectivity | pending | |
| G | G5 | distinct borrow semantics | pending | |
| G | G6 | concept constraints: trust boundary + compound | pending | |
| G | G7 | static[T] params as instantiation-key components | pending | |
| G | G8 | multi-parameter generics | pending | |
| G | G9 | ~~concept stdlib table~~ | folded | →G1c |
| G | G10 | regression smoke vs E; walker `"7"→"8"` | pending | |

## Cluster C — closures and procs-as-values

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| C | C0-ADR | author ADR-0009-closure-encoding.md + closures.md skeleton | pending | |
| C | C1 | IR + parser: iekLambda, iekClosureCall, svClosure stub | pending | |
| C | C2a | walker: closure construction (env snapshot) | pending | |
| C | C2b | walker: closure call dispatch + multi-return-path axiom | pending | |
| C | C3 | top-level procs as values (unit-env encoding) | pending | |
| C | C4 | DSL HOFs: filter/map/fold over seq[T] | pending | |
| C | C5 | closure equality (nominal-for-site + structural-for-env) | pending | |
| C | C6 | regression smoke vs G; walker `"8"→"9"` | pending | |

## Cluster R — ref/ptr aliasing (logical heap)

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| R | R1a | IR + SVKind variants + exhaustive dispatch stubs | pending | |
| R | R1 | ref sort introduction — refSorts, nilConsts, allocRefSort, isDeref | pending | |
| R | R1b | inter-procedural heap threading | pending | |
| R | R2 | new T semantics — allocCounters, freshness cap | pending | |
| R | R3 | p[] read — select(heap_T, p) | pending | |
| R | R4 | p[] = v write — store(heap_T, p, v) | pending | |
| R | R5 | nil handling — nil_T, nil-fork → sxRaised(NilAccessDefect) | pending | |
| R | R6 | ref object field access | pending | |
| R | R7 | ref equality + alias chain | pending | |
| R | R8 | ptr T family + pointer arithmetic (hePtrArith) | pending | |
| R | R8b | var ref T param handling | pending | |
| R | R9 | recursive ref structures — heapDepth; heDepthExhausted | pending | |
| R | R10 | maxHeapDepth setting — cache-key participation | pending | |
| R | R11 | cast[ptr T](addr x) — sxUnknown(heUnsafeCast) | pending | |
| R | R11b | cross-cluster regression sweep + witness-format-v3.md | pending | |
| R | R12 | walker `"9"→"10"`, rendering `"2"→"3"`, heap-snapshot witness | pending | |
| R | R13 | closures capturing ref T; ptr T + try/finally composition | pending | |

## Documentation index

ADRs and design docs introduced or referenced by Phase 15 (closes Des-LOW-L2):

- `RFC-phase15-language-fragments.md` — the RFC (design source of truth).
- `RFC-phase15-reconciliation.md` — **authoritative override layer** (read first).
- `ADR-0005-float-nan-inf.md` — float NaN/Inf semantics (on disk; F0-ADR).
- `ADR-0006-string-codepoint-indexing.md` — string codepoint indexing (S0-ADR).
- `ADR-0007-exception-flow.md` — exception flow model (Z4).
- `ADR-0008-generic-instantiation.md` — generic instantiation (on disk; G0-ADR).
- `ADR-0009-closure-encoding.md` + `closures.md` — closure encoding (C0-ADR).
- `ADR-0010-logical-heap.md` — logical heap model (H1).
- `witness-format-v3.md` — heap-snapshot witness format (R11b).
- `determinism.md` — updated by S7b, S11, R10 (string/heap determinism notes).
