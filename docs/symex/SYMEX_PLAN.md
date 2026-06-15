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
| F | F2 | float literal lifts (Inf, NaN, -0.0, finite) + IEEE ==/!= | SHIPPED | (this cycle) |
| F | F3 | arithmetic ops (+ - * / unary-) | SHIPPED | (this cycle) |
| F | F4 | ordering compare (< <= > >=) | SHIPPED | (this cycle) |
| F | F5 | int↔float conversions with range overflow | SHIPPED | (this cycle) |
| F | F6 | math-module ops + FP predicates | SHIPPED | (this cycle) |
| F | F7 | eval-side bit-exact float witness round-trip | SHIPPED | (this cycle) |
| F | F8 | regression smoke; walker `"4"→"5"`; withSymexSettings wiring | SHIPPED | (this cycle) |
| F | F9a | array[N, float32/64] element type-bridge audit | SHIPPED | (this cycle) |
| F | F9b | seq[float32/64] param: allocate → extract → emitTyAndReader | SHIPPED | (this cycle) |
| F | F9c | object-variant arm fields of float32/64 | SHIPPED | (this cycle) |

## Cluster S — full strings

> **Model: byte-faithful per ADR-0006 (Corey-locked).** Free `string` vars
> constrain every char ≤ 0xFF, so Z3 position == Nim byte index. `s.len`/`s[i]`/
> `s[a..b]`/`s.high`/`for c in s` are all byte-faithful supported; only `s[i]=c`/
> `s.add` (immutability) and `toLower`/`toUpper` (no Z3 case-fold) stay unsupported.

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| S | S0-ADR | author ADR-0006 — **byte-faithful** string model (Corey-locked) | SHIPPED | (this cycle) |
| S | S1 | type-bridge: string → full Z3 String walker (chars ≤0xFF); iekStr* stubs | SHIPPED | (this cycle) |
| S | S2 | string literal lifts; byte-faithful (`"é".len == 2`) | SHIPPED | (this cycle) |
| S | S3 | s.len, s[i], s[a..b], s.high byte-faithful supported (+≤0xFF char constraint); s[i] char-bridged; for-c-in-s honestly classified unsupported (unbounded iteration) | SHIPPED | (this cycle) |
| S | S4 | find, contains, startsWith, endsWith (real nim-z3 contains/startsWith/endsWith/indexOf; `sub in s`→iekStrContains) | SHIPPED | (this cycle) |
| S | S5 | replace, replaceAll, split, join; maxSplitParts (replace first-occ; replaceAll version-gated→seZ3VersionMissing; split special-cases concrete/empty-sep, general→seZ3StringIncomplete; join over concrete seq[string]) | SHIPPED | (this cycle) |
| S | S6a | regex_parser.nim standalone | SHIPPED | (this cycle) |
| S | S6b | walker integration: iekStrMatch/iekStrFindRe | SHIPPED | match SAT/UNSAT; findRe deferred (no Z3 indexOf/regex); replaceRe gated |
| S | S7a | bytes(s) trivial byte-view (identity over ≤0xFF chars) | SHIPPED | byte-faithful identity svSeq[BV8]; seqLen EQUAL len(s); at→toCode→BV8 bridge; concrete-literal length only (symbolic → seBytesSymbolicLength); >maxBytesEncodingLen(32) → seBytesLengthTooLarge; seBytesBeyondBMP unreachable |
| S | S7b | Z3-string-theory regression smoke (L+F+S1–S7a) | SHIPPED | hermetic cross-op smoke `tsymex_phase15_S7b_smoke.nim` (8 tests, c+cpp): multi-op SUTs (len+index+contains+startsWith / len+slice+endsWith+find), concrete split+join+bytes in one SUT, regex match + string-equality, withSymexSettings on a string SUT, ≤0xFF free-`s.len==1` single-byte round-trip, walker version still "5". Broad regression subset all green, no hangs. determinism.md gains a STRING section. Finding: bool-returning string *helper* procs don't inline (sxUnknown) — conditions inlined per S-cluster convention |
| S | S8 | `&` string concatenation → Z3_mk_seq_concat | SHIPPED | `iekStrConcat` (StrOpKinds stub since S1) wired: parser intercepts `&` in the `nnkInfix` arm BEFORE `binopForInfix` when BOTH operands `classifyType` as `itString` (`s&t`, `s&"lit"`, `"lit"&s`); chained `a&b&c` is left-assoc nested binary nodes so operand recursion handles it; the seq/other-`&` path is untouched (non-itString operands fall through to `binopForInfix`). runtime `lower`: `SymVal(svString, concat(l.str, r.str))` (nim-z3 `concat` = `Z3_mk_seq_concat`; both operands lower to svString, a literal via the `iekStrLit`→`mkString` path). `probeProto` svString arm. No parser-`&` was ever wired for seq concat, so additive. Test `tsymex_phase15_S8_concat.nim` (5 tests: literal→"foobar", var concat→b=="llo", chained "abc", additive len, UNSAT contradiction) green c+cpp 5/5; regression S1–S7b + phase5_seq + F2 clean, no hangs. Walker version unchanged at "5" |
| S | S9 | toLower/toUpper → seUnsupportedStringOp | SHIPPED | case-folding ops classified unsupported (ADR-0006: no Z3 native case-fold; regex-range approx deferred to Phase 16). dsl_parser intercepts `toLower`/`toUpper` (std/unicode) + `toLowerAscii`/`toUpperAscii` (std/strutils) on an `itString` receiver BEFORE `getStdlibModelFor`, routing to `iekStrUnsupported` → classified `seUnsupportedStringOp` (sxUnknown, Invariant 3 — never silent UNSAT/crash). Reuses the existing `iekStrUnsupported`/`SymexUnsupportedStringOpError` mechanism — no new IR kind, no new error kind. Explicit guard (not the `getStdlibModelFor` else-fallthrough) keeps classification intentional + carries the real op name into the diagnostic. Test `tsymex_phase15_S9_caseconv.nim` (5 tests: 4 case-conv ops → sxUnknown+seUnsupportedStringOp, plus plain `s=="abc"` still sxSat) green c+cpp 5/5; regression S1–S5,S8,S7b clean, no hangs. Walker version unchanged at "5" |
| S | S10a | $int/parseInt digits-path; explicit unsoundness window | SHIPPED | digits-path only (S10b raises-path still deferred to post-E1). New error kind `seParseIntPreE` (**sevHint**, NOT sevError — a path carrying it stays sxSat, exercising the sxSat+non-error severity contract). dsl_parser: `$n` (`nnkPrefix` `$`) on an itInt → `iekIntToStr` (Z3 `Z3_mk_int_to_str`, nim-z3 `toStr` on Z3Int; operand coerced via `toZ3Int` since int params are BVs); `parseInt(s)` on an itString → `iekStrToInt`. runtime: `iekStrToInt` = `ite(startsWith(s,"-"), -toInt(substr(s,1,len-1)), toInt(s))` (nim-z3 `startsWith`=`Z3_mk_seq_prefix`, NOT the RFC's `prefixOf`; `toInt`=`Z3_mk_str_to_int` returns **−1** for non-digit, NOT "unconstrained" as the RFC premised — verified `strings.nim:126`). Digits gate on the NEGATIVE branch only (`isNeg ⇒ negInner>=0`) via a `parseIntGateConstraints` threadvar drained into every `trySolve` check; positive branch is already faithful (returns true digits or −1). seParseIntPreE sevHint emitted whenever parseInt is lowered on a not-provably-digit string (conservative HINT over-emission), surfaced on sxSat results via `parseIntPreEHints` threadvar. Test `tsymex_phase15_S10a_strconv.nim` (4 tests: `$n=="42"`→n=42; `parseInt(s)==42`→s="42"; `parseInt("-42")`→ −42; non-digit `parseInt(s)==-1`→sxSat+seParseIntPreE hint) green c+cpp 4/4. str.to_int + prefix ops do NOT hang under ≤0xFF. Regression S1–S5,S8,S9,S7b,phase1_arith,F2 clean. Walker version unchanged at "5" |
| S | S10b | parseInt raises-path fork (depends on E1) | pending | |
| S | S11 | string mutation classified; walker `"5"→"6"` | SHIPPED | **CLOSES Cluster S.** Immutable-string mutations classified `seUnsupportedStringOp` → sxUnknown (ADR-0006, Invariant 3 — never silent UNSAT/crash). dsl_parser: (1) `s[i] = c` detected in the `nnkAsgn` arm when the LHS `nnkBracketExpr` receiver is `itString` → `mkAssign(s, mkStrOp(iekStrUnsupported,"string mutation",[recv,idx,val]))`; the index-assign path IS reachable in the SUT grammar (local `var s: string` + index assign parses cleanly). (2) `s.add(c)`/`s.add(otherStr)` intercepted in the statement-`nnkCall` arm BEFORE the itSeq `add` arm when receiver is `itString` → `mkStrOp(iekStrUnsupported,"string add",…)`. Both reuse the S9/S3 idiom (residual `lower` arm raises `SymexUnsupportedStringOpError` → runSymex boundary maps to seUnsupportedStringOp). No new IR kind, no new error kind. **Walker version bumped `"5"→"6"`** (single-sourced `canonicalize.nim:symexWalkerVersion`; confirmed no duplicate). Stale F8/S7b version-pin assertions advanced "5"→"6" (expected consequence of the bump). determinism.md: unsupported-op table updated + Cluster-S op-table-complete note. Test `tsymex_phase15_S11_mutation.nim` (5 tests: s[i]=c, s.add(c), s.add("x") → sxUnknown+seUnsupportedStringOp; plain read → sxSat; version=="6") green c+cpp 5/5. Broad regression under v6 (cache keys orphaned → everything re-solves) all green, no hangs: S1–S10a, F2, F6, F8, phase1_arith, phase5_seq, phase14_multivariant_walker/disc_promotion/frontier_pruning. (S10b — parseInt raises-path — remains deferred to post-E1; it will carry its own bump.) |

## Cluster H — heap preparation

| cluster | cycle | title | status | commit |
|---------|-------|-------|--------|--------|
| H | H1 | Path refactor (heaps/heapDepth/allocCounters) + ADR-0010 | SHIPPED | |

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
- `ADR-0006-string-codepoint-indexing.md` — **byte-faithful** string model
  (S0-ADR; filename historical — title is now byte-faithful, Corey-locked).
- `ADR-0007-exception-flow.md` — exception flow model (Z4).
- `ADR-0008-generic-instantiation.md` — generic instantiation (on disk; G0-ADR).
- `ADR-0009-closure-encoding.md` + `closures.md` — closure encoding (C0-ADR).
- `ADR-0010-logical-heap.md` — logical heap model (H1).
- `witness-format-v3.md` — heap-snapshot witness format (R11b).
- `determinism.md` — updated by S7b, S11, R10 (string/heap determinism notes).
