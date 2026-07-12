# RFC — proptest consumer-hardening (from chapulin v1/v2 harness)

> Empirically-sourced hardening RFC. Every item was surfaced building chapulin's
> symex + fuzz + soak verification harnesses against proptest, and **re-verified
> at HEAD `99fa2db`** before entering this doc — healed findings are dropped, live
> ones carry their reproduced symptom + locus. Source:
> `/mnt/c/Users/corey/projects/chapulin/docs/proptest-findings.md`.

## Status

| | |
|---|---|
| **Stage** | 1 (RFC + slicing) |
| **Scope** | mega-RFC across all subsystems (Corey-decided 2026-07-12), organized into per-subsystem clusters, each independently sliceable |
| **Verification** | all ~30 findings re-checked at `99fa2db` by 4 agents; results in the session's `verify_results.md` and reflected below |
| **Handoff** | `docs/RFC-chapulin-hardening.handoff.md` |

## §0 — Thesis (the marquee, cross-cutting)

chapulin's own top ticket: *"make the walker's failure mode total."* Verification
sharpened this into a **two-sided invariant**:

> **Totality + soundness of the failure mode.** Any construct proptest doesn't
> model must degrade to a **sound** classified `sxUnknown` — never (a) a native
> crash (uncaught `doAssert`/`KeyError`/`ValueError`), never (b) a compile-time
> macro `error()` that aborts expansion, and never (c) a **silent wrong answer**
> (a `false sxSat`/`sxRaised` with empty `errors`). Then progressively widen the
> modeled fragment.

The (c) clause is new and load-bearing: verification found that today's
"degrade" path (`mkUnsupported` statements) is itself **unsound** — so the (a)/(b)
crash-hardening *must not ship before* the (c) soundness fix, or we'd trade
visible crashes for silent wrong answers (strictly worse under Invariant 3).

**Hard dependency:** `SND-1 ≺ CR-1, CR-2` (soundness before crash-degrade).

## Slice inventory

Status legend: **LIVE** (reproduced at HEAD) · **NEW** (found during verification)
· **DROP** (healed — listed in §Healed, not sliced). Size S/M/L.

| ID | Slice | Cluster | Sev | Size | Deps |
|----|-------|---------|-----|------|------|
| SND-1 | Unmodeled statement must not silently mis-mutate (no false `sxSat`) | Soundness | **CRIT** | L | — |
| SND-2 | `symexAssume` real filter semantics (stop masking `sxUnsat` with false `sxRaised`) | Soundness | **CRIT** | M | — |
| CR-1 | Walker runtime crash → classified `sxUnknown` (sweep) | Crash-totality | high | M | SND-1 |
| CR-2 | Macro-expansion totality: `error()` → classified degrade | Crash-totality | high | M | SND-1 |
| M1 | `seq[byte]`/fixed-width-int witness readers | Model gaps | high | S–M | CR-1 |
| M2 | `parseBiggestInt` model (unblocks chapulin B4) | Model gaps | high | S | — |
| M3 | `rfind` model | Model gaps | med | M | — |
| M4 | in-place string `.add` / `&=` model | Model gaps | med | S–M | SND-1 |
| M5 | `min`/`max` (if-expression-bodied inlining) | Model gaps | med | M | CR-2 |
| M6 | `probeProto` sentinel completeness (defensive) | Model gaps | low | XS | — |
| P1 | general `nnkTupleConstr` return | Parser | med | S–M | — |
| P2 | `nnkObjConstr` in the expression path | Parser | med | M–L | — |
| P3 | `seq` slicing `data[a..b]` (+ `openArray` type path) | Parser | med | M | — |
| P4 | `..^` backward-index slicing | Parser | low | S | — |
| Q1 | dependent bounded loops (defect-target search) | Solver | med | L | — |
| Q2 | loop + `string`-param under defect-target search | Solver | high | L | — |
| F1 | non-pruned coverage-corpus channel (`dbReusePhase`) | Fuzz | high | L | — |
| F2 | up-front coverage-replay of preloaded seeds (`minimizeCorpus`) | Fuzz | med | M | — |
| F3 | export `minimalCovering*` | Fuzz | low | S | — |
| F4 | `FuzzSettings.stopOnFirstCrash` | Fuzz | low | S | — |
| F5 | document `db.nim applySave` ordering | Fuzz | low | S | — |
| F6 | per-primary-entry metadata slot | Fuzz | med | M | — |
| F7 | choice-IR seed protocol: document + surface dropped-seed count | Fuzz | med | M | — |
| F8 | corpus section-size introspection helper | Fuzz | low | S | — |
| C1 | coverage slot→`file:line:col` side-table | Coverage | med | L | — |
| C2 | (doc-only) explain 8192-bitmap convergence | Coverage | low | S | C1 |
| SH1 | shrinker `seq[byte]` `Int128` compile bug | Shrinker | — | ? | **deferred — needs consumer repro** |

---

## Cluster 1 — Soundness (worst class: silent wrong answers)

### SND-1 — unmodeled statement silently mis-mutates → false `sxSat`  ·  CRIT  ·  NEW
**Found during verification** (not in the original doc, but implicated by #10's `&=`).
Any `mkUnsupported` **statement** is handled as a no-op that continues the path
with **stale state** (`runtime.nim:6041-6043`: `of isUnsupported: w.sawUnknown =
true; paths`), and ADR-0012 D2's precedence (`runtime.nim:7305-7331`: *first
`sxSat` wins outright, `sawUnknown` consulted only when no `sxSat`/`sxRaised`
exists anywhere*) means a target reached **after** the dropped mutation is
reported `sxSat` with a **silently wrong witness and empty `errors`**.
- **Reproduced (general, not string-specific):** `t &= "x"; if t == "ax": target`
  → `sxSat` witness `s="ax"` (real Nim: `"ax" & "x" = "axx" ≠ "ax"`, correct
  witness is `"a"`). And `acc /= 2.0; if acc == 5.0: target` → `sxSat` witness
  `x=5.0` (real needs `10.0`).
- **DoD:** an unmodeled statement on a path must make any `sxSat` found *downstream
  on that same path* untrustworthy — either **halt the path** (contribute
  `sxUnknown`, not a witness) or **taint** the precedence so a same-path
  `sawUnknown` demotes a downstream `sxSat` below `sxUnknown`. Regression: a
  target reached *before* / independent of the drop still yields a valid `sxSat`.
- **Likely needs an ADR** (amends ADR-0012 D2 precedence). This is the sequencing
  root: **must land before CR-1/CR-2.**

### SND-2 — `symexAssume` == `symexAssert`, masking `sxUnsat` with false `sxRaised`  ·  CRIT  ·  LIVE
`dsl_parser.nim:2716-2717` parses `symexAssume(cond)` to `mkAssert(cond)` —
byte-identical to `symexAssert` — while `symex.nim:934-941` documents filter/prune
("conjoin into the path condition") semantics. `isAssert` (`runtime.nim:5891-5899`)
unconditionally forks an `AssertionDefect` via `forkDefect`→`routeRaise`, and E6
(`runtime.nim:6154-6167`) surfaces any reachable `Defect` regardless of target.
- **Reproduced:** a genuinely-unreachable target (`s[0]=='a' and s[0]=='b'`)
  proves `sxUnsat` cleanly; prepending `symexAssume(s.len <= 5)` (violatable) flips
  it to **`sxRaised(AssertionDefect)`** — a false defect masking a correct proof.
- **DoD:** a distinct `isAssume` IR kind that **purely conjoins `cond` into
  `p.pc`** with no `forkDefect`/E6 raise-fork; `symexAssume(cond)` narrows the
  search (violating states pruned), never manufactures a defect. Touches every
  `isAssert`-exhaustive site (`scan.nim`, `abstraction.nim`, `canonicalize.nim`,
  `runtime.nim`, `types.nim`). Regression: `symexAssert` behavior unchanged.

---

## Cluster 2 — Crash-totality (Invariant-3: never crash, always classify)

**Depends on SND-1** (degrading to a sound `mkUnsupported` first).

### CR-1 — walker runtime crashes → classified `sxUnknown`  ·  high  ·  LIVE
Sweep the walker for uncaught crash sites and convert each to a classified
`SymexUnsupported…`/`sxUnknown`. Two confirmed instances anchor it:
- **#4** implicit tail-expression return referencing a local `let` → uncaught
  `KeyError` at `runtime.nim:2629` (`of iekVar: env[e.vname]`). Repro:
  `let hi = data[o] mod 256; hi + 1`. **LIVE-CRASH.**
- **#3** bitwise op on an `svInt` (arising from `.len`/`find`/`indexOf`/`parseInt`,
  *not* a plain-int param which now allocates `svBV64`) → uncaught
  `ValueError: bitwise op on promoted Z3Int` at `runtime.nim:2951-2957`. Repro:
  `s.find(x) and 1`, `len and 1`. **LIVE (narrowed).**
- **DoD:** both repros return a classified `sxUnknown` (not a native exit); a
  grep-guided sweep of `runtime.nim` for bare `env[...]`/`doAssert`/`raise
  newException` on the walk path converts each to soft-fail. Regression: no
  currently-`sxSat`/`sxUnsat` test flips.

### CR-2 — macro-expansion totality: `error()` → classified degrade  ·  high  ·  LIVE
An unsupported **expression kind** or **type** currently aborts *compilation* via
`error()` (`dsl_parser.nim:1847` `parseExpr` catch-all; `dsl_typebridge.nim:452`
scalar-type switch) — strictly worse than `sxUnknown` (the SUT can't even be
analyzed). Convert these hard errors into a classified degrade (emit
`mkUnsupported` → `sxUnknown`) so any unmodeled construct fails soft. This is the
**safety net** that catches the whole macro-error class (M1/M2/M5/P1/P2/P3 shapes)
*before* each feature is individually built.
- **DoD:** a SUT using any currently-`error()`-ing construct returns `sxUnknown`
  with a classified kind, not a compile failure. **Must land after SND-1** (else
  it multiplies the silent-mis-mutation surface).

---

## Cluster 3 — Model / stdlib gaps (clean degrade today; widen coverage)

- **M1 — `seq[byte]`/fixed-width-int witness readers** · LIVE (compile macro-error
  at `symex.nim:696-698`; `itSeq` reader handles only `int64`/`f32`/`f64`/`ref`).
  Add reader cases for `byte`/`uint8..uint64`/`int8..int32`. Removes chapulin's
  `atByte` mask workaround *and* the #3 collision surface. Size S–M.
- **M2 — `parseBiggestInt`** · LIVE (compile macro-error; only `parseInt` matched
  at `dsl_parser.nim:1504-1506`). Near-clone → same `iekStrToInt` IR (64-bit on
  this platform). **Directly unblocks chapulin v2 slice B4.** Size S.
- **M3 — `rfind`** · LIVE (clean `sxUnknown` degrade; `dsl_parser.nim:1727`
  catch-all). Model mirroring `iekStrFind` (needs a last-occurrence Z3 seq
  primitive or bounded scan; cf. nim-z3 `lastIndexOf`). Size M.
- **M4 — string `.add` / `&=`** · LIVE. `.add` degrades cleanly; `&=` is the
  SND-1 case (silent no-op → false `sxSat`). Model both as concat
  (`iekStrConcat`), and add `&=` to the augmented-assign set
  (`dsl_parser.nim:2962-3000`). **Coupled to SND-1.** Size S–M.
- **M5 — `min`/`max`** · LIVE (compile macro-error; `nnkIfExpr` handled in
  `parseStmt` but not `parseExpr`, `dsl_parser.nim:1847`). Add an `nnkIfExpr`
  case to `parseExpr` (synthetic let+read) — also fixes any if-expression-bodied
  proc inlining. Size M.
- **M6 — `probeProto` sentinel completeness** · LIVE-but-DEAD. The catch-all at
  `runtime.nim:1763-1767` omits `iekStrToLower/Upper/RadixFmt/RuneToStr` from its
  modeled set (returns `none`), but it's **inert today** (proto unused by string
  arms; `bEq` fallback recovers). Defensive-only fix. Size XS.
  *(Finding #7's original symptom — `toLowerAscii` unmodeled — is **HEALED** by
  A9; see §Healed.)*

## Cluster 4 — Parser expression coverage

- **P1 — general `nnkTupleConstr` return** · LIVE (macro-error at 1847; only the
  `yield (e1,e2)` special-case at 1999-2023 exists). Add a general N-ary case
  building an `itTuple` SymVal. Size S–M.
- **P2 — `nnkObjConstr` in the expression path** · LIVE (macro-error; only handled
  inside `newException(...)` at 2914 + codegen). Object/variant construction as a
  first-class expression — touches the field-split heap model. Size M–L.
- **P3 — `seq` slicing `data[a..b]`** · LIVE, root cause **upstream**: Nim types
  the slice as `openArray[int]`, rejected by the scalar classifier
  (`dsl_typebridge.nim:452`) before `itSeq`'s bracket case (1241-1247, which also
  lacks a slice branch, unlike `itString`). Needs both an `openArray`/slice-result
  type path *and* a seq-slice IR. Size M.
- **P4 — `..^` backward-index slicing** · LIVE (incidental; `result[1..^1]` →
  parser "unsupported infix operator ..") . Size S.

## Cluster 5 — Solver capability (fail-soft; scoping matters)

- **Q1 — dependent bounded loops** · LIVE (`sxUnknown`, empty errors; confirmed
  independent of `maxLoopUnwind`/`maxCallDepth`). **Only bites a defect/universal
  target** (`tIndexError()`), not a `tLabel` reachability search. Size L.
- **Q2 — loop + `string` param** · LIVE, **narrower than the original claim**: the
  doc's "ANY loop + string param → `sxUnknown`" is empirically false for `tLabel`
  (all shapes `sxSat`); it's real specifically for **defect-search targets over an
  `s.len`-bounded loop** (Z3 Sequence-theory × loop-unwind path-merge). Biggest
  string-code capability gap; the target-kind gate shrinks the surface. Size L.

## Cluster 6 — Fuzz / corpus / DB  (all CONFIRMED at HEAD)

- **F1** non-pruned "coverage corpus" channel, separate from the regression-replay
  primary that `dbReusePhase` prunes (`engine/phases.nim:65-84`). L.
- **F2** up-front coverage-replay pass over preloaded seeds so an external corpus
  minimizes losslessly (`fuzz.nim:381-403` seeds get zero-`Coverage`). M.
- **F3** `export minimalCovering*` (`fuzz.nim:337`). S.
- **F4** `FuzzSettings.stopOnFirstCrash` (`fuzz.nim:122-186`). S.
- **F5** document `applySave` prepend/reverse-insertion order (`db.nim:163-169`). S.
- **F6** per-primary-entry metadata slot (`db.nim:47-52,109-111`). M.
- **F7** document the 2N+1 choice-IR draw-order protocol + surface `captureIR`'s
  dropped-seed count in `FuzzReport` (`strategy.nim:451-480`, `fuzz.nim:262-277`). M.
- **F8** corpus section-size introspection helper (`db.nim:83-101`). S.

## Cluster 7 — Coverage

- **C1** emit a slot→`file:line:col` side-table at `{.cover.}` expansion
  (`coverage.nim:85-88`) — unblocks source-mapped coverage-gap reports. L.
- **C2** (doc-only) explain the fixed 8192-slot bitmap convergence
  (`coverage.nim:23`); C1 is the real lever. S.

## Cluster 8 — Shrinker

- **SH1** `shrink` 2-arg overload `seq[byte]` `Int128` compile bug
  (`shrinker.nim:274`). **Does NOT reproduce at HEAD** — three faithful repros
  compiled clean under Nim 2.2.10. **Deferred:** needs chapulin's exact repro file
  / a bisect before it can be sliced; do not fix blind.

---

## Healed since the findings doc (verified — not sliced)

- **#5** var-out-param helper in a loop — 5 shapes all `sxSat`/expected.
- **#11** depth-3 nested-if string helper + string op — depth 1–6 + replace→contains
  all clean.
- **#7** `toLowerAscii`/`toUpperAscii` symptom — modeled by A9 (walker v37); every
  comparison shape returns validated `sxSat`. (Residual `probeProto` gap → M6.)
- **`pred`/`succ`** — work via generic call-inlining.
- **`..<`** — matched as a literal infix; never lowered through `pred`.
- **SH1** — see Cluster 8 (does-not-reproduce; deferred, not healed-confirmed).

## Sequencing & Phase-DoD

**Order (dependency-respecting):**
1. **SND-1** (soundness root — unblocks safe degrading), then **SND-2**.
2. **CR-1**, **CR-2** (crash-totality, now safe to degrade).
3. Model/parser feature slices (M1–M5, P1–P4) — each turns a now-`sxUnknown`
   construct into real `sxSat`; independently orderable. **M2 early** (unblocks
   chapulin B4).
4. Solver slices Q1/Q2 (harder; can run in parallel with 3).
5. Fuzz/coverage clusters (F*, C*) — independent subsystem; any order.
6. SH1 deferred pending repro.

**DoD:** every LIVE/NEW slice ships with a both-backend (`c`+`cpp`) regression
green; the §0 invariant holds (a fuzz-style sweep of unsupported constructs yields
`sxUnknown`, never a crash/macro-error/false-`sxSat`); chapulin's harness re-runs
against the new pin with its documented workarounds removable. SH1 excluded (no
repro). Fuzz/coverage/shrinker doc-only items (C2, F5) are documentation DoD.

## ADRs likely introduced

- **Failure-mode totality & soundness** (SND-1 + CR-1/CR-2) — amends ADR-0012 D2
  verdict precedence so a same-path `sawUnknown` demotes a downstream `sxSat`.
- **`isAssume` semantics** (SND-2) — a filter/prune IR kind distinct from
  `isAssert`.
- (Possibly) **object/tuple construction as expressions** (P1/P2) vs the
  field-split heap model.
