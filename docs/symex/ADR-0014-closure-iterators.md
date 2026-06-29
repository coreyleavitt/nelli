# ADR-0014 — closure iterators (inline-desugaring at the `for`-site)

> **STATUS: ACCEPTED — 2026-06-28.** Design ADR for RFC slice **A3** (closure
> iterators). Authored from a thorough read-only Explore map of the current
> iterator/closure handling. Sits on top of **ADR-0009** (closure encoding) and
> the existing `isWhile` bounded-unroll. Citations are point-in-time at walker
> **v29**; re-verify each `/tdd` cycle.

## Context — the blocker

A `{.closure.}` (or inline) iterator and a `for x in it():` loop over it cannot be
symbolically executed today:

- An `iterator` definition parses to `iekLambda` with a sentinel
  `mkUnsupported("closure iterators not yet supported")` body
  (`dsl_parser.nim:945–965`) → `ceNotImplemented` → **`sxUnknown`**.
- `for x in someIterator():` parses the iterable as an `nnkCall` and routes it
  through the `isCall` path (`dsl_parser.nim:2000–2159`) with no iterator
  protocol → **`sxUnknown`**.

There is **no `iekIterator` IR node** and no resumable-iterator semantics.

## Decision

**Model `for x in <iteratorCall>(args):` by INLINING the iterator body at the
`for`-site** — exactly how the Nim compiler expands an *inline* iterator. This is
a **parse-time (macro-time) AST transformation**; it produces only existing IR
(`isWhile`/`isIf`/`isLet`/…), reuses the **entire** existing walker — including
the `isWhile` bounded-unroll (`maxLoopUnwind`, default 5) for any loop *inside*
the iterator — and needs **no new IR node, no resumable-state machine**.

It covers **both** inline and `{.closure.}` iterators in the overwhelmingly common
`for x in it(args):` direct-call form (inlining is identical for both — once we
expand, the `{.closure.}` pragma is irrelevant; we never build a closure object).

**First-class resumable iterators are DEFERRED** (see D6): an iterator value
stored in a `var`, passed as an argument, or resumed via an explicit `next()`
outside a `for` — those genuinely need the resume-point state machine and are rare.

**Rejected alternatives.**
- *New `iekIterator` node + a resumable env+resume-point walker protocol* — 8
  plumbing sites (types.nim enum/fields/ctor/render, dsl_parser, canonicalize,
  walker, abstraction) and a stateful resume model, to buy semantics that
  inlining already gives for the common case. Defer the resumable model to when a
  first-class-iterator SUT actually demands it.
- *Reuse `iekLambda` + an iterator marker + a multi-yield `applyIteratorYields`
  axiom* — keeps the closure funcSym machinery but a closure iterator is **not a
  pure function** (it yields a *sequence* with state across resumes); shoehorning
  it into the `applyClosureGround` ground-axiom form is more complex and less
  sound than just inlining the control flow.

## Design

### D1 — detection (`for`-loop arm, `dsl_parser.nim` ~2000–2159)

In the `nnkForStmt` parse arm, insert the **iterator-call** detection **AFTER the
existing `items`/`pairs` built-in dispatch (~line 2035) and BEFORE the final
`else`/`mkUnsupported`** (review N-4). The ordering is load-bearing: `items`/
`pairs`/`mitems` over arrays/seqs/strings ARE `nnkIteratorDef` symbols too, and the
existing seq/array/range/string paths model them optimally — they must NOT be
inline-expanded. So detection fires only for a *user* iterator call that none of the
prior arms claimed.

Detect: the iterable is an `nnkCall` whose callee resolves (via `getImpl`) to an
`nnkIteratorDef`. **Wrap `getImpl` in a `try`/`except`** (review N-1): on any
failure (unresolvable/builtin/magic callee) fall through to the existing path →
`sxUnknown`, never a crash. Only **direct calls** qualify in A3-S1; a bare iterator
*value* (non-`nnkCall` iterable, or a callee that is a `var`/param of iterator type
whose `getImpl` is not an `nnkIteratorDef`) falls through → still `sxUnknown`
(deferred D6), never wrong.

### D2 — the inline transformation

Given `for <loopVars> in <itSym>(<args>): <forBody>`:

0. **Soundness pre-scans — run ALL of these FIRST; if any fires, emit
   `mkUnsupported(<reason>)` for the WHOLE `for` statement (→ `sxUnknown`, sound)
   and do not inline.** These mechanize D4’s degradation promises (the review found
   that stating the outcome without the mechanism left two Invariant-3 holes):
   - **(a) `getImpl` shape (CRIT-4).** `impl = getImpl(itSym)` inside the D1
     `try`. Require `impl.kind == nnkIteratorDef` AND the body contains ≥1
     `nnkYieldStmt` (scanning outside nested `nnkProcDef`/`nnkFuncDef`/
     `nnkIteratorDef`/`nnkLambda`). If a `{.closure.}` iterator’s impl came back
     already state-machine-lowered (no surface `yield`), degrade. *(**CONFIRMED
     empirically 2026-06-28**: `getImpl(countUp)` on a `{.closure.}` iterator
     returns `nnkIteratorDef` with body `StmtList(VarSection, WhileStmt(…,
     YieldStmt(Sym i), inc i))` — clean `YieldStmt` leaves, pre-`transf`. The guard
     stays as belt-and-suspenders for edge cases.)*
   - **(b) `return` in the iterator body (CRIT-1 — Invariant-3).** Scan `impl`’s
     body for `nnkReturnStmt` NOT inside a nested routine. If found, degrade. A
     bare iterator `return` means *finish early*, but the parser lowers it to a
     proc-`return` (`dsl_parser.nim:2099`) → `isReturn` either drops the path
     (callStack.len==0) or, when the SUT is itself a called proc, routes to the
     caller’s `returnedPaths` with an UNCONSTRAINED `retSym` → Z3 may pick an
     impossible return value → **false positive**. Degrade until a later slice
     models iterator-early-finish.
   - **(c) `break`/`continue` in `<forBody>` (CRIT-2/SF-1 — Invariant-3 for a
     FINITE iterator).** Scan the raw `forBody` NimNode for `nnkBreakStmt`/
     `nnkContinueStmt` (outside nested loops/routines) BEFORE parsing it. If
     found, degrade. Rationale: a finite (yield-per-statement) iterator inlines to
     a *sequence of blocks with no enclosing `while`*, so a `break` hits
     `loopStack.len==0` → the path is dropped while LATER inlined yields still run
     → surviving state is wrong → **false positive**. (A while-driven iterator
     happens to model `break` correctly, but we cannot cheaply distinguish the two
     at scan time, so degrade uniformly in S1; S2 lifts this.)
   - **(d) recursion (CRIT-3 — compile-time hang).** Thread a
     `HashSet[string]` of iterator syms *currently being inlined* on the parse
     `ctx`. If `itSym` is already in the set, degrade (`"recursive iterator —
     cannot inline"`). Add `itSym` before recursing into its body, remove after.
     Without this a self-/mutually-recursive iterator infinitely re-`getImpl`s →
     compiler stack overflow on a valid SUT.
   - **(e) non-trivial default-valued params (N-2).** If a formal param is absent
     from the call and its default expr is not a literal/module-const, degrade
     (the default may reference iterator-scope syms that don’t survive inlining).
   - *Note (SF-2): `nnkDefer` already routes to `mkUnsupported` (`dsl_parser.nim`
     ~2404) so `defer` degrades for free — no extra scan. `try`/`except`/`finally`
     IS fully supported (E3, `runtime.nim:5922`), so an iterator body using it is
     walked faithfully — do NOT degrade for `try` (the draft was overcautious).*
1. `impl = getImpl(itSym)` — the typechecked iterator routine AST
   (`nnkIteratorDef`: formal params, body with `nnkYieldStmt` leaves), already
   validated by pre-scan 0(a).
2. **Param binding.** For each formal param `p_i` with supplied arg `a_i`, emit a
   fresh `let __it_p_i = a_i` (A-normalised; gensym the name) and substitute
   `p_i → __it_p_i` throughout the iterator body. (Or bind directly if the parser
   already A-normalises call args.) Default-valued params absent from the call use
   the default expr.
3. **Yield rewrite.** Replace every `nnkYieldStmt(e)` in the body with the block
   ```
   block:
     let <loopVars> = <e>      # bind the for-loop variable(s); tuple-destructure if multiple
     <forBody>                 # the original for-loop body, hygienically spliced
   ```
   A `yield` that produces a tuple destructured by multiple `loopVars` binds each
   component (mirror Nim's `for a, b in it()`).
4. **Splice & re-parse.** The rewritten iterator body becomes the desugared
   statement list; hand it to the normal statement parser. Iterator-local `var`s
   become ordinary locals of the enclosing scope (gensym to avoid collisions). Any
   `while`/`for`/`if` inside the iterator parses to the normal IR and is bounded by
   the existing unroll machinery.

The net effect is **as if the user had written the loop out by hand** — the
canonical inline-iterator expansion.

### D3 — bounding & termination

The `for x in it():` loop terminates symbolically because the iterator's *internal*
control flow is what drives yields, and every internal loop is bounded by
`maxLoopUnwind` (`isWhile` unroll). A finite (yield-per-statement) iterator inlines
to straight-line code; a `while`-driven iterator inlines to a bounded `while`. **No
new budget** — reuse `maxLoopUnwind`. (A separate `maxIteratorUnwind` is YAGNI
until a SUT needs to bound iterator yields independently of in-iterator loops.)

### D4 — soundness (Invariant 3 — no false positives)

1. **Beyond the bound ⇒ `uncertain`, never a wrong verdict.** An iterator that
   would yield more than `maxLoopUnwind` times inlines to a `while` whose tail
   paths the unroll marks `uncertain` (`sxUnknown`) — sound (we never claim a
   target reached or a defect absent past the bound).
2. **`break`/`continue` in `<forBody>` (CRIT-2/SF-1).** For a FINITE iterator the
   inlined body has no enclosing `while`, so `break` hits `loopStack.len==0` and the
   path is dropped while later inlined yields still execute → wrong surviving state →
   **false positive**. S1 therefore **degrades to `sxUnknown`** for ANY for-body
   containing `break`/`continue`, via the **mechanized pre-scan D2 step 0(c)** (scan
   the raw for-body NimNode for `nnkBreakStmt`/`nnkContinueStmt` BEFORE parsing).
   This is the realisation of the promise — stating it without the scan is what left
   the hole. S2 lifts the restriction for while-driven iterators where targeting is
   provably correct.
3. **`return` inside the iterator body (CRIT-1).** A bare iterator `return` (finish
   early) lowers to a proc-`return` → `isReturn` drops the path or leaves the
   caller’s `retSym` unconstrained → **false positive**. S1 degrades via **pre-scan
   D2 step 0(b)**.
4. **`defer` inside the iterator** degrades for free (`nnkDefer` →
   `mkUnsupported`). **`try`/`except`/`finally` IS supported** (E3,
   `runtime.nim:5922`) and is walked faithfully when inlined — NOT degraded.
5. **Recursive / mutually-recursive iterators** degrade via **pre-scan D2 step
   0(d)** (the `ctx` currently-inlining set) — a compile-time-hang guard, not a
   verdict issue.
6. **Var mutation across yields is modelled for free.** Because we inline into one
   scope, an iterator local mutated between yields (`inc i`) is an ordinary
   sequential mutation the walker already handles — no special state machine.
7. **Exceptions raised inside the iterator body** route through the existing
   defect/raise machinery (the inlined statements fork raises exactly as if
   written inline) — no special handling, sound.
8. **Side-effecting args / impure iterators** — args are A-normalised to `let`
   bindings (evaluated once, as Nim does), preserving evaluation order.

### D5 — hygiene

All synthesised names (param binds, iterator locals, the loop-var binds) are
**gensym’d** so they cannot collide with the SUT’s own identifiers or with a
second inlining of the same iterator in the same proc. The substitution is
capture-avoiding (rename iterator formals/locals; never rebind a free var the
iterator captured from its definition scope — those resolve as the original syms).

### D6 — DEFERRED: first-class resumable iterators

Out of A3-S1/S2 scope (own later slice if a SUT demands it): an iterator value
stored in a `var`/param, passed to/returned from a proc, or advanced by explicit
`next()` calls interleaved with other code. These need the resumable env +
resume-point (program-counter) state machine over ADR-0009’s closure env. Until
then they remain `sxUnknown` (sound). The non-call/`var`-iterable `for` also stays
deferred (D1).

### D7 — version & pins

Iterator SUTs flip `sxUnknown` → real verdicts ⇒ behaviour change ⇒
**`symexWalkerVersion` 29→30 + update/run BOTH pins**
(`tsymex_phase15_CR2_cachekey`, `tsymex_phase16_R16_1_arithcheck_foundation`). Per
[[symex-version-bump-cr2]]. (Even though no IR *node* is added, the IR *produced*
for an iterator SUT changes from `iekLambda`-unsupported to the inlined body, and
verdicts change — a previously-cached `sxUnknown` is stale.)

## Consequences

- Iterator `for`-loops over direct calls become first-class, reusing the whole
  walker; zero new IR/budget; the design mirrors Nim’s own inline expansion.
- New `tests/tsymex_a3_closure_iterators.nim` MUST include both directions:
  - *Positive:* a `countUp`-style bounded iterator summed in a `for` reaching a
    label (`sxSat` with a witness asserting the summed value); a beyond-bound
    iterator (`uncertain`/`sxUnknown`, sound).
  - *False-positive-direction RED tests (SF-4 — these go RED if a degradation
    silently mis-models):* (1) a FINITE iterator with `break` in the for-body →
    must be `sxUnknown`, NOT a spurious `sxSat`; (2) an iterator containing
    `return` → must be `sxUnknown`, not a corrupted call frame; (3) a label AFTER
    the `for` over a `return`-bearing iterator → must be `sxSat` (reachable via the
    non-return path), proving paths aren’t silently dropped.
  - *Deferred forms* (first-class iterator value, recursive iterator) confirmed
    still `sxUnknown` (documented incompleteness, not regressions).
- All degradations (`break`/`continue`/`return`/recursion/`defer`/post-`transf`
  lowering) are **mechanized pre-scans** (D2 step 0), never silent mis-models.

## Implementation path (`/tdd`)

1. **S1 — inline direct-call iterator into `for`.** Detection (D1, inserted AFTER
   the items/pairs dispatch) + the D2 step-0 mechanized pre-scans (getImpl-shape,
   `return`, `break`/`continue`, recursion, default-params) + transform (D2 steps
   1–4); reuse `maxLoopUnwind`. RED set per Consequences (positive + the 3
   false-positive-direction tests). **Bump v29→v30 + both pins.**
2. **S2 — lift restrictions:** `break`/`continue` for while-driven iterators where
   targeting is provably correct; tuple yields `for a, b in it()` (guard the
   multiple-loop-var case at `dsl_parser.nim:2010` `expectKind nnkSym` — S2 handles
   `n[0]..n[^3]` as several loop-var syms, SF-3); nested iterators. Each modelled
   faithfully or soundly degraded. Bump if verdicts change.
3. **S3 (deferred, separate) — first-class resumable iterators** (D6).

Each slice: full both-backend `dt-bounded` sweep; never restructure a SUT to pass
— escalate as a BLOCKER; soundness-gate any construct we cannot model (degrade to
`sxUnknown`, never a wrong verdict).
