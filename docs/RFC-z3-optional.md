# RFC — make `import nelli` Z3-free by inverting the concolic bridge

**Issue:** #160 · **Branch:** `rfc-z3-optional` (off `main` at v0.6.0, `1f50752`)
**Status:** stage 1 (RFC + slicing)

## §0 — Thesis

`import nelli` forces every downstream consumer to resolve Z3 at compile time,
to serve a capability that is **runtime-off by default**. A consumer using only
`property`/`StateMachine`/`forAll` — or `fuzz(...)` without concolic assist —
pays the heaviest native dependency in the tree for code it never executes.

Invert it: the core owns a nil-defaultable bridge hook expressed in already
Z3-free leaf types; the walker-touching implementation moves to an opt-in
module that registers into that hook. `import nelli` stops reaching Z3;
`import nelli/concolic` restores today's behavior.

## Ground truth — verified, not assumed (2026-08-28)

Every claim below was checked against the tree at `1f50752`.

**The chain is real.** `nelli.nim:22` imports/exports `fuzzmacro`;
`fuzzmacro.nim:49` does an unconditional `import ./symex`, `:51` `export symex`;
`symex` reaches the walker, which imports `z3`.

**Proven RED, with a repro:**

    nim c --hints:off --skipProjCfg --skipParentCfg \
          --path:src --path:_deps/softlink/src <probe importing nelli>
    => src/nelli/symex.nim(22, 8) Error: cannot open file: z3   (rc=1)

**The runtime path is already off by default.** `GuidanceConfig.stallRounds`
defaults `0`, and `tryConcolicBridge` early-returns unless the bridge is
non-nil AND `stallRounds > 0` AND the frontier is stalled. So the link is
unconditional for a feature almost nobody runs.

**`fuzz.nim` already proves the separation works.** It imports
`./smt/concolictaxonomy` (`:21`) and stays Z3-free; that leaf module's own doc
records that none of its types reference Z3. R29b moved `ConcolicFlipResult`/
`ConcolicFlipCounters` there for exactly this reason — the precedent is in-tree.

### The crux, resolved

The issue flagged one risk: if the macro's spliced codegen inlines walker-*typed
expressions* rather than a single call, the hook signature must widen. It does
not. The emitted closure (`fuzzmacro.nim:801-823`) references exactly:

| Symbol | Nature | Disposition |
|---|---|---|
| `concolicFlip` | proc (`symex.nim`, walker) | route through the hook |
| `ConcolicParamBinding`, `ConcolicBindingKind` | variant over `int`/`int64`/`bool` | **pure data — movable** |
| `ConcolicConjunct`, `ConcolicConjunctOp` | `drawIndex`, `a`, `b`, `op` | **pure data — movable** |
| `ChoiceNode`, `ConcolicBridgeResult`, `wckIf` | already Z3-free | unchanged |

None of the four data types reference a Z3 type. `bindingExprFor`'s own doc
(`fuzzmacro.nim:594-599`) settles it: it emits "primitive int64/enum literals
only — `runtime.nim` never sees this module's descriptor tree at all".

**So the only genuinely walker-bound symbol in generated code is a proc** —
precisely what a registry hook routes. No signature widening.

## Load-bearing property

> **A module that does `import nelli` compiles with no Z3 on the path, and
> adding `import nelli/concolic` restores end-to-end concolic solving.**

Both halves, or it has not landed. The first half alone is achievable by
deleting the feature; the second half is what proves the seam rather than a
removal. Slice 1 produces both.

## Verification channel — cheaper than the issue assumed

The issue proposed a Z3-free CI image. Not required. Withholding the z3
`--path` under `--skipProjCfg --skipParentCfg` makes any transitive `import z3`
fail at Nim compile time, which is the dependency we care about — z3 binds via
softlink/dynlib, so there is no separate static-link step to catch. This is
deterministic, local, runs in seconds, and needs no new image.

A CI leg still gets added (the check must not depend on someone remembering to
run it), but it is a step in an existing leg, not new infrastructure.

## Slices — producer first

Ordered so the load-bearing property runs end-to-end at slice 1; later slices
harden rather than complete it.

- **S1 — the seam, end to end (the crux).** Move the four binding types to
  `smt/concolictaxonomy.nim` (pure move, re-exported from `runtime.nim` so
  nothing breaks). Add the nil-defaultable registration hook. Create
  `nelli/concolic` as the sole walker importer, registering the real
  `concolicFlip`. Drop `import ./symex` / `export symex` from `fuzzmacro`.
  **DoD:** the Z3-free probe compiles AND an existing Track-G test passes
  unchanged with `import nelli/concolic` added. Both, in one slice — this is
  the property, not scaffolding for it.

- **S2 — pin it in CI.** Add the Z3-free compile check as a step so the
  property cannot silently regress. Must fail loudly if `import nelli` ever
  reaches Z3 again.

- **S3 — audit the rest of the umbrella.** `fuzzmacro` is the known path;
  confirm no *other* `nelli.nim` re-export (`fuzzworker`, `parallel`, …) drags
  Z3 in by another route. Purely a verification slice — it ships a test, and
  a fix only if it finds one.

- **S4 — consumer-facing docs.** `docs/fuzz/USAGE.md` + README: state that
  concolic assist needs one extra import, and why. Small, but the feature is
  undiscoverable otherwise.

No slice ships a consumer without its producer: S1 delivers hook *and*
registrar together; the hook is never merged nil-only with "a later slice
registers it."

## Risks

- **Macro hygiene at the splice site.** Generated code resolves identifiers in
  the *caller's* scope. Moving types must keep them reachable via
  `import nelli` alone (they are re-exported from a Z3-free leaf, so this
  should hold) — but `fuzzmacro.nim:53-64` records a real prior footgun here,
  so S1 must prove it with a macro-call-site test, not a unit test.
- **Silent regression.** Without S2, any future `import` in the wrong module
  reintroduces the dependency invisibly. S2 is not optional polish.
- **Registration timing.** A registry populated at module-init must be
  registered before the first `fuzz(...)` call that needs it. Nim module init
  order is deterministic, but S1 should assert the failure mode: bridge absent
  ⇒ concolic silently skipped (today's default behavior), never a crash.

## Non-goals

- No `-d:nelliConcolic` compile flag. Too coarse — whole-compilation switch,
  bifurcates macro codegen, cannot vary per call site.
- No change to `fuzz(...)`'s public signature or default runtime behavior.
- Not making Z3 optional for `nelli/symex` itself — that module *is* the
  walker; a consumer importing it is asking for Z3 by definition.
