# RFC-z3-optional — handoff

- **Stage:** 2 (architect) — **round 1 COMPLETE + mechanism resolved & spiked**
- **Round:** 1 done (5 lenses: depth, breadth, design, feasibility, liveness)
- **Mechanism:** RESOLVED — **design D** ("stop auto-wiring the seam").
  Corey-approved 2026-08-28. Both unknowns spike-proven green.
- **Resume:** `/tdd docs/RFC-z3-optional.md S1a`

## Context

Follow-on to issue #160, filed after v0.6.0 shipped. Branch `rfc-z3-optional`
off `main` at `1f50752` (v0.6.0). Nothing implemented yet — RFC + slices only.

## Slices (re-sliced for design D — ~3 files, was 7-8)

- [ ] **S1a** — relocate the bridge builder to `src/nelli/concolic.nim`:
      `import ./symex; export symex`, `classifyStrategyExpr`/`bindingExprFor`
      moved verbatim from `fuzzmacro.nim:526-643`, plus a new
      `concolicAssist(prop, strat)` macro holding `fuzzmacro.nim:797-823`'s
      logic. Core still auto-wires — **pure relocation, zero behavior change**.
      DoD: full `nimble test` green.
- [ ] **S1b** — **produces the load-bearing property, both halves.** Core
      gains the 4-arg `fuzz` overload (param literally named `assist`), drops
      `import ./symex`/`export symex`, builds no bridge;
      `tfuzzconcolicbridge_real` adds the import + `assist =` arg. DoD: probe
      compiles Z3-free AND the 0xCAFEBABE gate test green with its
      positive-signal checks; plus negative control + diagnostic surface.
- [ ] **S1c** — `fuzzConcolic` sugar over `concolicAssist`. Separable.
- [ ] **S2** — pin the probe in CI (`fuzzer-windows.yaml`), corrected flags.
      Pins half (1) only — state the half-(2) coupling.
- [ ] ~~**S3**~~ — **deleted**, pre-verified green and had no achievable RED.
- [ ] **S4** — consumer docs + build matrix + missing-libz3 behavior.
- [ ] **S5** (new) — release mechanics: 0.7.0, CHANGELOG, downstream note,
      fix stale `nelliVersion = "0.1.0"` at `src/nelli.nim:20`.

## Open forks (awaiting Corey)

None. The mechanism fork closed on design D.

## Spike results (2026-08-28, `localhost/nelli-dev:latest`)

Artifacts in `scratchpad/z3spike/` (throwaway; safe to delete).

- Assist expression semchecks in the **caller's** scope and splices into core's
  `quote do` — **yes**, positional and named. Proven by branch-count: a
  2-branch property returned 2, a 1-branch property 1.
- 2-/3-/4-arg `fuzz` overloads coexist — **yes**.
- Core-only consumer with the walker unreachable compiles, `assist=NONE`.
- `fuzzConcolic` sugar works.
- **Gotcha:** the named-arg form needs the macro param literally named
  `assist`; `assistExpr` fails with "unknown named parameter: assist".
- **Real-tree half (1) proven:** with symex dropped, both bridge arms nil'd and
  the classifier removed, `tests/tz3free_probe.nim` printed `z3-free probe OK`.
  Patch reverted; `tests/tz3free_probe.nim` is kept (untracked → commit in S1b).
- **Design refinement the spike forced:** `classifyStrategyExpr`/
  `bindingExprFor` reference `ccoEq` from the Z3-importing `smt/runtime.nim`
  and must move WITH the bridge — hence `concolicAssist(prop, strat)` takes the
  strategy too. Without it: `fuzzmacro.nim(628): undeclared identifier: 'ccoEq'`.

## Round 1 findings (all 5 lenses, verified against `1f50752`)

- **Unanimous CRITICAL:** `concolicFlip` is a **macro** (`symex.nim:1247`),
  not a proc. It does compile-time AST capture via `parseEntryImpl`
  (`smt/dsl_parser.nim:8850`) and splices a `SymexProgram` IR literal +
  `runConcolicFlipImpl` into the caller. A runtime proc-var cannot route it.
  The real seam is **parse/IR (Z3-free) vs walk/solve (Z3-bound)**; only
  `symex.nim:22`, `smt/runtime.nim:28`, `smt/regex_parser.nim` import z3.
- **Probe flags unsound:** need `--skipUserCfg --noNimblePath`; drop the
  softlink path. Current baseline passes RED only by environment luck.
- **Liveness:** most Track-G tests don't discriminate; exactly one does.
- **Breaking change** (`export symex` removal) was undeclared; needs 0.7.0.
- **README already promises the target state** (`:91-95`) — this is a
  regression fix, and the v0.6.0 wiring broke a documented contract.

## Key decisions (this session)

- ~~**Feasibility resolved before writing the RFC, not assumed.**~~
  **OVERTURNED IN ROUND 1.** The stage-1 conclusion — "the only walker-bound
  symbol is `concolicFlip`, a proc — exactly what a hook routes" — was wrong.
  It inspected only `fuzzmacro`'s *pre-expansion* output. `concolicFlip` is a
  macro; post-expansion the spliced code carries the walker's IR surface. The
  issue's original open question ("does the hook signature have to widen?")
  resolves **yes**, or is dispensed with entirely by compile-time gating.
  The four-type claim itself still holds (verified `smt/runtime.nim:12687-12732`),
  but the inventory was incomplete — enum *values* and three static defaults
  were missed.
- **The type move is no longer needed.** R29b's precedent was real, but under
  design D core constructs no bindings, so the four types / enum values /
  static defaults stay put in `smt/runtime.nim` — they are only needed where
  the bridge is built, which is now `nelli/concolic` (which imports symex
  anyway). Round 1 correctly found the draft's inventory incomplete; the right
  fix turned out to be deleting the requirement, not completing the list.
- **Verification channel simplified** (still true), **but the flag set was
  wrong.** `--skipProjCfg --skipParentCfg` misses `~/.config/nim/nim.cfg` and
  the nimblepath; add `--skipUserCfg --noNimblePath`. "Local, seconds" also
  assumed a host Nim, which does not exist — the probe runs in the podman
  image. Corrected invocation is in the RFC.
- **RED baseline captured and re-confirmed under the corrected flags:**
  `src/nelli/symex.nim(22, 8) Error: cannot open file: z3`, rc=1. Then proven
  invertible — see §Spike results.
- **Design D approved by Corey 2026-08-28**, together with spike-before-slice
  sequencing.

## Review ledger (stage 4)

Not started.
