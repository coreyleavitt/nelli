# RFC-z3-optional — handoff

- **Stage:** 2 (architect) — **round 1 COMPLETE, applied to the RFC**
- **Round:** 1 done (5 lenses: depth, breadth, design, feasibility, liveness)
- **BLOCKED:** §Mechanism is an open decision awaiting Corey. S1b/S1c cannot
  be written until A/B/C is picked.
- **Resume after sign-off:** `/architect docs/RFC-z3-optional.md round 2`

## Context

Follow-on to issue #160, filed after v0.6.0 shipped. Branch `rfc-z3-optional`
off `main` at `1f50752` (v0.6.0). Nothing implemented yet — RFC + slices only.

## Slices (re-sliced in round 1 — old S1 was a round, not a slice)

- [ ] **S1a** — pure type move: 4 binding types + 3 static defaults from
      `smt/runtime.nim` → `smt/concolictaxonomy.nim`. Keep the **module-level**
      re-export (enum values depend on it). DoD: full `nimble test` green.
- [ ] **S1b** — the seam, bridge-absent half (**blocked on §Mechanism**).
      Ships the negative control + the diagnostic surface.
- [ ] **S1c** — the registrar; **produces the load-bearing property**. DoD:
      `tfuzzconcolicbridge_real`'s 0xCAFEBABE gate test red on S1b, green here.
- [ ] **S1d** — drop `import ./symex` / `export symex` from `fuzzmacro`; the
      Z3-free probe goes green.
- [ ] **S2** — pin the probe in CI (`fuzzer-windows.yaml`), corrected flags.
      Pins half (1) only — state the half-(2) coupling.
- [ ] ~~**S3**~~ — **deleted**, pre-verified green and had no achievable RED.
- [ ] **S4** — consumer docs + build matrix + missing-libz3 behavior.
- [ ] **S5** (new) — release mechanics: 0.7.0, CHANGELOG, downstream note,
      fix stale `nelliVersion = "0.1.0"` at `src/nelli.nim:20`.

## Open forks (awaiting Corey)

- **§Mechanism (A / B / C).** The draft's runtime registry cannot be built —
  `concolicFlip` is a macro. Three repairs; recommendation is **(A)
  `when declared` caller-scope gating**, with (B) explicit
  `GuidanceConfig.solver` the serious rival and (C) dominated. This overturns
  a baked-in RFC assumption, hence escalated rather than edited.

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
- **Precedent exists in-tree:** R29b already moved `ConcolicFlipResult` into
  `smt/concolictaxonomy.nim` for this same reason. S1's type move is the same
  move, not a novel one.
- **Verification channel simplified** (still true), **but the flag set was
  wrong.** `--skipProjCfg --skipParentCfg` misses `~/.config/nim/nim.cfg` and
  the nimblepath; add `--skipUserCfg --noNimblePath`. "Local, seconds" also
  assumed a host Nim, which does not exist — the probe runs in the podman
  image. Corrected invocation is in the RFC.
- **RED baseline captured** so S1 has something to invert:
  `src/nelli/symex.nim(22, 8) Error: cannot open file: z3`, rc=1.

## Review ledger (stage 4)

Not started.
