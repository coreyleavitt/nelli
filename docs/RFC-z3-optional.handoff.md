# RFC-z3-optional — handoff

- **Stage:** 1 (RFC + slicing) **COMPLETE** → next is stage 2 (architect)
- **Round:** —
- **Resume:** `/architect docs/RFC-z3-optional.md round 1`

## Context

Follow-on to issue #160, filed after v0.6.0 shipped. Branch `rfc-z3-optional`
off `main` at `1f50752` (v0.6.0). Nothing implemented yet — RFC + slices only.

## Slices

- [ ] **S1** — the seam end to end: move the four binding types to the Z3-free
      leaf, add the nil-defaultable hook, create `nelli/concolic` as sole
      walker importer, drop `fuzzmacro`'s `import ./symex`. **This slice
      produces the load-bearing property**; both halves (Z3-free probe compiles
      AND Track-G passes with the opt-in import) are its DoD.
- [ ] **S2** — pin the Z3-free check in CI so it cannot silently regress.
- [ ] **S3** — audit the other `nelli.nim` re-exports for a second Z3 route.
- [ ] **S4** — consumer docs (USAGE + README): concolic needs one extra import.

## Open forks (awaiting Corey)

None.

## Key decisions (this session)

- **Feasibility resolved before writing the RFC, not assumed.** The issue's own
  open question was whether the macro's spliced codegen needs walker *types* in
  the caller's scope (forcing a wider hook signature). Verified it does not:
  the four types it references (`ConcolicParamBinding`, `ConcolicBindingKind`,
  `ConcolicConjunct`, `ConcolicConjunctOp`) are pure data over int/int64/bool
  with zero Z3 references, and `bindingExprFor` emits "primitive int64/enum
  literals only". The only walker-bound symbol is `concolicFlip`, a proc —
  exactly what a hook routes.
- **Precedent exists in-tree:** R29b already moved `ConcolicFlipResult` into
  `smt/concolictaxonomy.nim` for this same reason. S1's type move is the same
  move, not a novel one.
- **Verification channel simplified.** The issue proposed a Z3-free CI image.
  Not needed: withholding the z3 `--path` under
  `--skipProjCfg --skipParentCfg` makes any transitive `import z3` fail at Nim
  compile time. z3 binds via softlink/dynlib so there is no separate static
  link to catch. Deterministic, local, seconds.
- **RED baseline captured** so S1 has something to invert:
  `src/nelli/symex.nim(22, 8) Error: cannot open file: z3`, rc=1.

## Review ledger (stage 4)

Not started.
