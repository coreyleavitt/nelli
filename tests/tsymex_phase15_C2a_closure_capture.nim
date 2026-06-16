## Phase 15 — Cluster C, cycle C2a: closure CONSTRUCTION. When the walker
## lowers an `iekLambda`, it (1) snapshots the captured locals from the CURRENT
## env into an `svTuple` `envRecord`, (2) get-or-creates the per-site
## uninterpreted `funcSym` (memoized in the `currentClosureSyms` threadvar,
## mirrored into `WalkerStatics.closureSyms`), and (3) binds the resulting
## `svClosure{closureSite, closureEnv, closureRawFD}` into the env under the
## let-binding name. The `iekClosureCall` arm STAYS `ceNotImplemented` (C2b
## wires application). See `docs/symex/ADR-0009-closure-encoding.md`.
##
## CONSTRUCTION ONLY — no full `symexFind` body descent (`f(3)` would hit the
## still-stubbed `iekClosureCall`). The test introspects the CONSTRUCTED
## `svClosure` via the `c2aClosureProbe` test hook, which (in runtime.nim, where
## the non-exported `Env`/`lower` live) builds the construction-time env, lowers
## an `iekLambda` against it (the `let f = …` binding point), and returns a
## plain probe record of the resulting `svClosure` for assertion — never
## descending into the body.
##
## C2a is ADDITIVE under walker version "8" (no bump; Cluster C bumps at C6).
import std/[unittest]
import proptest/smt/runtime

# The reference SUT (per RFC §C2a) the construction models:
#
#   proc sut(x: int): int =
#     let offset = x * 2
#     let f = proc(y: int): int = y + offset
#     f(3)
#
# At the `let f = …` binding point the env holds `offset` (== x*2) and an
# `unrelated` local. The walker constructs an `svClosure` whose `closureEnv` is
# an `svTuple` with ONE field ("offset") — the captured `offset` SymVal — and
# the `unrelated` local is NOT snapshotted.

suite "symex Phase 15 C2a — closure construction (env snapshot + per-site funcSym)":

  test "C2a: closure capturing a local, resulting svClosure.closureEnv contains correct captured SymVals":
    let p = c2aClosureProbe()

    # The result is an svClosure carrying the site key.
    check p.isClosure
    check p.siteHash == 4242'i64
    check p.declOrder == 0

    # closureEnv is an svTuple with EXACTLY ONE field — the captured `offset` —
    # and the unrelated local is NOT snapshotted.
    check p.envIsTuple
    check p.envFieldNames == @["offset"]
    check p.envFieldCount == 1

    # The snapshotted field VALUE equals the captured `offset` SymVal
    # (same Z3 representation hash).
    check p.capturedFieldMatchesOffset

    # The per-site uninterpreted funcSym was declared (closureRawFD non-nil)
    # and memoized in the closureSyms cache.
    check p.funcDeclIsLive
    check p.closureSymsLen == 1

  test "C2a: same site re-lowered reuses the memoized funcSym (one entry)":
    # Two lowerings of the SAME site against the SAME env/param sorts ⇒ ONE
    # memoized funcSym entry (the get-or-create memoization).
    let p = c2aClosureProbeRelowered()
    check p.isClosure
    check p.closureSymsLen == 1

  test "C2a: construction adds NO Z3 assertion / no body descent":
    # The lambda body (`y + offset`) is never lowered at construction — only
    # the funcSym is declared and the env snapshotted. closureEnv is exactly
    # the captured snapshot (one field), proving no body evaluation happened.
    let p = c2aClosureProbe()
    check p.isClosure
    check p.envFieldCount == 1
    check p.assertionCountDuringConstruction == 0
