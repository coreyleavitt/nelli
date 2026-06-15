## Phase 15 — Cluster S, cycle S1: string type-bridge migration.
##
## Byte-faithful model (ADR-0006): `string` is a Z3 String whose characters
## will be constrained to ≤ 0xFF (Latin-1) so Z3 position == Nim byte. S1
## adds the `iekStr*` IR scaffolding + `smkStr*` stdlib-model stubs and the
## `string.len` parse-routing guard; the op semantics arrive in S2–S11.
##
## This cycle proves:
##   1. A `string` SUT param round-trips through the Phase-5 baseline:
##      `s == "hello"` is `sxSat`, witness == "hello".
##   2. `s.len` on an `itString` receiver lands on `isUnsupported`
##      (a clean parse boundary) rather than mis-routing to `iekSeqLen`
##      and crashing on a Z3String sort mismatch. It surfaces as
##      `sxUnknown` (S3 fleshes the real `iekStrLen` lowering).
import std/unittest
import proptest/symex

proc isHello(s: string) =
  if s == "hello":
    symexTarget("hello")

proc lenGt3(s: string) =
  if s.len > 3:
    symexTarget("long")

suite "symex Phase 15 S1 — string type-bridge":
  test "string SUT param: walker accepts, Z3 returns model, evalStr extracts":
    let r = symexFind(isHello, tLabel("hello"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "s.len on itString receiver -> isUnsupported (clean, not a crash)":
    let r = symexFind(lenGt3, tLabel("long"))
    # The `s.len` op is not modeled until S3; the statement lands on
    # `isUnsupported`, so the target is never provably reached -> sxUnknown.
    check r.status == sxUnknown
