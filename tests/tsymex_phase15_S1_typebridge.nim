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
##   2. `s.len` on an `itString` receiver routes to the dedicated `iekStrLen`
##      path (NOT `iekSeqLen`, which would crash on a Z3String sort mismatch).
##      As of S3 the real `iekStrLen` lowering (Z3 `str.len`, byte-faithful) is
##      live, so `s.len > 3` is now `sxSat` (was `sxUnknown` in S1, when the op
##      was still an unmodeled stub). This assertion was updated when S3 shipped.
import std/unittest
import nelli/symex

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

  test "s.len on itString receiver -> iekStrLen (modeled as of S3, sxSat)":
    let r = symexFind(lenGt3, tLabel("long"))
    # S3 ships the real Z3 `str.len` lowering (byte-faithful), so a free `s`
    # with `s.len > 3` is satisfiable. (In S1 this was an unmodeled stub ->
    # sxUnknown; the assertion was updated when S3 made the op live.)
    check r.status == sxSat
