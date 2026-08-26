## RFC-fuzzer-nextgen G4 — confirms the Nim-tier comparison hook
## (`{.covercmp.}`/`logCmp`, `coverage.nim`) does NOT reopen the walker gap
## G3fix closed. `logCmp` carries the SAME local `{.symexOpaque.}` pragma
## `recordEdge` does, so the walker must treat a call to it exactly like a
## call to `recordEdge`: no descent, no crash on `cmpLogMode`'s free-standing
## threadvar. Mirrors `tsymex_g3fix_walkergap.nim`'s shape (same magic-byte
## gate, same `concolicFlip` call), but the property here is BOTH
## `{.cover.}`'d AND `{.covercmp.}`'d — the exact "concolic-walked and
## cmp-instrumented" combination G4's brief calls out.
import std/unittest
import nelli
import nelli/symex

proc coveredMagicCmpGate(drawnInt: int) {.cover, covercmp.} =
  if drawnInt == 0xCAFEBABE:
    symexTarget("magic_hit")
  else:
    symexTarget("magic_miss")

suite "RFC-fuzzer-nextgen G4 — concolicFlip over a {.cover, covercmp.}'d property":

  test "the walker does not choke on logCmp's free coverageMode-shaped ref (cmpLogMode)":
    let trace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(coveredMagicCmpGate, trace, bindings, 0)
    check r.outcome == cfoSolvedExact
    check r.materialized.len == 1
    check $r.materialized[0] == "int(3405691582)"   # 0xCAFEBABE
    check r.coverage == ccoIntendedCovered
