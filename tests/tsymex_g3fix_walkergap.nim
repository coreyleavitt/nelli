## RFC-fuzzer-nextgen G3fix — walker gap surfaced wiring the real concolic
## bridge against a `{.cover.}`-instrumented property (every real in-process
## Nim `fuzz()` target gets coverage this way). Before this fix, the walker
## descended into nelli's own `recordEdge` (injected by `{.cover.}`) and its
## `if coverageMode == cmOff: return` guard crashed with an uncaught
## `KeyError: key not found: coverageMode` — `coverageMode` is a module-level
## `{.threadvar.}` in `coverage.nim`, never bound in the walker's `env`.
##
## Two-layer fix:
##   1. instrumentation opacity (primary) — `recordEdge` was tagged with a
##      local `{.symexOpaque.}` pragma (`coverage.nim`) so the parser never
##      registered/walked its body; a call to it built `mkOpaqueCall` (the
##      graceful machinery #137 gives `echo`/`writeFile`). Issue #163 slice 1
##      retagged it `{.symexTransparent.}`: a call to it in statement
##      position is no longer merely left unwalked, it is DELETED — the
##      parser emits `mkBlock(@[])`, the established no-op
##      (`smt/dsl_parser.nim`'s `hasSymexTransparentPragma`) — because
##      `recordEdge` is genuinely inert to the symbolic state, not just a
##      black box the walker should avoid. This file is now the pin proving
##      no route regressed to walking `recordEdge`'s/`logCmp`'s bodies after
##      that retag — see `tsymex_g4_cmpwalk.nim` for the sibling hook.
##   2. free-reference degrade (safety net) — `smt/runtime.nim`'s
##      `lower(iekVar)` no longer crashes on ANY unresolved free reference
##      while `wmFollowConcrete` (concolic collection); it havocs to a fresh
##      symbolic (same "PARAM refs stay free/havoc" precedent as Cluster H).
##      `wmExplore` keeps the old crash (mode-gated via `isFollowConcreteWalk`
##      — byte-identical).
import std/unittest
import nelli
import nelli/symex

proc coveredMagicGate(drawnInt: int) {.cover.} =
  ## The G2 magic-byte gate, now under REAL `{.cover.}` instrumentation —
  ## exactly how every real in-process `fuzz()` target reaches the walker
  ## once G3's real concolic bridge is wired (the crash this file's fix
  ## addresses; see the C4 headline end-to-end test in tfuzzconcolicbridge).
  if drawnInt == 0xCAFEBABE:
    symexTarget("magic_hit")
  else:
    symexTarget("magic_miss")

suite "RFC-fuzzer-nextgen G3fix — opaque instrumentation + free-ref havoc":

  test "concolicFlip over a {.cover.}'d property no longer crashes on recordEdge's free coverageMode ref":
    let trace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(coveredMagicGate, trace, bindings, 0)
    check r.outcome == cfoSolvedExact
    check r.materialized.len == 1
    check $r.materialized[0] == "int(3405691582)"   # 0xCAFEBABE
    check r.coverage == ccoIntendedCovered
