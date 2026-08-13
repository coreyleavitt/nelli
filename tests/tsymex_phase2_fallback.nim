## Phase 2 — abstraction declines under bit-twiddling.
##
## Per ADR-0001, an integer's def-use chain that contains any
## `shl`/`shr`/`and`/`or`/`xor` operation makes Z3Int abstraction
## unsound (the BV semantics don't agree with Int semantics on
## bit-twiddling). The walker must detect this and *decline*
## promotion even when the variable's range would otherwise fit
## the BV window.
##
## Observable: the variable stays in its BV encoding, the
## `AbstractionLog` does not list it, and operations on it work
## (no runtime errors from a stale Z3Int handle).
import std/unittest
import nelli/symex

suite "symex Phase 2 — bit-twiddling declines promotion":
  test "plain int with no range info stays BV; audit log empty":
    # No type-derived range → nothing to promote even under
    # `isOptimised`. The witness should still work end-to-end.
    proc plainArith(x: int) =
      if x == 42:
        symexTarget("hit")
    let r = symexFind(plainArith, tLabel("hit"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] == 42
    check r.abstractions.len == 0

  test "shr on a range param declines promotion":
    proc twiddle(x: range[0..100]) =
      if (x shr 1) == 25:
        symexTarget("hit")
    let r = symexFind(twiddle, tLabel("hit"), optimisedSymexSettings())
    check r.status == sxSat
    # 2*25 = 50, 2*25+1 = 51; both in [0..100].
    check (r.witness[0] shr 1) == 25
    # x must have stayed BV — the audit log should reflect the decline.
    check r.abstractions.len == 0
