## RFC-parser-normalization (#146), review finding H2 — behavioral pin for
## the `ctx.inGuardCond` carve-out in `parseAtomicOperand`
## (`src/nelli/smt/dsl_parser.nim`, ~:1310: `if ctx.inGuardCond or
## isAtomicIR(ir) or n.typeKind == ntyNone: return ir`).
##
## Prior to this file, the carve-out had NO behavioral test — only a
## marker-string audit (grepping `dsl_parser.nim` for the carve-out's
## presence). This file pins the actual soundness contract it protects: a
## `while`-guard whose condition contains a compound, FAULT-FREE operand
## (`(i and 7) != 5` — bitwise `and`, which deposits no inline defect-fork
## of its own) plus a `continue` in the loop body must still resolve to a
## REAL verdict (`sxSat`/`sxUnsat`, never `sxUnknown`) via
## `mkShortCircuitWhile`'s Case-4 fast path ("no preamble needed at all").
##
## Why bitwise `and`, not `+`/`-`: `tsymex_phase15_A1_loopguard.nim`'s own
## cell (b) is the RFC's NAMED demonstrative cell for this exact shape
## ("compound fault-free guard operand + continue in body"), but it uses
## `i < n + 1` and is pinned there as a BLOCKER — `+`'s own inline
## overflow-check fork deposits a preamble entry independently of
## `parseAtomicOperand`'s hoist decision, so that cell degrades to
## `sxUnknown` even WITH the carve-out intact and cannot isolate the
## carve-out's own effect. Bitwise int ops (`and`/`or`/`xor` on `int`,
## Nim's genuinely bitwise family per the classify-first A2b split — never
## the boolean short-circuit family) carry no such fork, so this file's SUT
## is the first shape able to actually witness the carve-out in isolation.
##
## Mechanism: `(i and 3) < 3` as a `while`-guard has top-level operator `<`
## (NOT `and`), so it parses through `mkShortCircuitWhile`'s plain
## (non-and-split) branch: `parseExpr(guardNode, tmpPre, ctx)`. `<`'s LHS
## operand `(i and 3)` is a compound `IRExpr` (not `isAtomicIR`), so
## `parseAtomicOperand` is the ONLY thing standing between it and a hoisted
## `let`. With the carve-out intact (`ctx.inGuardCond` set for the whole
## guard-tree parse), `parseAtomicOperand` no-ops and `tmpPre` stays empty
## → Case 4 (plain `mkWhile`) → `continue` cannot go stale (the guard is
## fully re-evaluated every real iteration by construction) → the run
## resolves to a real verdict. Remove the carve-out and `(i and 3)` gets
## hoisted into `tmpPre`, `mkShortCircuitWhile` sees a non-empty preamble
## with a `continue`-bearing body, and Case 3 (R14 sound-degrade) fires —
## the verdict degrades to `sxUnknown`.
##
## NOTE on operator choice: `!=` was tried first and empirically does NOT
## witness this — Nim's typed AST desugars `a != b` to `not (a == b)`, and
## something in the `nnkPrefix "not"` traversal ends up depositing a guard
## preamble regardless of the carve-out, landing in Case 3 even with the
## carve-out intact (a distinct, pre-existing shape gap, out of this pin's
## scope — recorded here only so a future reader does not "simplify" this
## file back to `!=` and reintroduce a non-witnessing pin). `<` parses as a
## direct `nnkInfix` and cleanly reaches Case 4, as required.
##
## RED-VERIFIED (per the task's TDD discipline): with `ctx.inGuardCond or `
## temporarily deleted from the `parseAtomicOperand` condition
## (`dsl_parser.nim` ~:1310), this file's pinned test goes RED — the
## verdict degrades from `sxSat` to `sxUnknown`, exactly as the mechanism
## above predicts. The deletion was reverted immediately after confirming
## RED; `git diff -- src/nelli/smt/dsl_parser.nim` is clean in the commit
## that adds this file.
import std/[unittest, strutils]
import nelli/symex

# ---------------------------------------------------------------------------
# SUT: while-guard `(i and 3) < 3` — a compound, FAULT-FREE bitwise operand
# (no overflow/div-by-zero/index-oob fork of its own) — with a `continue` in
# the body. `i` runs 0, 1 (skipped via `continue`, so NOT counted into
# `acc`), 2 before the guard's low-2-bits reach 3 and the loop exits (4
# guard evaluations total, i = 0,1,2,3 — well within the default
# `maxLoopUnwind` of 5, so the k-unroll budget cannot itself be the reason
# this proves); `acc` is therefore deterministically 2 on exit regardless of
# `n`. `n` is the actual search variable — the target additionally requires
# `n == 7`, so this is a real Z3 search, not a trivially-reachable target.
# ---------------------------------------------------------------------------
proc sutGuardCondCarveOut(n: int) =
  symexAssume(n >= 0 and n < 1_000)
  var i = 0
  var acc = 0
  while (i and 3) < 3:
    if i == 1:
      inc i
      continue
    acc += 1
    inc i
  if acc == 2 and n == 7:
    symexTarget("hit")

suite "symex A2a — ctx.inGuardCond carve-out behavioral pin (review finding H2)":

  test "compound bitwise guard operand + continue in body resolves to a REAL verdict":
    ## Pins the Case-4 fast path: this must be `sxSat` (never `sxUnknown`).
    let r = symexFind(sutGuardCondCarveOut, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 7

  test "walker version floor: symexWalkerVersion >= 73":
    check parseInt(symexWalkerVersion) >= 73
