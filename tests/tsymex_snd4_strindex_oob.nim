## RFC-chapulin-hardening SND-4 (ADR-0024, walker v59) — Cluster 1 (Soundness).
##
## Fixes a soundness UNDER-approximation (false "no defect"): string character
## index reads (`s[i]`, IR kind `iekStrAt`) had ZERO `IndexError`/`IndexDefect`
## modeling, unlike seq/array/Table indexing (which already fork a defect via
## the unconditional `forkDefect` in the `isIndex` walk arm, Phase 16 D1a).
## `lowerStrArm`'s `iekStrAt` arm (`runtime_strings.nim`) computed
## `toCode(at(recv.str, idxZi))` with no bounds check: Z3's `at`/`toCode` spec
## silently degrades an out-of-range `idxZi` to the empty string / -1 -> BV8
## 0xFF, so an OOB `s[i]` read never crashed and never forked — a
## `tIndexError()` search over `s[i]` returned `sxUnsat` ("no OOB reachable")
## EVEN WHEN AN OOB WAS REACHABLE.
##
## THE FIX (never re-derive; this suite pins it): mirrors the EXISTING
## `parseIntRaiseConds`/`divByZeroConds`/`overflowConds` lowering-sink ->
## drain-fork pattern EXACTLY (never fork inline from `lower()` — SND-3's
## anti-pattern). `iekStrAt` deposits `oob = idx<0 or idx>=len(s)` into the new
## `strIndexOobConds` threadvar/WalkCtx-field sink (`syncStrIndexOobCond`);
## `drainStrIndexRaises`, folded into `drainScalarRaiseForks` as a 4th stage
## (after parseInt / divByZero / overflow), forks the OOB sub-path as a routed
## `IndexDefect` and asserts the negation onto the survivor's
## `defectSurvivorPc` (ADR-0012) — the same "digits continuation" shape as
## `drainParseIntRaises`.
##
## Every test in this file asserts the SAME verdict is expected on BOTH the
## `c` and `cpp` backends (run via `scripts/dt-bounded.sh c|cpp`) — pinning
## `c == cpp` is the entire point of this soundness class.
##
## Bumps `symexWalkerVersion` 58->59 (verdict-surface change: `s[i]` now forks
## `IndexDefect`, and every string-index continuation gains an implicit
## `not oob` fact — a real bounds correction, not a new witness shape).
## `renderAsChoicesVersion` STAYS "7" — IndexError is a raise (surfaced via
## `raisedWitness`), not a rendered `witness` shape.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------
#
# NOTE: every SUT below binds the index read to a `let` (`let c = s[...]`)
# rather than a bare `discard s[...]`. A bare `discard <expr>` for anything
# other than `getCurrentException[Msg]`/`parseInt`/`parseBiggestInt` is
# DROPPED by the parser (`dsl_parser.nim`'s `nnkDiscardStmt` arm) — it never
# reaches the walker at all. `let c = s[...]; discard c` is the established
# idiom for this in the codebase (see
# `tsymex_phase16_D1a_defect_routeraise.nim`'s `uncaughtIndexed`:
# `let v = arr[i]; discard v`).

# 1. Tracer — concrete OOB-reachable index on an unconstrained string.
proc sutBareOobIndex(s: string) =
  let c = s[5]
  discard c

# 2. Scan-then-OOB — the Q1-spike repro. `find` returns -1 when absent (so
# `s[0]` on the -1+1=0 path is in-bounds when s is non-empty) but when ":" IS
# found at the last byte, `i+1 == s.len` -> OOB is reachable.
proc sutScanThenOob(s: string) =
  let i = s.find(":")
  let c = s[i + 1]
  discard c

# 3. Bounds-safe — precision test: the index is PROVABLY in-bounds under the
# guard. Proves the fork does not over-report (no false defect). Load-bearing.
proc sutBoundsSafe(s: string) =
  if s.len > 5:
    let c = s[2]
    discard c

# 4a. Continuing path carries `not oob` — a reachability target gated on both
# the length guard AND the indexed char; must still resolve to a real `sxSat`
# with a satisfying witness (the new bounds fact must not corrupt the char's
# VALUE semantics on the survivor path).
proc sutReachableInBounds(s: string) =
  if s.len > 3 and s[3] == 'x':
    symexTarget("hit")

# 4b. Continuing path carries `not oob` — companion contradiction: forcing
# `s[3]` to be two different chars is UNSAT regardless of bounds, proving the
# survivor still computes a real verdict (not a fabricated default). The
# length guard is a SEPARATE, OUTER `if` (not `and`-combined with the index
# reads) so `s.len > 3` is already asserted into the path condition BEFORE
# `s[3]` is lowered — this makes the OOB raise path itself infeasible
# (`len(s) > 3` contradicts `3 >= len(s)`), so no independently-reachable
# raise can leak in and dominate the verdict via sxRaised>sxUnsat precedence
# (an `and`-combined guard does NOT give this pre-narrowing, since the whole
# conjunction lowers as one boolean expression before anything is asserted).
proc sutUnreachableContradiction(s: string) =
  if s.len > 3:
    if s[3] == 'x' and s[3] == 'y':
      symexTarget("contradiction_hit")

# 5. Negative index — isolates the `idx < 0` disjunct of the OOB condition
# (independent of the `idx >= len` disjunct: `len` is always >= 0, so `i < 0`
# alone already guarantees OOB regardless of `s`'s length).
proc sutNegativeIndex(s: string, i: int) =
  if i < 0:
    let c = s[i]
    discard c

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening SND-4 — string-index OOB IndexError (c==cpp)":

  test "SND-4-1 (tracer): s[5] on unconstrained s -> sxRaised IndexDefect (was sxUnsat)":
    let r = symexFind(sutBareOobIndex, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "SND-4-2 (Q1-spike repro): find(\":\") then s[i+1] -> sxRaised (scan-then-OOB reachable)":
    let r = symexFind(sutScanThenOob, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "SND-4-3 (load-bearing precision): s.len>5 guard makes s[2] provably in-bounds -> sxUnsat":
    let r = symexFind(sutBoundsSafe, tIndexError())
    check r.status == sxUnsat

  test "SND-4-4a: continuing path keeps real sxSat semantics (len>3 and s[3]=='x')":
    let r = symexFind(sutReachableInBounds, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len > 3
    check r.witness[0][3] == 'x'

  test "SND-4-4b: continuing path keeps real sxUnsat semantics (s[3] can't be 'x' and 'y')":
    let r = symexFind(sutUnreachableContradiction, tLabel("contradiction_hit"))
    check r.status == sxUnsat

  test "SND-4-5: negative index also forks IndexDefect -> sxRaised":
    let r = symexFind(sutNegativeIndex, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    check r.raisedWitness[1] < 0

suite "symex RFC-chapulin-hardening SND-4 — version pins":

  test "walker version floor >= 59 (SND-4 introduced at 59)":
    check parseInt(symexWalkerVersion) >= 59

  test "renderAsChoicesVersion floor >= 7 (SND-4 does NOT bump RC — IndexError is a raise, not a rendered witness shape)":
    check parseInt(renderAsChoicesVersion) >= 7
