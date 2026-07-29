## RFC-chapulin-hardening R1B (short-circuit OOB-guard fix), folded into the
## same walker v61 landing as R1 (`tests/tsymex_r1_draingap.nim`).
##
## THE BUG (fully root-caused; this suite pins the fix): `s[i]` (`iekStrAt`,
## SND-4) and `parseInt(s)` (`iekStrToInt`, S10b) each deposit an inline
## defect-fork predicate into a threadvar sink (`strIndexOobConds` /
## `parseIntRaiseConds`, `runtime_strings.nim`) EVERY time they lower — this
## is how the SND-4/R16 machinery routes a real Nim raise. When one of these
## nodes sits on the RHS of a short-circuit `and`/`or` (e.g. `i < s.len and
## s[i] == 'x'`), Nim NEVER evaluates the RHS unless the LHS demands it. But
## `rhsHasInlineDefectFork` (`dsl_parser.nim`) did not recognise `iekStrAt`/
## `iekStrToInt` as inline defect forks in their own right (it only recursed
## into their sub-expressions), so D1c's `and`/`or` short-circuit modelling
## took its FAST flat-`mkBinop` path — evaluating the RHS UNGUARDED. The
## `s[i]` OOB fork then fired regardless of whether the LHS held, producing a
## FALSE `sxRaised(IndexDefect)` for a program that real Nim never raises on.
##
## THE FIX (two parts, see `symexWalkerVersion`'s doc comment in
## `canonicalize.nim` for the full writeup):
##   Part 1 — `iekStrAt`/`iekStrToInt` now self-report `true` in
##     `rhsHasInlineDefectFork`, forcing D1c's GUARDED path (`let sc = A; if
##     sc: (…; sc = B)`) for the once-evaluated arms: if/let/assign/return.
##     Evaluating the RHS's preamble only inside the LHS guard makes the OOB
##     predicate itself conjoined with the guard, so it correctly comes out
##     UNSAT when the LHS forbids the RHS.
##   Part 2 — a `while` guard is RE-EVALUATED every iteration, but D1c's
##     guarded-path preamble was hoisted ONCE before the loop (stale after
##     the first iteration: the guard variable never gets recomputed as the
##     loop variables advance). The `nnkWhileStmt` arm now restructures to
##     `while true: <guard preamble>; if not cond: break; <body>` whenever
##     the guard produced a hoisted preamble, so the guard (and its defect
##     fork) re-runs every pass — the fast path (no hoisted preamble) is
##     byte-identical to before.
##
## SCOPE NOTE: only `and`/`or` are modelled by D1c (both are fixed by this
## same self-report — the guard direction differs, not the mechanism). This
## file's "or" case (`sutOrGuardedOob`) is a direct analogue proving `or`
## is ALSO correctly guarded, not merely "unaffected".
##
## Every test in this file is checked on BOTH the `c` and `cpp` backends
## (`scripts/dt-bounded.sh c|cpp`) per project convention.
##
## `symexWalkerVersion` STAYS "61" — this fix lands as part of the same R1
## cycle (see `tests/tsymex_r1_draingap.nim`'s pin). `renderAsChoicesVersion`
## STAYS "7" (no new witness shape).

import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# Reduced loop-unwind budget for the for-NESTED while cases below. A
# defect-guarded scan nested inside another k-unrolled loop has an INHERENT
# path-frontier blowup at the default unwind of 5 (see `sutForNestedWhileOob`'s
# doc comment); a small unwind keeps the verdict decidable and these tests fast
# while still proving the ~2665 arm produces the correct guarded verdict.
const nestedLoopBudget = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxLoopUnwind = 3

# ---------------------------------------------------------------------------
# if-arm (once-evaluated)
# ---------------------------------------------------------------------------

proc sutIfGuardedOob(s: string) =
  var i = 0
  if i < s.len and s[i] == 'x':
    symexTarget("hitIf")

# ---------------------------------------------------------------------------
# let-arm (once-evaluated)
# ---------------------------------------------------------------------------

proc sutLetGuardedOob(s: string) =
  var i = 0
  let ok = i < s.len and s[i] == 'x'
  if ok:
    symexTarget("hitLet")

# ---------------------------------------------------------------------------
# return-arm (once-evaluated) — the guarded and/or expr IS the return value.
# ---------------------------------------------------------------------------

proc helperGuardedReturn(s: string, i: int): bool =
  return i < s.len and s[i] == 'x'

proc sutReturnGuardedOob(s: string) =
  var i = 0
  if helperGuardedReturn(s, i):
    symexTarget("hitReturn")

# ---------------------------------------------------------------------------
# while-arm (re-evaluated each iteration) — Part 2's target.
# ---------------------------------------------------------------------------

proc sutWhileGuardedOob(s: string) =
  ## Mirrors tests/tsymex_q1_scanlift.nim's Q1-4a `sutSkipWhileGuardImpossible`
  ## (a `==`-guard skip-while the Q1 scan-idiom recognizer deliberately does
  ## NOT lift, so it stays on this ordinary k-unroll path). `i` never outruns
  ## `s.len` inside the loop (the `and`-guard always checks bounds first), so
  ## "impossible" can never actually be reached.
  var i = 0
  while i < s.len and s[i] == ' ':
    inc i
  if i > s.len:
    symexTarget("whileImpossible")

proc sutWhileFindX(s: string) =
  ## Reachable-target companion: proves the restructured `while true` +
  ## break loop still finds a real, reachable target through several
  ## iterations, with a valid witness.
  var i = 0
  while i < s.len and s[i] != 'x':
    inc i
  if i < s.len:
    symexTarget("foundX")

proc sutWhileConcreteBound(s: string) =
  ## Concrete-bound loop (bound is a LITERAL, not `s.len`) — proves the
  ## `while true` + break restructuring does not hang and still terminates/
  ## behaves correctly on an ordinary bounded scan.
  var i = 0
  while i < 3 and s[i] == 'a':
    inc i
  if i == 3:
    symexTarget("allThreeA")

# ---------------------------------------------------------------------------
# for-NESTED while (parseIterBodyStmt context) — the SECOND `nnkWhileStmt`
# arm. A `while i<s.len and s[i]==c` inside a `for` body is parsed by
# `parseIterBodyStmt`'s own `nnkWhileStmt` case (~2665), which — like the
# top-level `parseStmtInner` arm — must route through `mkGuardedWhile` so the
# guard's inline OOB fork re-runs each iteration instead of being hoisted once
# (stale). Proves both arms are consistent.
# ---------------------------------------------------------------------------

proc sutForNestedWhileOob(s: string) =
  ## `while i<s.len and s[i]==' '` nested inside a `for` body — the inner
  ## while is parsed by `parseIterBodyStmt`'s own `nnkWhileStmt` case (~2665),
  ## the SECOND while-arm. The `==`-guard skip-while is NOT lifted by the Q1
  ## scan recognizer (it only matches `!=`), so it stays on the k-unroll
  ## `mkGuardedWhile` path — exercising that arm. `i` never outruns `s.len`
  ## inside the loop (the guard checks bounds first, short-circuiting `s[i]`),
  ## so real Nim never OOBs. RED (pre-fix, 2665 arm still hoisting the guard
  ## preamble once): sxRaised(IndexDefect) false positive; GREEN (post-fix,
  ## routed through mkGuardedWhile): NOT sxRaised.
  ##
  ## NOTE (cost): these for-nested cases run under a REDUCED `maxLoopUnwind`
  ## (see `nestedLoopBudget` below). Soundly modelling a defect-guarded scan
  ## NESTED inside another k-unrolled loop re-fires the `s[i]` OOB defect fork
  ## on every inner iteration across every outer iteration — an INHERENT
  ## nested-loop path-frontier blowup (the pre-R1B code was cheap only because
  ## it was UNSOUND: one stale hoisted fork). At the default unwind of 5 the
  ## frontier explodes to a bounded-runner timeout; a small unwind keeps the
  ## verdict decidable and the test fast while still distinguishing the fixed
  ## (guarded → NOT sxRaised) behaviour from the buggy (false sxRaised) one.
  var i = 0
  for k in 0 .. 0:
    while i < s.len and s[i] == ' ':
      inc i
  if i > s.len:
    symexTarget("forWhileImpossible")

proc sutForNestedWhileFindX(s: string) =
  ## Reachable-target companion: a for-nested scan that finds 'x' — proves the
  ## restructured for-nested loop still reaches a real, satisfiable target.
  var i = 0
  for k in 0 .. 0:
    while i < s.len and s[i] != 'x':
      inc i
  if i < s.len:
    symexTarget("forFoundX")

# ---------------------------------------------------------------------------
# or-guard analogue (D1c handles `and` and `or` via the SAME self-report;
# this proves `or` is correctly guarded too, not merely unaffected).
# ---------------------------------------------------------------------------

proc sutOrGuardedOob(s: string) =
  var i = 0
  if i >= s.len or s[i] == 'x':
    symexTarget("hitOr")

# ---------------------------------------------------------------------------
# Regression guards: genuinely UNGUARDED s[i] reads must STILL raise —
# proves the fix does not over-reach into non-short-circuit contexts.
# ---------------------------------------------------------------------------

proc sutIfNoGuardOob(s: string) =
  ## `if s[0] == 'x':` — the index read IS the if's own condition (not
  ## gated behind any `and`/`or`), so it is unconditionally evaluated —
  ## exactly like real Nim's `if COND:`. Must still genuinely OOB when s
  ## is empty.
  if s[0] == 'x':
    discard

proc sutWhileUnboundedOob(s: string) =
  ## No bound at all on `i` — a real, unguarded OOB read every iteration.
  ## This is R1's own fix (not R1B's); must not regress.
  var i = 0
  while s[i] == ' ':
    inc i
  symexTarget("afterUnbounded")

# ---------------------------------------------------------------------------
suite "symex R1B — once-evaluated arms (if/let/return): A and s[i] must NOT false-raise":

  test "R1B-if-1: i<s.len and s[i]=='x' -> IndexDefect is NOT reachable (sxUnsat, not sxRaised)":
    ## RED (pre-fix): sxRaised(IndexDefect) — the OOB fork fires unguarded.
    ## GREEN (post-fix): NOT sxRaised — the guard makes the OOB predicate UNSAT.
    let r = symexFind(sutIfGuardedOob, tRaisedExn("IndexDefect"))
    check r.status != sxRaised

  test "R1B-if-2 (reachable companion): \"hitIf\" is still a real sxSat":
    let r = symexFind(sutIfGuardedOob, tLabel("hitIf"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check r.witness[0][0] == 'x'

  test "R1B-let-1: let ok = i<s.len and s[i]=='x' -> IndexDefect NOT reachable":
    let r = symexFind(sutLetGuardedOob, tRaisedExn("IndexDefect"))
    check r.status != sxRaised

  test "R1B-let-2 (reachable companion): \"hitLet\" is still a real sxSat":
    let r = symexFind(sutLetGuardedOob, tLabel("hitLet"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check r.witness[0][0] == 'x'

  test "R1B-return-1: return i<s.len and s[i]=='x' -> IndexDefect NOT reachable":
    let r = symexFind(sutReturnGuardedOob, tRaisedExn("IndexDefect"))
    check r.status != sxRaised

  test "R1B-return-2 (reachable companion): \"hitReturn\" is still a real sxSat":
    let r = symexFind(sutReturnGuardedOob, tLabel("hitReturn"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check r.witness[0][0] == 'x'

suite "symex R1B — while-arm (re-evaluated each iteration): A and s[i] must NOT false-raise":

  test "R1B-while-1: i<s.len and s[i]==' ' skip-while -> IndexDefect NOT reachable":
    ## RED (pre-fix): sxRaised(IndexDefect) — the guard preamble is hoisted
    ## once before the loop and never re-evaluated, so it drifts stale.
    ## GREEN (post-fix): NOT sxRaised.
    let r = symexFind(sutWhileGuardedOob, tRaisedExn("IndexDefect"))
    check r.status != sxRaised

  test "R1B-while-2: \"whileImpossible\" degrades to sxUnknown (k-unroll), never a false sxRaised":
    ## This is the tests/tsymex_q1_scanlift.nim Q1-4a shape exactly.
    ## RED (pre-fix): sxRaised (false). GREEN (post-fix): sxUnknown.
    let r = symexFind(sutWhileGuardedOob, tLabel("whileImpossible"))
    check r.status == sxUnknown

  test "R1B-while-3 (reachable companion): \"foundX\" is a real sxSat with a valid witness":
    let r = symexFind(sutWhileFindX, tLabel("foundX"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check 'x' in r.witness[0]

  test "R1B-while-4: concrete-bound loop (while i<3 and s[i]=='a') still behaves — reaches i==3":
    ## Proves the `while true` + break restructuring does not hang and
    ## produces the same verdict as the pre-restructure `while cond: body`
    ## would have for a genuinely bounded scan.
    let r = symexFind(sutWhileConcreteBound, tLabel("allThreeA"))
    check r.status == sxSat
    check r.witness[0].len >= 3
    check r.witness[0][0] == 'a'
    check r.witness[0][1] == 'a'
    check r.witness[0][2] == 'a'

suite "symex R1B — for-NESTED while (parseIterBodyStmt arm): A and s[i] must NOT false-raise":

  test "R1B-fornest-1: for k: while i<s.len and s[i]==' ' -> IndexDefect NOT reachable":
    ## RED (pre-fix, the ~2665 arm still hoisted the guard preamble once):
    ## sxRaised(IndexDefect) — proves the SECOND while-arm had the same bug.
    ## GREEN (post-fix, routed through mkGuardedWhile): NOT sxRaised.
    let r = symexFind(sutForNestedWhileOob, tRaisedExn("IndexDefect"), nestedLoopBudget)
    check r.status != sxRaised

  test "R1B-fornest-2: \"forWhileImpossible\" degrades to sxUnknown, never a false sxRaised":
    let r = symexFind(sutForNestedWhileOob, tLabel("forWhileImpossible"), nestedLoopBudget)
    check r.status == sxUnknown

  test "R1B-fornest-3 (reachable companion): \"forFoundX\" is a real sxSat with a valid witness":
    let r = symexFind(sutForNestedWhileFindX, tLabel("forFoundX"), nestedLoopBudget)
    check r.status == sxSat
    check r.witness[0].len > 0
    check 'x' in r.witness[0]

suite "symex R1B — or-guard analogue: i>=s.len or s[i]=='x' must NOT false-raise":

  test "R1B-or-1: i>=s.len or s[i]=='x' -> IndexDefect NOT reachable":
    let r = symexFind(sutOrGuardedOob, tRaisedExn("IndexDefect"))
    check r.status != sxRaised

  test "R1B-or-2 (reachable companion): \"hitOr\" is still a real sxSat":
    let r = symexFind(sutOrGuardedOob, tLabel("hitOr"))
    check r.status == sxSat

suite "symex R1B — regression guards: genuinely unguarded s[i] must STILL raise":

  test "R1B-noguard-1: if s[0]=='x' (own condition, no and/or) -> STILL sxRaised(IndexDefect)":
    let r = symexFind(sutIfNoGuardOob, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "IndexDefect"

  test "R1B-noguard-2: unbounded while s[i]==' ' (no bound at all) -> STILL sxRaised(IndexDefect)":
    ## This is R1's own fix (runtime.nim isWhile drain); pins that R1B's
    ## while-restructuring does not regress it.
    let r = symexFind(sutWhileUnboundedOob, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "IndexDefect"

suite "symex R1B — version pins":

  test "walker version at least 61 (R1B folded into the R1 landing at 61)":
    ## Was an exact `== "62"` pin; converted to a `>=` floor (R14, walker v63)
    ## so this file auto-tracks future bumps instead of hard-pinning a
    ## specific version. `tsymex_phase15_CR2_cachekey.nim`'s "CR-2 sub-test 5"
    ## remains the SOLE exact `==` pin on `symexWalkerVersion` by convention.
    check parseInt(symexWalkerVersion) >= 61

  test "renderAsChoicesVersion stays 7 (no new witness shape)":
    check renderAsChoicesVersion == "7"
