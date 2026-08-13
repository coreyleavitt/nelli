## RFC-chapulin-hardening Q1 (ADR-0025, walker v60) — Cluster 5 (Solver capability).
##
## The `isWhile` walker does finite k-unrolling: a loop whose trip count is
## bounded by a SYMBOLIC quantity (`while i < s.len and s[i] != ':': inc i`)
## degrades to `sxUnknown` regardless of `maxLoopUnwind` -- finite unrolling
## structurally can't decide a symbolic trip count.
##
## THE FIX (never re-derive; this suite pins it): the canonical bounded
## forward scan-to-literal-delimiter idiom
##   while <i> < <bound> and <s>[<i>] != <lit>: inc <i>
## IS a `find`/`indexOf`. `tryRecognizeScanIdiom` (dsl_parser.nim) matches
## this EXACT shape at parse time and rewrites it to the closed form
##   <i> = (let p = <s>.find($<lit>, <i>);
##          if p == -1 or p >= <bound>: <bound> else: p)
## eliminating the loop -- decided via Sequence-theory `indexOf`, not
## unwinding. Dependent chains (`var j = i + 1; while j < s.len and ...`)
## compose for free since the rewrite reads the CURRENT `<i>`/`<j>` as the
## find start. Anything off this exact shape (`==`-guards, char-class scans,
## non-`inc` bodies, ...) is deliberately left UNRECOGNIZED and falls through
## to the unchanged `mkWhile` k-unroll path -- a false recognition would be
## UNSOUND, strictly worse than a clean `sxUnknown` degrade.
##
## Part 1 (foundation): `iekStrFind` gained an optional 3rd `strArgs[2]`
## start operand (`s.find(sub, start)` -> Z3 `indexOf(s, sub, start)`) --
## the scan-idiom rewrite's closed form is built on this. Incidental finding:
## pre-Q1, a caller-written 3-arg `s.find(sub, start)` already PARSED (the
## strArgs-collection loop is arity-agnostic) but `start` was SILENTLY
## DROPPED at lowering -- a latent unsoundness (wrong verdict, not even a
## clean degrade), fixed as part of this same slice.
##
## Every test in this file asserts the SAME verdict is expected on BOTH the
## `c` and `cpp` backends (run via `scripts/dt-bounded.sh c|cpp`).
##
## Bumps `symexWalkerVersion` 59->60 (verdict-surface change: recognized scan
## loops move from `sxUnknown` to real verdicts). `renderAsChoicesVersion`
## STAYS unchanged -- no new witness shape (witnesses are strings/ints
## already rendered).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# Part 1 -- 3-arg `find(sub, start)` sanity pin
# ---------------------------------------------------------------------------

proc sutFindWithStart(s: string) =
  let i = s.find(":", 2)
  if i == 5:
    symexTarget("hit")

proc sutFindWithStartUnsat(s: string) =
  let i = s.find(":", 2)
  if i == 1:
    # Can never be reachable: `start = 2` means any real match index is
    # >= 2 (or -1). If `start` were silently dropped (pre-fix bug), this
    # WOULD be reachable via a ':' at position 1 -- this is the load-bearing
    # regression check for that latent unsoundness.
    symexTarget("impossible")

suite "symex RFC-chapulin-hardening Q1 Part 1 -- 3-arg find(sub, start)":

  test "Q1-P1a: find(sub, start) resolves a real sxSat honoring the start offset":
    let r = symexFind(sutFindWithStart, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len >= 6

  test "Q1-P1b UNSAT companion: result can never be < start (start is not silently dropped)":
    let r = symexFind(sutFindWithStartUnsat, tLabel("impossible"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Part 2 -- the scan-idiom recognizer
# ---------------------------------------------------------------------------

# 1. Tracer -- single scan now decides (was sxUnknown pre-Q1).
proc sutScanTracer(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i == 3:
    symexTarget("hit")

# UNSAT companion -- the closed form MUST cap `i` at `bound` (= s.len here);
# `i` can never exceed it. This is the soundness-critical clamp in the
# closed form (`if p == -1 or p >= bound: bound else: p`).
proc sutScanTracerUnsat(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i > s.len:
    symexTarget("impossible")

suite "symex RFC-chapulin-hardening Q1 Part 2 -- scan-idiom recognizer":

  test "Q1-1 tracer: while i<s.len and s[i]!=':' : inc i ; i==3 -> sxSat (was sxUnknown)":
    let r = symexFind(sutScanTracer, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len >= 3

  test "Q1-1b UNSAT companion: i > s.len is impossible (closed form clamps at bound)":
    let r = symexFind(sutScanTracerUnsat, tLabel("impossible"))
    check r.status == sxUnsat

# 2. Chained/dependent scan -- the RFC's headline finding (#6): a 2nd scan's
# start derives from the 1st scan's result. Composes for free -- the rewrite
# just reads whatever `i`/`j` currently is as the find start.
proc sutChainedScan(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  var j = i + 1
  while j < s.len and s[j] != ';':
    inc j
  if i == 2 and j == 7:
    symexTarget("hit")

# UNSAT companion -- `j`'s scan starts at `i + 1`, so `j < i` can never hold
# (the closed form clamps `j` into `[i+1, bound]`). Load-bearing: proves the
# DEPENDENT chain's start offset is honored, not just each scan in isolation.
proc sutChainedScanUnsat(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  var j = i + 1
  while j < s.len and s[j] != ';':
    inc j
  if j < i:
    symexTarget("impossible")

suite "symex RFC-chapulin-hardening Q1 Part 2b -- chained/dependent scans (headline)":

  test "Q1-2 chained scan: dependent i,j both pinned (i==2 and j==7) -> sxSat":
    let r = symexFind(sutChainedScan, tLabel("hit"))
    check r.status == sxSat

  test "Q1-2b UNSAT companion: j < i is impossible (j's scan starts at i+1)":
    let r = symexFind(sutChainedScanUnsat, tLabel("impossible"))
    check r.status == sxUnsat

# 3. Scan then out-of-bounds -- the loop-FORM analogue of SND-4's
# `sutScanThenOob` (which uses `s.find(":")` directly -- already decidable
# pre-Q1). This SUT scans via the EXPLICIT while-loop idiom; Q1's lift makes
# the OOB reachable end-to-end through the recognized loop too, not just the
# pre-existing 2-arg-find form. Needs SND-4 (ADR-0024, already landed at
# walker v59) for `s[i+1]` to model `IndexError` at all.
proc sutScanThenOobViaLoop(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  let c = s[i + 1]
  discard c

suite "symex RFC-chapulin-hardening Q1 Part 2c -- scan then out-of-bounds":

  test "Q1-3: loop-form scan then s[i+1] -> sxRaised IndexDefect (scan-then-OOB reachable via the loop, not just find())":
    let r = symexFind(sutScanThenOobViaLoop, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

# 4. Scope guards -- each is a deliberate near-miss of the recognized shape,
# proving the recognizer is correctly NARROW (no false recognition -- a
# false-positive lift would be UNSOUND). Every SUT below queries the SAME
# "impossible" `i > s.len` target used by the tracer's UNSAT companion
# (#1b): this is the MEANINGFUL, uniform diagnostic -- proving `i` can never
# exceed `bound` requires reasoning across ALL possible trip counts (not
# just the ones explored within `maxLoopUnwind`), so an UN-recognized loop
# MUST stay `sxUnknown` here (empirically confirmed: k-unroll's residual
# "trip count > k" tail taints this class of query regardless of guard
# shape). If any of these were WRONGLY recognized, the closed form would
# (dishonestly) prove `sxUnsat` here instead -- so this is a REAL trip-wire,
# not just an assertion of the status quo. (A plain shallow `tLabel`
# reachability query is NOT a reliable narrowness probe: k-unroll already
# resolves those for many near-miss shapes regardless of Q1 -- e.g. the
# `==`-guard below independently reaches a real `sxSat` for `i==3` via
# ordinary unrolling, which is correct pre-existing behavior, not a Q1
# regression, but also not evidence of anything Q1-specific.)

# 4a. `==`-guard (skip-while, not scan-to-delimiter) -- out of scope.
proc sutSkipWhileGuardImpossible(s: string) =
  var i = 0
  while i < s.len and s[i] == ' ':
    inc i
  if i > s.len:
    symexTarget("impossible")

# 4b. Char-class/predicate scan -- the guard's 2nd `and`-operand is a range
# check, not a `!=` literal comparison, so the top-level shape (and(lt,
# ne)) never matches at all -- structurally out of scope, no special-casing
# needed in the recognizer.
proc sutCharClassScanImpossible(s: string) =
  var i = 0
  while i < s.len and s[i] >= '0' and s[i] <= '9':
    inc i
  if i > s.len:
    symexTarget("impossible")

# 4c. Non-`inc` body (extra statement) -- out of scope.
proc sutNonIncBodyImpossible(s: string) =
  var i = 0
  var count = 0
  while i < s.len and s[i] != ':':
    inc i
    inc count
  if i > s.len:
    symexTarget("impossible")

suite "symex RFC-chapulin-hardening Q1 Part 2d -- scope guards (must stay sxUnknown, unchanged)":

  test "Q1-4a: ==-guard (skip-while) is NOT recognized -> sxUnknown (unchanged, real trip-wire)":
    let r = symexFind(sutSkipWhileGuardImpossible, tLabel("impossible"))
    check r.status == sxUnknown

  test "Q1-4b: char-class/predicate scan is NOT recognized -> sxUnknown (unchanged, real trip-wire)":
    let r = symexFind(sutCharClassScanImpossible, tLabel("impossible"))
    check r.status == sxUnknown

  test "Q1-4c: non-inc body (extra statement) is NOT recognized -> sxUnknown (unchanged, real trip-wire)":
    let r = symexFind(sutNonIncBodyImpossible, tLabel("impossible"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 5. Regression -- a plain non-scan while loop. The guard `i < n` is not
# `and`-shaped at all, so the recognizer declines on the very first check
# (before even looking at the body) -- proves Q1 leaves ordinary k-unrolled
# loops completely untouched.
# ---------------------------------------------------------------------------

proc sutPlainWhile(n: int) =
  var i = 0
  var acc = 0
  while i < n:
    acc += i
    inc i
  if acc == 3:
    symexTarget("hit")

suite "symex RFC-chapulin-hardening Q1 Part 2e -- regression (plain non-scan while, unaffected)":

  test "Q1-5: plain `while i < n: acc += i; inc i` still k-unrolls -> sxSat (acc==3 via n==3)":
    let r = symexFind(sutPlainWhile, tLabel("hit"))
    check r.status == sxSat

suite "symex RFC-chapulin-hardening Q1 -- version pins":

  test "walker version floor >= 60 (Q1 introduced at 60)":
    check parseInt(symexWalkerVersion) >= 60

  test "renderAsChoicesVersion floor >= 7 (Q1 does NOT bump RC -- no new witness shape)":
    check parseInt(renderAsChoicesVersion) >= 7
