## RFC-0005 (soundness channels) slice S8k -- termination and resources.
## Walker 160 -> 161.
##
## Three ways a symex run could fail to finish, or take its host down:
##   (1) a query whose witness needs a long string: Z3's sequence solver
##       explores string lengths upward, and past ~100 elements each step
##       grows super-linearly (probed on the pinned Z3: `len(s) > 200` alone
##       peaks at 1.6 GB and 19 s, `len(s) > 300` at 3.4 GB with a single
##       ~100 s stretch in which neither `rlimit` nor `timeout` is polled;
##       `findColon(s, 0) > 1000`'s query never returns). The walker now
##       caps every string / seq in a query at `maxSeqLen` elements
##       (`checkCapped`): an UNSAT the cap took part in is a recorded
##       `beSolverUndef`, never a verdict;
##   (2) the loop k-unroll forked every iteration without asking whether it
##       was feasible, so a dead label after a loop was `sxUnknown` and
##       nested loops grew as a power of the unroll bound;
##   (3) witness replay runs the real SUT, and a real nil dereference is a
##       SIGSEGV (not a `NilAccessDefect`) in the default build, so a
##       candidate whose path goes through the walker's nil fork must never
##       be replayed.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build, c and cpp identical); the probe is quoted beside the test.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc onlyKinds(errs: seq[SymexErrorInfo]; ks: set[SymexErrorKind]): bool =
  for e in errs:
    if e.severity == sevError and e.kind notin ks: return false
  true

proc capMsg(errs: seq[SymexErrorInfo]): bool =
  for e in errs:
    if e.kind == beSolverUndef and "maxSeqLen" in e.msg: return true
  false

# ---- (1) long-string queries are bounded ----------------------------------
#
# Probe: `findColon(repeat('x', 1500), 0)` returns 1500; so the label below
# is reachable in reality, with a string of more than 1000 bytes and no ':'
# in its first 1001.

proc findColon(s: string, offset: int): int =
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return i
    i = i + 1
  return i

proc farColon(s: string) =
  if findColon(s, 0) > 1000:
    symexTarget("s8k_far_colon")

proc longAndShort(s: string) =
  ## Contradictory on lengths alone: the cap must not turn a real UNSAT
  ## into a decline (the unsat core does not contain it).
  if s.len > 1000 and s.len < 10:
    symexTarget("s8k_long_and_short")

proc needs130(s: string) =
  if s.len == 130 and s[129] == 'q':
    symexTarget("s8k_needs130")

proc len130(s: string) =
  if s.len == 130:
    symexTarget("s8k_len130")

proc len100(s: string) =
  if s.len == 100:
    symexTarget("s8k_len100")

const wideCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 160))
const smallSeqBudget = SymexSettings(
  budget: ResourceBudget(maxSeqLen: 160, seqQueryRLimit: 50_000))

suite "S8k (1): every query over strings is bounded":

  test "oracle: the far-colon label is reachable in Nim":
    check findColon(repeat('x', 1500), 0) == 1500

  test "findColon(s, 0) > 1000 terminates as a recorded maxSeqLen decline":
    ## Was: no return (the query needs a 1001-byte witness).
    let r = symexFind(farColon, tLabel("s8k_far_colon"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.capMsg
    check r.errors.onlyKinds({beSolverUndef})

  test "a length contradiction stays sxUnsat under the cap":
    let r = symexFind(longAndShort, tLabel("s8k_long_and_short"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a 100-byte witness is inside the default cap":
    let r = symexFind(len100, tLabel("s8k_len100"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 100

  test "a 130-byte witness is past the default cap: declined, not sxUnsat":
    let r = symexFind(needs130, tLabel("s8k_needs130"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.capMsg

  test "a 130-byte length alone is past the default cap too":
    let r = symexFind(len130, tLabel("s8k_len130"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.capMsg

  test "maxSeqLen raises the cap: the 130-byte witness is found":
    let r = symexFind(len130, tLabel("s8k_len130"), wideCap)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 130

  test "a byte test is decided in its character form":
    ## `s[129] == 'q'` lowers to `int2bv8(str.to_code(str.at(s, 129))) ==
    ## 0x71`; the query takes it as `str.at(s, 129) == "q"` (the same
    ## predicate on a byte string). Was: over 300 s under the wide cap
    ## with no budget, the sequence solver polling the counter slowly.
    let r = symexFind(needs130, tLabel("s8k_needs130"), wideCap)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 130
      check r.witness[0][129] == 'q'

  test "a within-cap query seqQueryRLimit cuts off is a recorded decline":
    ## The same query takes about 5 s; under a small `seqQueryRLimit` it
    ## is declined at once.
    let r = symexFind(needs130, tLabel("s8k_needs130"), smallSeqBudget)
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.onlyKinds({beSolverUndef})
    var named = false
    for e in r.errors:
      if e.kind == beSolverUndef and "seqQueryRLimit" in e.msg: named = true
    check named

  test "maxSeqLen and seqQueryRLimit enter the cache key only when not the default":
    let d = defaultSymexSettings()
    check ";msl=" notin canonicalize(d)
    check ";msl=160" in canonicalize(wideCap)
    check ";sqr=" notin canonicalize(d)
    check ";sqr=50000" in canonicalize(smallSeqBudget)

# ---- (2) loop-iteration feasibility pruning ---------------------------------
#
# Probe: `deadAfter` never reaches its label (the loop always ends with
# i == 3); `nested` always ends with acc == 16.

proc deadAfter(x: int) =
  var i = 0
  while i < 3:
    inc i
  if i != 3 and x == 1:
    symexTarget("s8k_dead_after")

proc liveAfter(x: int) =
  var i = 0
  while i < 3:
    inc i
  if i == 3 and x == 1:
    symexTarget("s8k_live_after")

proc nested(x: int) =
  var acc = 0
  for i in 0 ..< 4:
    for j in 0 ..< 4:
      acc += 1
  if acc != 16 and x == 2:
    symexTarget("s8k_nested_dead")

proc symbolicTrip(n: int) =
  var i = 0
  while i < n:
    inc i
  if i == 9:
    symexTarget("s8k_symbolic_trip")

suite "S8k (2): the k-unroll prunes infeasible iterations":

  test "oracle":
    deadAfter(1); liveAfter(1); nested(2); symbolicTrip(9)

  test "a dead label after a concretely bounded loop is sxUnsat":
    ## Was: sxUnknown [beBudgetExhausted] -- the infeasible "guard still
    ## true" survivors of every iteration past the third.
    let r = symexFind(deadAfter, tLabel("s8k_dead_after"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "the live label after the loop is still a clean sxSat":
    let r = symexFind(liveAfter, tLabel("s8k_live_after"))
    check r.status == sxSat

  test "nested loops at the default unwind: sxUnsat, iterations linear in the trip counts":
    ## Was: every iteration forked a continuation and an exit whether or not
    ## either was feasible, so every infeasible outer survivor re-ran the
    ## inner loop. Measured with the feasibility checks switched off (the
    ## rest of this walker unchanged): 9330 body walks, 34211 Z3 queries,
    ## `sxUnknown` [beBudgetExhausted]. Pruned: the four outer and sixteen
    ## inner bodies a real run executes -- 20 -- and 37 queries.
    symexLoopIterations = 0
    let r = symexFind(nested, tLabel("s8k_nested_dead"))
    checkpoint show(r.errors)
    checkpoint "loop body walks: " & $symexLoopIterations
    check r.status == sxUnsat
    check symexLoopIterations == 20

  test "a symbolic trip count past the bound still records the budget decline":
    let r = symexFind(symbolicTrip, tLabel("s8k_symbolic_trip"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(beBudgetExhausted)

# ---- (3) replay never executes a witness into a SIGSEGV ----------------------
#
# Probe (Nim 2.2.10, debug, c and cpp; `--nilchecks:on` changes nothing):
#   `var p: ref Obj; try: p[].x = 1 except NilAccessDefect: echo "caught"`
#   prints "SIGSEGV: Illegal storage access. (Attempt to read from nil?)"
#   and exits 139 -- the except arm never runs, for a read (`p.x`) too.
#   `int(NaN)` does not raise (S8g: C-level undefined).
# Each SUT below reaches its nil write only on a NaN input, where the
# preceding `int(f)` is a `feConvFloatToIntUndefined` fresh symbol: the
# path is `scSpurious`-tainted, so its finding is a replay CANDIDATE, and
# replaying it would run `p[].x = 1` with `p == nil` for real.

type S8kObj = object
  x: int

proc nilWriteOnNaN(p: ref S8kObj; f: float) =
  let k = int(f)
  if f != f:
    p[].x = k

proc nilWriteCaught(p: ref S8kObj; f: float) =
  let k = int(f)
  if f != f:
    try:
      p[].x = k
    except NilAccessDefect:
      symexTarget("s8k_nil_caught")

suite "S8k (3): replay declines a witness through a nil dereference":

  test "a NilAccessDefect candidate is not replayed: the process survives":
    ## Was: the run replayed the candidate against
    ## `tRaisedExn("NilAccessDefect")`, called `nilWriteOnNaN(nil, NaN)`,
    ## and the test binary died with SIGSEGV.
    let r = symexFind(nilWriteOnNaN, tRaisedExn("NilAccessDefect"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check not r.errors.hasKind(feReplayRefuted)

  test "a label behind a caught nil write is not replayed either":
    let r = symexFind(nilWriteCaught, tLabel("s8k_nil_caught"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check not r.errors.hasKind(feReplayRefuted)

  test "replayInScope: a NilAccessDefect raise target is out of scope":
    check not replayInScope(tRaisedExn("NilAccessDefect"))
    check replayInScope(tRaisedExn("ValueError"))
    check replayInScope(tRaisedExn(""))

suite "S8k: walker version floor":

  test "walker version >= 161":
    check parseInt(symexWalkerVersion) >= 161
