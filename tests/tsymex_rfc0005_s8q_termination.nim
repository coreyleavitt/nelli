## RFC-0005 (soundness channels) slice S8q -- S8o's termination remainder.
##
## S8o left `tsymex_r6_b7r_bytescan` running past 900 s on Linux: its B7R-3
## query, `str.indexof(data, "\0", start) == start + 4`, reached Z3 with the
## `int` parameter `start` as a 64-bit bit-vector bridged into the string
## theory through a signed `bv2int` (an `ite` over `bvslt`). In the walk's
## shared context one such check ignored its 10M `rlimit` for over 300 s.
## This slice closes:
##   (1) an `int` parameter traced to a B3 scan-pair's index (through one
##       rebind and one call boundary, as B4's `isIntOffset` is traced) is
##       allocated as a Z3 Int, stamped with its Nim width and constrained
##       to its type's range, so the string query holds no bit-vector
##       bridge and the parameter keeps its overflow obligations;
##   (3) `symexAssume(a and b and ...)` is one assume per conjunct, in
##       order, instead of D1c's guarded temporaries, which forked every
##       path at every conjunct (2^(n-1) paths for n conjuncts).
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build); the probe is quoted beside the test.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

type ScanError = object of CatchableError

# ---- (1) a scan-pair offset parameter is an Int, not a bridged bit-vector --

proc scanPair(data: seq[byte], start: int): (int, int) =
  var i = start
  while i < data.len:
    if data[i] == 0'u8:
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "unterminated")

proc sutPairFound(data: seq[byte], start: int) =
  let (p, q) = scanPair(data, start)
  if p == start + 4 and q == start + 5:
    symexTarget("s8q_pair_hit")

proc sutPairOverflow(data: seq[byte], start: int) =
  ## The promotion keeps `start`'s overflow obligation: Nim raises
  ## `OverflowDefect` on `start + 1` at `start == high(int)`.
  let next = start + 1
  let (p, _) = scanPair(data, next)
  if p == next:
    symexTarget("s8q_ovf_unused")

proc sutPairNegative(data: seq[byte], start: int) =
  ## The type range is the only constraint the promotion adds: a negative
  ## start still reaches the scan's entry read (IndexDefect).
  discard scanPair(data, start)

const tightSeqBudget = SymexSettings(
  budget: ResourceBudget(seqQueryRLimit: 2_000_000))

suite "S8q (1): a scan-pair offset parameter reaches Z3 as an Int":

  test "oracle: the pair hit is reachable in Nim":
    ## Probe: `scanPair(@[1'u8, 1, 1, 1, 0], 0) == (4, 5)`.
    let (p, q) = scanPair(@[1'u8, 1, 1, 1, 0], 0)
    check p == 4 and q == 5

  test "start is promoted, stamped with its width, over int's range":
    ## RED: no abstraction entry (`start` was a bit-vector).
    let r = symexFind(sutPairFound, tLabel("s8q_pair_hit"), tightSeqBudget)
    checkpoint show(r.errors)
    var found = false
    for a in r.abstractions:
      if a.name == "start":
        found = true
        check a.interval == interval(low(int64), high(int64))
    check found

  test "B7R-3's query is decided within 2M units, with a replayable witness":
    ## RED: in the bridged form Z3 does not answer this within the budget
    ## (S8o: past 300 s in the walker, `unknown` at 10M standalone).
    let r = symexFind(sutPairFound, tLabel("s8q_pair_hit"), tightSeqBudget)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      let (p, q) = scanPair(data, start)
      check p == start + 4 and q == start + 5

  test "the overflow obligation on the promoted param stays live":
    ## Probe: `sutPairOverflow(@[], high(int))` raises OverflowDefect.
    var raised = false
    try: sutPairOverflow(@[], high(int))
    except OverflowDefect: raised = true
    check raised
    let r = symexFind(sutPairOverflow, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[1] == high(int)

  test "a negative start still raises IndexDefect at the entry read":
    ## Probe: `sutPairNegative(@[0'u8], -1)` raises IndexDefect.
    var raised = false
    try: sutPairNegative(@[0'u8], -1)
    except IndexDefect: raised = true
    check raised
    let r = symexFind(sutPairNegative, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[1] < 0

# ---- (3) a conjunctive assume does not fork per conjunct --------------------

proc sutAssume12(data: seq[byte]) =
  symexAssume(data.len == 12)
  symexAssume(
    data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
    data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
    data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
    data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8)
  symexTarget("s8q_assume12")

proc sutAssumeGuarded(s: string, i: int) =
  ## Short-circuit: `s[i]` is read only when `i` is in range.
  symexAssume(i >= 0 and i < s.len and s[i] == 'a')
  symexTarget("s8q_guarded")

proc sutAssumeUnguarded(s: string, i: int) =
  ## `s[i]` is read first, so an out-of-range `i` raises before the assume
  ## filters anything.
  symexAssume(s[i] == 'a' and i >= 0 and i < s.len)

proc sutAssumeContradiction(s: string) =
  symexAssume(s.len == 2 and s[0] == 'a' and s[0] == 'b')
  symexTarget("s8q_contradiction")

suite "S8q (3): symexAssume(a and b and ...) adds its conjuncts without forking":

  test "a 12-conjunct assume solves the target a bounded number of times":
    ## RED: 2049 Z3 calls (2^11 + 1: D1c's guard temporaries fork every
    ## path at every conjunct, and every path reaches the label). GREEN:
    ## 13, linear -- the target solve, plus one per conjunct for the
    ## IndexDefect raise its read forks (a real raise; `data.len == 12`
    ## makes each one UNSAT).
    symexZ3CallCount = 0
    let r = symexFind(sutAssume12, tLabel("s8q_assume12"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 13
    if r.status == sxSat:
      let d = r.witness[0]
      check d == @[97'u8, 97, 0, 98, 98, 0, 99, 99, 0, 100, 100, 0]

  test "short-circuit is kept: a guarded read never raises":
    ## Probe: Nim never evaluates `s[i]` here with `i` out of range.
    let r = symexFind(sutAssumeGuarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let r2 = symexFind(sutAssumeGuarded, tLabel("s8q_guarded"))
    check r2.status == sxSat
    if r2.status == sxSat:
      let (s, i) = r2.witness
      check i >= 0 and i < s.len and s[i] == 'a'

  test "an unguarded read before the range test still raises":
    ## Probe: `sutAssumeUnguarded("", 0)` raises IndexDefect.
    var raised = false
    try: sutAssumeUnguarded("", 0)
    except IndexDefect: raised = true
    check raised
    let r = symexFind(sutAssumeUnguarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised

  test "contradictory conjuncts leave the target unreachable":
    let r = symexFind(sutAssumeContradiction, tLabel("s8q_contradiction"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

suite "S8q: walker version floor":

  test "walker version >= 165":
    check parseInt(symexWalkerVersion) >= 165
