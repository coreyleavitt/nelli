## RFC-0005 (soundness channels) slice S8t -- S8q's termination remainder.
##
## This slice closes:
##   (1) D1c's `and`/`or` lowering chained its guard temporaries
##       (`let sc2 = sc1; if sc2: ...`), so the path on which an early
##       operand was false still forked at every later guard: n operands
##       with raising reads gave 2^(n-1) paths in `if`, `while`,
##       `symexAssert` and `let`. S8q split only `symexAssume`. The guards
##       now nest, one temporary per chain (`let sc = a; if sc: (sc = b;
##       if sc: (sc = c; ...))`), so the path count is linear and a later
##       operand is still evaluated only when every earlier one allowed it.
##   (2) S8q's Int-with-width-stamp allocation (an entry `int` param traced
##       to a scan's offset is a Z3 Int stamped with its width, its type's
##       range in the initial path condition) covers the other scan shapes
##       -- a Q1/B0 skip-while scan and a B6 pair loop -- and `isExact`,
##       which kept the bit-vector and its `bv2int` bridge into the string
##       query;
##   (3) a B4 accumulating-scan offset (`isIntOffset`) is promoted the same
##       way: before S8t it was an unstamped Int with no range, so
##       arithmetic on it had no overflow obligation (a missed
##       `OverflowDefect`).
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build); the probe is quoted beside the test.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser   ## S8t2: emitStmt, parseEntryImpl, emitHoistHeight
import std/macros

type ScanError = object of CatchableError

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (1) an `and` / `or` chain lowers to nested guards ----------------------

proc sutIf12(data: seq[byte]) =
  symexAssume(data.len == 12)
  if data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
     data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
     data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
     data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8:
    symexTarget("s8t_if12")

proc sutLet12(data: seq[byte]) =
  symexAssume(data.len == 12)
  let ok =
    data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
    data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
    data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
    data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8
  if ok:
    symexTarget("s8t_let12")

proc sutAssert12(data: seq[byte]) =
  symexAssume(data.len == 12)
  symexAssert(not (
    data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
    data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
    data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
    data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8))

proc sutWhile12(data: seq[byte]) =
  symexAssume(data.len == 12)
  while data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
        data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
        data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
        data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8:
    symexTarget("s8t_while12")
    break

proc sutOr12(data: seq[byte]) =
  symexAssume(data.len == 12)
  if data[0] != byte('a') or data[1] != byte('a') or data[2] != 0'u8 or
     data[3] != byte('b') or data[4] != byte('b') or data[5] != 0'u8 or
     data[6] != byte('c') or data[7] != byte('c') or data[8] != 0'u8 or
     data[9] != byte('d') or data[10] != byte('d') or data[11] != 0'u8:
    discard
  else:
    symexTarget("s8t_or12")

proc sutIfGuarded(s: string, i: int) =
  ## Short-circuit: `s[i]` is read only when `i` is in range.
  if i >= 0 and i < s.len and s[i] == 'a' and s[i] != 'b':
    symexTarget("s8t_if_guarded")

proc sutOrGuarded(s: string, i: int) =
  ## `s[i]` is read only when `i` is in range (every earlier operand false).
  if i < 0 or i >= s.len or s[i] != 'a':
    discard
  else:
    symexTarget("s8t_or_guarded")

proc sutIfUnguarded(s: string, i: int) =
  ## `s[i]` is read before the range tests, so it can raise.
  if s[i] == 'a' and i >= 0 and i < s.len:
    symexTarget("s8t_if_unguarded")

proc sutMixed(s: string, i: int) =
  ## A mixed chain: the `or` is one operand of the `and` chain.
  if i >= 0 and (i >= s.len or s[i] == 'x') and i < s.len and s[i] == 'x':
    symexTarget("s8t_mixed")

proc sutWhileFirstFault(s: string): int =
  ## The guard's first binary node, `(s.len > 0 and s[0] == 'a') and
  ## i < s.len`, hoists a guarded read, so before S8t the guard took the
  ## rotated form. `s[i]` is read only when `i < s.len`.
  symexAssume(s.len <= 3)
  var i = 0
  while s.len > 0 and s[0] == 'a' and i < s.len and s[i] == 'a':
    inc i
  i

suite "S8t (1): the nested lowering keeps short-circuit evaluation":

  test "a guarded read in an `if` chain never raises":
    ## Probe: Nim never evaluates `s[i]` here with `i` out of range.
    let r = symexFind(sutIfGuarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let r2 = symexFind(sutIfGuarded, tLabel("s8t_if_guarded"))
    check r2.status == sxSat
    if r2.status == sxSat:
      let (s, i) = r2.witness
      check i >= 0 and i < s.len and s[i] == 'a'

  test "a guarded read in an `or` chain never raises":
    let r = symexFind(sutOrGuarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let r2 = symexFind(sutOrGuarded, tLabel("s8t_or_guarded"))
    check r2.status == sxSat
    if r2.status == sxSat:
      let (s, i) = r2.witness
      check i >= 0 and i < s.len and s[i] == 'a'

  test "an unguarded read before the range tests still raises":
    ## Probe: `sutIfUnguarded("", 0)` raises IndexDefect.
    var raised = false
    try: sutIfUnguarded("", 0)
    except IndexDefect: raised = true
    check raised
    let r = symexFind(sutIfUnguarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised

  test "a mixed and/or chain keeps its guards":
    ## Probe: no input makes `sutMixed` raise (`s[i]` is read only under
    ## `0 <= i < s.len`); `("x", 0)` reaches the target.
    sutMixed("x", 0)
    sutMixed("", 5)
    let r = symexFind(sutMixed, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let r2 = symexFind(sutMixed, tLabel("s8t_mixed"))
    check r2.status == sxSat
    if r2.status == sxSat:
      let (s, i) = r2.witness
      check i >= 0 and i < s.len and s[i] == 'x'

  test "a while guard whose first operand hoists keeps the later reads guarded":
    ## Probe: `sutWhileFirstFault("a") == 1`, `("aa") == 2`, no raise: once
    ## `i == s.len`, `s[i]` is not evaluated. RED: `sxUnknown`
    ## (`beBudgetExhausted`): the rotated guard, whose preamble also read
    ## `s[i]` outside the `i < s.len` guard, never proved the loop's exit
    ## within `maxLoopUnwind` although `s.len <= 3` bounds it.
    check sutWhileFirstFault("a") == 1
    check sutWhileFirstFault("aa") == 2
    check sutWhileFirstFault("ba") == 0
    check sutWhileFirstFault("") == 0
    let r = symexFind(sutWhileFirstFault, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat

const want12 = @[97'u8, 97, 0, 98, 98, 0, 99, 99, 0, 100, 100, 0]

suite "S8t (1): an and/or chain does not fork 2^(n-1) paths":

  test "if a and b and ... (12 operands) solves in linearly many Z3 calls":
    ## RED: 2049 Z3 calls (2^11 + 1: every chained guard forked every
    ## path). GREEN: 13 -- the target solve plus one UNSAT IndexDefect
    ## solve per read. The same counts hold for the four tests below.
    symexZ3CallCount = 0
    let r = symexFind(sutIf12, tLabel("s8t_if12"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 13
    if r.status == sxSat:
      check r.witness[0] == want12

  test "let x = a and b and ... (12 operands)":
    symexZ3CallCount = 0
    let r = symexFind(sutLet12, tLabel("s8t_let12"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 13
    if r.status == sxSat:
      check r.witness[0] == want12

  test "symexAssert(not (a and b and ...)) (12 operands)":
    symexZ3CallCount = 0
    let r = symexFind(sutAssert12, tAssertionViolation())
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxRaised
    check symexZ3CallCount <= 13
    if r.status == sxRaised:
      check r.raisedWitness[0] == want12

  test "while a and b and ... (12 operands)":
    symexZ3CallCount = 0
    let r = symexFind(sutWhile12, tLabel("s8t_while12"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 13
    if r.status == sxSat:
      check r.witness[0] == want12

  test "if a or b or ... (12 operands), target on the else side":
    symexZ3CallCount = 0
    let r = symexFind(sutOr12, tLabel("s8t_or12"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 13
    if r.status == sxSat:
      check r.witness[0] == want12

# ---- (2) and (3): scan offsets are width-stamped Ints ------------------------

proc hasTypeRangeEntry(r: auto, name: string): bool =
  for a in r.abstractions:
    if a.name == name and a.interval == interval(low(int64), high(int64)):
      return true
  false

proc readCStr(data: seq[byte], offset: int): (string, int) =
  ## B4's accumulating scan (chapulin's `readCString`).
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

proc sutAccOverflow(data: seq[byte], start: int) =
  ## `start + 1` overflows at `high(int)` before the scan runs.
  let bump = start + 1
  let (k, p) = readCStr(data, start)
  if k.len == 2 and p == bump + 2:
    symexTarget("s8t_acc_hit")

proc skipTo(s: string, start: int): int =
  ## Q1/B0's skip-while scan.
  var i = start
  while i < s.len and s[i] != ':':
    inc i
  i

proc sutSkip(s: string, start: int) =
  let bump = start + 1
  let p = skipTo(s, start)
  if p == bump + 3 and p < s.len:
    symexTarget("s8t_skip_hit")

proc readOpt(s: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sutPairLoop(s: string, start: int) =
  ## B6's pair loop (chapulin's `readOptions`), seeded from a param.
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = readOpt(s, i)
    if key.len == 0:
      break
    let (val, p2) = readOpt(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("s8t_pairloop_done")

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
    symexTarget("s8t_pair_hit")

const exactTight = SymexSettings(
  integerSemantics: isExact,
  budget: ResourceBudget(seqQueryRLimit: 2_000_000))

suite "S8t (3): a B4 accumulating-scan offset keeps its overflow obligation":

  test "oracle: start + 1 raises OverflowDefect at high(int)":
    var raised = false
    try: sutAccOverflow(@[], high(int))
    except OverflowDefect: raised = true
    check raised

  test "the B4 offset is promoted over int's range":
    ## RED: no abstraction entry (the unstamped promotion logged nothing).
    let r = symexFind(sutAccOverflow, tLabel("s8t_acc_hit"))
    checkpoint show(r.errors)
    check hasTypeRangeEntry(r, "start")

  test "the OverflowDefect on the B4 offset is found":
    ## RED: `sxRaised` with witness `(@[], -1)` and `raisedTypeId`
    ## IndexDefect: the unstamped Int had no overflow fork on `start + 1`,
    ## so the only Defect found was the scan's entry read `data[-1]`, and
    ## E6 surfaces a reachable Defect with its own type whatever the
    ## target. (RFC-0005 S8w traced this; S8t first read it as a false
    ## OverflowDefect. The finding was a correct, replaying IndexDefect.)
    let r = symexFind(sutAccOverflow, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      checkpoint "witness: " & $r.raisedWitness
      check r.raisedTypeId == "OverflowDefect"
      check r.raisedWitness[1] == high(int)

  test "the B4 hit is still reachable, with a replayable witness":
    let r = symexFind(sutAccOverflow, tLabel("s8t_acc_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      let (k, p) = readCStr(data, start)
      check k.len == 2 and p == start + 3

suite "S8t (2): the other scan shapes and isExact":

  test "a Q1/B0 skip-while offset is promoted, and its overflow found":
    ## RED: the suite is killed at 900 s inside this test (`start` was a
    ## bit-vector bridged into the string query, which Z3 did not bound).
    let r = symexFind(sutSkip, tLabel("s8t_skip_hit"))
    checkpoint show(r.errors)
    check hasTypeRangeEntry(r, "start")
    check r.status == sxSat
    if r.status == sxSat:
      let (s, start) = r.witness
      let p = skipTo(s, start)
      check p == start + 4 and p < s.len
    var raised = false
    try: sutSkip("", high(int))
    except OverflowDefect: raised = true
    check raised
    let r2 = symexFind(sutSkip, tRaisedExn("OverflowDefect"))
    checkpoint show(r2.errors)
    check r2.status == sxRaised

  test "a pair-loop offset is promoted over int's range":
    ## RED: no abstraction entry (and `beBudgetExhausted`).
    let r = symexFind(sutPairLoop, tLabel("s8t_pairloop_done"))
    checkpoint show(r.errors)
    check hasTypeRangeEntry(r, "start")

  test "under isExact a scan-pair offset is a stamped Int too":
    ## RED: `sxUnknown` ("canceled") -- the bridged query is not decided
    ## within 2M units (S8q measured it `unknown` at 10M).
    let r = symexFind(sutPairFound, tLabel("s8t_pair_hit"), exactTight)
    checkpoint show(r.errors)
    check hasTypeRangeEntry(r, "start")
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      let (p, q) = scanPair(data, start)
      check p == start + 4 and q == start + 5

# ---------------------------------------------------------------------------
# RFC-0005 S8t2 -- the emitted IR builder's depth. S8t's nested guards made
# the builder `emitStmt` produces ~7 AST levels deeper per chain operand, and
# the compiler semchecks that AST by native recursion: a 10-operand chain
# (`tsymex_r6_nulwitness`) overflowed the Windows `nim.exe`'s 1 MB stack,
# and this 40-operand one overflowed 1 MB on Linux (`ulimit -s 1024`).
# `boundEmittedDepth` binds any call subtree taller than `emitHoistHeight`
# to a `let`. Compiling this file at all on Windows is half the guard; the
# height check below is the platform-independent half.
# ---------------------------------------------------------------------------

proc sutChain40(s: string) =
  if s.len == 40 and
     s[0] == 'a' and s[1] == 'a' and s[2] == 'a' and s[3] == 'a' and
     s[4] == 'a' and s[5] == 'a' and s[6] == 'a' and s[7] == 'a' and
     s[8] == 'a' and s[9] == 'a' and s[10] == 'a' and s[11] == 'a' and
     s[12] == 'a' and s[13] == 'a' and s[14] == 'a' and s[15] == 'a' and
     s[16] == 'a' and s[17] == 'a' and s[18] == 'a' and s[19] == 'a' and
     s[20] == 'a' and s[21] == 'a' and s[22] == 'a' and s[23] == 'a' and
     s[24] == 'a' and s[25] == 'a' and s[26] == 'a' and s[27] == 'a' and
     s[28] == 'a' and s[29] == 'a' and s[30] == 'a' and s[31] == 'a' and
     s[32] == 'a' and s[33] == 'a' and s[34] == 'a' and s[35] == 'a' and
     s[36] == 'a' and s[37] == 'a' and s[38] == 'a' and s[39] == 'a':
    symexTarget("hit")

proc emittedHeight(n: NimNode): int =
  result = 1
  for c in n: result = max(result, 1 + emittedHeight(c))

macro builderHeights(fn: typed): untyped =
  ## (height of the raw `emitStmt` builder, height of the one emitted)
  let parsed = parseEntryImpl(fn, "builderHeights",
                              defaultSymexSettings().budget.maxInstantiationsPerProc)
  newLit((emittedHeight(emitStmt(parsed.body)),
          emittedHeight(parsed.bodyNimNode)))

suite "S8t2: the emitted IR builder's depth is bounded":

  test "a 40-operand chain's builder is bound under emitHoistHeight":
    const hs = builderHeights(sutChain40)
    checkpoint "raw " & $hs[0] & ", emitted " & $hs[1]
    check hs[0] > 200                        # the unbounded builder: deep
    check hs[1] <= emitHoistHeight + 8       # what the compiler semchecks

  test "the 40-operand chain still solves":
    let r = symexFind(sutChain40, tLabel("hit"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == repeat('a', 40)

suite "S8t: walker version floor":

  test "walker version >= 168":
    check parseInt(symexWalkerVersion) >= 168
