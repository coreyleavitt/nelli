## RFC-0005 (soundness channels) slice S8aa -- S8w's remainder.
##
## This slice closes:
##   (1) arithmetic that TRAPS in the generated C was forked as a Nim
##       Defect: with overflow checks off, Nim emits no zero-divisor check,
##       so `x div 0` / `x mod 0` reach the C division, which aborts the
##       process (SIGFPE). The model raised `DivByZeroDefect` there (its
##       witness aborts the replay) or, with `acDivByZero` off as well,
##       continued with Z3's `x div 0` value. `low(T) div -1` / `mod -1`,
##       S8w's named suspect, was already confined off the trap at 32 and
##       64 bits (S8i) and wraps at 8 and 16 as C does; it is pinned here;
##   (2) the short-circuit join (S8w) merged only paths that differ in
##       scalars: an operand that writes a string, seq, heap cell or ref, or
##       that leaves more than one surviving path, forked 2^m paths;
##   (3) the B6 pair loop certified a negative start as a region member (Z3's
##       `str.substr` at a negative offset is ""), so the first scan's
##       `IndexDefect` was never walked: `sxUnknown` when the fallback's
##       unroll budget ran out, a false `sxUnsat` when it did not;
##   (4) a same-width signedness reinterpret of an Int-sorted value
##       (`data.len.uint`, `s.find(c).uint`) declined to a fresh placeholder.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is, c and cpp); the probe is
## quoted beside the test. A trapping input is never executed here: it
## would abort this process.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- (1) arithmetic that traps in C -----------------------------------------

{.push overflowChecks: off.}
proc sutZeroDiv(x, y: int) =
  ## Probe (`{.push overflowChecks: off.}`, debug build, c and cpp):
  ## `5 div 0` prints "SIGFPE: Arithmetic error." and aborts; no `except`
  ## arm runs. So no input with `y == 0` gets past the division.
  let q = x div y
  if y == 0 and q == -1:
    symexTarget("s8aa_zero_div")

proc sutZeroMod(x, y: int) =
  ## Probe: `5 mod 0` aborts the same way.
  let q = x mod y
  if y == 0 and q == x:
    symexTarget("s8aa_zero_mod")

proc sutZeroDivU(x, y: uint32) =
  ## Unsigned: the C `/` traps on a zero divisor as well.
  let q = x div y
  if y == 0'u32 and q == 0'u32:
    symexTarget("s8aa_zero_divu")

proc sutLowDiv(x, y: int) =
  ## Probe: `low(int) div -1` aborts (SIGFPE). The only negative quotient
  ## of two negatives is that one, so the target is dead.
  if x < 0 and y < 0 and x div y < 0:
    symexTarget("s8aa_low_div")

proc sutLowDiv32(x, y: int32) =
  ## Probe: `low(int32) div -1` aborts too.
  if x < 0 and y < 0 and x div y < 0:
    symexTarget("s8aa_low_div32")

proc sutLowMod(x, y: int) =
  ## Probe: `low(int) mod -1` aborts.
  if x == low(int) and y == -1 and x mod y == 0:
    symexTarget("s8aa_low_mod")

proc sutLowDiv8(x, y: int8) =
  ## Probe: `low(int8) div -1 == -128`: C promotes to `int` and the
  ## quotient 128 converts back to -128. No trap below 32 bits.
  if x < 0 and y < 0 and x div y < 0:
    symexTarget("s8aa_low_div8")

proc sutSafeDiv(x, y: int) =
  ## Away from both traps the quotient is Nim's (C's truncating) one.
  if y < 0 and x div y == 7 and x mod y == -3:
    symexTarget("s8aa_safe_div")

type ScanError = object of CatchableError

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

proc sutOffsetDiv(data: seq[byte], start: int) =
  ## A B4 offset (a width-stamped Int since S8w) divided by -1: at
  ## `low(int)` the division traps, it does not wrap.
  if start < 0:
    if start div -1 < 0:
      symexTarget("s8aa_offset_div")
    return
  let (k, p) = readCStr(data, start)
  if k.len == 1 and p == start + 2:
    symexTarget("s8aa_offset_hit")
{.pop.}

proc sutCheckedZero(x, y: int) =
  ## The default (checked) build: Nim's own check raises DivByZeroDefect.
  let q = x div y
  if q == 3:
    symexTarget("s8aa_checked")

const optUnchecked = SymexSettings(integerSemantics: isOptimised,
                                   arithChecks: {acDivByZero, acRange})
const exactUnchecked = SymexSettings(integerSemantics: isExact,
                                     arithChecks: {acDivByZero, acRange})
const noChecks = SymexSettings(integerSemantics: isOptimised, arithChecks: {})

suite "S8aa (1): a division that traps in C is not a Defect":

  test "unchecked x div 0 is a trap, not a DivByZeroDefect (isOptimised)":
    ## RED: `sxRaised` DivByZeroDefect, witness (0, 0) -- whose replay
    ## aborts with SIGFPE.
    let r = symexFind(sutZeroDiv, tRaisedExn("DivByZeroDefect"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "unchecked x div 0 is a trap, not a DivByZeroDefect (isExact)":
    let r = symexFind(sutZeroDiv, tRaisedExn("DivByZeroDefect"),
                      exactUnchecked)
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "unsigned: unchecked x div 0 is a trap":
    let r = symexFind(sutZeroDivU, tRaisedExn("DivByZeroDefect"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "no execution continues past x div 0 (no checks at all)":
    ## RED: `sxSat` with witness (0, 0): the continuation carried Z3's
    ## `x div 0 == -1`, and the witness aborts on replay.
    let r = symexFind(sutZeroDiv, tLabel("s8aa_zero_div"), noChecks)
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "no execution continues past x mod 0 (no checks at all)":
    ## RED: `sxSat` with witness (0, 0) (Z3's `x mod 0 == x`).
    let r = symexFind(sutZeroMod, tLabel("s8aa_zero_mod"), noChecks)
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "checked arithmetic still raises DivByZeroDefect, and it replays":
    var real = ""
    try: sutCheckedZero(1, 0)
    except DivByZeroDefect: real = "DivByZeroDefect"
    check real == "DivByZeroDefect"
    let r = symexFind(sutCheckedZero, tRaisedExn("DivByZeroDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"
      var got = ""
      try: sutCheckedZero(r.raisedWitness[0], r.raisedWitness[1])
      except DivByZeroDefect: got = "DivByZeroDefect"
      check got == "DivByZeroDefect"

  test "low(T) div -1 and mod -1 at 32 and 64 bits trap (pinned)":
    template dead(fn: typed, lbl: string, st: static SymexSettings) =
      block:
        let r = symexFind(fn, tLabel(lbl), st)
        checkpoint lbl & " " & show(r.errors)
        check r.status == sxUnsat
    dead(sutLowDiv, "s8aa_low_div", optUnchecked)
    dead(sutLowDiv, "s8aa_low_div", exactUnchecked)
    dead(sutLowDiv32, "s8aa_low_div32", optUnchecked)
    dead(sutLowMod, "s8aa_low_mod", optUnchecked)

  test "low(int8) div -1 wraps, and the witness replays":
    let r = symexFind(sutLowDiv8, tLabel("s8aa_low_div8"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (x, y) = r.witness
      check x == low(int8) and y == -1'i8
      var q: int8
      {.push overflowChecks: off.}
      q = x div y
      {.pop.}
      check q == low(int8)

  test "a division away from the traps keeps its quotient":
    let r = symexFind(sutSafeDiv, tLabel("s8aa_safe_div"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (x, y) = r.witness
      check y < 0 and x div y == 7 and x mod y == -3

  test "a stamped B4 offset divided by -1 traps at low(int)":
    let r = symexFind(sutOffsetDiv, tLabel("s8aa_offset_div"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let r2 = symexFind(sutOffsetDiv, tLabel("s8aa_offset_hit"), optUnchecked)
    checkpoint show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      let (data, start) = r2.witness
      let (k, p) = readCStr(data, start)
      check k.len == 1 and p == start + 2

# ---- (2) the short-circuit join over store shapes ---------------------------

proc noteS(log: var string, c: char): bool =
  log.add c
  true

proc noteQ(log: var seq[int], c: int): bool =
  log.add c
  true

type Box = ref object
  n: int

proc noteH(b: Box, v: int): bool =
  b.n = b.n + v
  true

type Holder = ref object
  cur: Box

proc noteHo(h: Holder, b: Box): bool =
  h.cur = b
  true

proc multi(x: byte): bool =
  ## Two returns: the operand leaves two surviving paths.
  if x > 100'u8:
    return x == 200'u8
  x == 3'u8

proc multiRead(s: string, i: int): bool =
  ## Two returns, one of which reads `s[i]` unguarded.
  if i > 3:
    return s[i] == 'x'
  i == 1

proc sutStr(data: seq[byte]) =
  symexAssume(data.len == 12)
  var log = ""
  if (data[0] == 1'u8 or noteS(log, 'a')) and
     (data[2] == 3'u8 or noteS(log, 'b')) and
     (data[4] == 5'u8 or noteS(log, 'c')) and
     (data[6] == 7'u8 or noteS(log, 'd')) and
     (data[8] == 9'u8 or noteS(log, 'e')) and
     (data[10] == 11'u8 or noteS(log, 'f')):
    if log == "ad":
      symexTarget("s8aa_str")
    if log.len == 7:
      symexTarget("s8aa_str_dead")

proc sutSeq(data: seq[byte]) =
  symexAssume(data.len == 12)
  var log: seq[int] = @[]
  if (data[0] == 1'u8 or noteQ(log, 1)) and
     (data[2] == 3'u8 or noteQ(log, 2)) and
     (data[4] == 5'u8 or noteQ(log, 3)) and
     (data[6] == 7'u8 or noteQ(log, 4)) and
     (data[8] == 9'u8 or noteQ(log, 5)) and
     (data[10] == 11'u8 or noteQ(log, 6)):
    if log.len == 2 and log[0] == 3 and log[1] == 6:
      symexTarget("s8aa_seq")

proc sutHeap(data: seq[byte], b: Box) =
  symexAssume(data.len == 12 and b != nil)
  let n0 = b.n
  if (data[0] == 1'u8 or noteH(b, 1)) and
     (data[2] == 3'u8 or noteH(b, 2)) and
     (data[4] == 5'u8 or noteH(b, 4)) and
     (data[6] == 7'u8 or noteH(b, 8)) and
     (data[8] == 9'u8 or noteH(b, 16)) and
     (data[10] == 11'u8 or noteH(b, 32)):
    if n0 < 1000 and n0 > -1000 and b.n == n0 + 5:
      symexTarget("s8aa_heap")

proc sutRef(data: seq[byte], a, b: Box) =
  ## A local ref rebound inside the operands.
  symexAssume(data.len == 12 and a != nil and b != nil and a != b)
  var cur = a
  if (data[0] == 1'u8 or (cur = b; true)) and
     (data[2] == 3'u8 or (cur = a; true)) and
     (data[4] == 5'u8 or (cur = b; true)) and
     (data[6] == 7'u8 or (cur = a; true)) and
     (data[8] == 9'u8 or (cur = b; true)) and
     (data[10] == 11'u8 or (cur = a; true)):
    if cur == b and data[0] != 1'u8:
      symexTarget("s8aa_ref")

proc sutRefCell(data: seq[byte], h: Holder, a, b: Box) =
  ## A ref stored in a heap cell, rebound by a callee.
  symexAssume(data.len == 12 and h != nil and a != nil and b != nil and
              a != b)
  h.cur = a
  if (data[0] == 1'u8 or noteHo(h, b)) and
     (data[2] == 3'u8 or noteHo(h, a)) and
     (data[4] == 5'u8 or noteHo(h, b)) and
     (data[6] == 7'u8 or noteHo(h, a)) and
     (data[8] == 9'u8 or noteHo(h, b)) and
     (data[10] == 11'u8 or noteHo(h, a)):
    if h.cur == b and data[0] != 1'u8:
      symexTarget("s8aa_ref_cell")

proc sutMulti(data: seq[byte]) =
  symexAssume(data.len == 12)
  if (data[0] == 1'u8 or multi(data[1])) and
     (data[2] == 3'u8 or multi(data[3])) and
     (data[4] == 5'u8 or multi(data[5])) and
     (data[6] == 7'u8 or multi(data[7])) and
     (data[8] == 9'u8 or multi(data[9])) and
     (data[10] == 11'u8 or multi(data[11])):
    if data[0] != 1'u8 and data[1] == 200'u8 and data[2] != 3'u8:
      symexTarget("s8aa_multi")

proc sutMultiRead(s: string, i, j: int) =
  if (i == 0 or multiRead(s, i)) and (j == 0 or multiRead(s, j)):
    symexTarget("s8aa_multi_read")

const heapRoom = SymexSettings(budget: ResourceBudget(maxHeapDepth: 64))

suite "S8aa (2): the short-circuit join covers store shapes":

  test "an operand that writes a string joins (6 pairs)":
    ## RED: 117 Z3 calls (2^m paths).
    symexZ3CallCount = 0
    let r = symexFind(sutStr, tLabel("s8aa_str"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] != 1 and d[2] == 3 and d[4] == 5 and d[6] != 7 and
            d[8] == 9 and d[10] == 11
    let r2 = symexFind(sutStr, tLabel("s8aa_str_dead"))
    checkpoint show(r2.errors)
    check r2.status == sxUnsat

  test "an operand that appends to a seq joins (6 pairs)":
    ## RED: 117 Z3 calls.
    symexZ3CallCount = 0
    let r = symexFind(sutSeq, tLabel("s8aa_seq"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] == 1 and d[2] == 3 and d[4] != 5 and d[6] == 7 and
            d[8] == 9 and d[10] != 11

  test "an operand that writes a heap cell joins (6 pairs)":
    symexZ3CallCount = 0
    let r = symexFind(sutHeap, tLabel("s8aa_heap"), heapRoom)
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] != 1 and d[2] == 3 and d[4] != 5 and d[6] == 7 and
            d[8] == 9 and d[10] == 11

  template refChain(fn: typed, lbl: string, st: static SymexSettings) =
    block:
      symexZ3CallCount = 0
      let r = symexFind(fn, tLabel(lbl), st)
      checkpoint lbl & " " & show(r.errors)
      checkpoint "z3 calls: " & $symexZ3CallCount
      check r.status == sxSat
      check symexZ3CallCount <= 16
      if r.status == sxSat:
        let d = r.witness[0]
        # The last rebinding wins: the last operand whose guard is false
        # names `b` (operands 1, 3, 5).
        var last = -1
        for k in 0 ..< 6:
          if d[2 * k] != byte(2 * k + 1): last = k
        check d[0] != 1 and last in [0, 2, 4]

  test "an operand that rebinds a local ref joins (6 pairs)":
    refChain(sutRef, "s8aa_ref", SymexSettings())

  test "an operand that rebinds a ref in a heap cell joins (6 pairs)":
    refChain(sutRefCell, "s8aa_ref_cell", heapRoom)

  test "an operand with two surviving paths joins (6 pairs)":
    ## RED: 731 Z3 calls.
    symexZ3CallCount = 0
    let r = symexFind(sutMulti, tLabel("s8aa_multi"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 24
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] != 1 and d[1] == 200 and d[2] != 3 and
            (d[3] == 3 or d[3] == 200)

  test "a raising read on one of two survivors still raises, and replays":
    ## Probe: `sutMultiRead("", 4, 0)` raises IndexDefect (`s[4]`).
    var raised = false
    try: sutMultiRead("", 4, 0)
    except IndexDefect: raised = true
    check raised
    let r = symexFind(sutMultiRead, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      let (s, i, j) = r.raisedWitness
      var again = false
      try: sutMultiRead(s, i, j)
      except IndexDefect: again = true
      check again
    let r2 = symexFind(sutMultiRead, tLabel("s8aa_multi_read"))
    checkpoint show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      let (s, i, j) = r2.witness
      var hit = true
      try: hit = (i == 0 or multiRead(s, i)) and (j == 0 or multiRead(s, j))
      except IndexDefect: hit = false
      check hit

# ---- (3) B6 with a negative offset ------------------------------------------

proc readCStringOpt(s: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc readOptionsSut(s: string, start: int) =
  ## `tsymex_r6_b6_optionregion.nim`'s pair loop.
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = readCStringOpt(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringOpt(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("s8aa_b6_done")

proc readOptionsShort(s: string, start: int) =
  ## The same loop on a short region, where the fallback's unroll ends
  ## inside its budget.
  symexAssume(s.len <= 2)
  readOptionsSut(s, start)

suite "S8aa (3): B6 with a negative offset":

  test "oracle: a negative start raises IndexDefect on the first scan":
    var got = ""
    try: readOptionsSut("a", -1)
    except IndexDefect: got = "IndexDefect"
    check got == "IndexDefect"

  test "a negative start is an IndexDefect witness":
    ## RED: `sxUnknown` (`beBudgetExhausted`): the member branch took the
    ## negative start (`str.substr` at -1 is "", a member).
    let r = symexFind(readOptionsSut, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "IndexDefect"
      let (s, start) = r.raisedWitness
      check start < 0
      var got = ""
      try: readOptionsSut(s, start)
      except IndexDefect: got = "IndexDefect"
      except CatchableError: got = $getCurrentException().name
      check got == "IndexDefect"

  test "a short region: the IndexDefect is found, not a false sxUnsat":
    let r = symexFind(readOptionsShort, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      let (s, start) = r.raisedWitness
      var got = ""
      try: readOptionsShort(s, start)
      except IndexDefect: got = "IndexDefect"
      except CatchableError: got = $getCurrentException().name
      check got == "IndexDefect"

# ---- (4) a same-width reinterpret of an Int-sorted value --------------------

proc readCStrU(data: seq[byte], offset: uint): (string, uint) =
  ## B4 with an unsigned offset: the bound is `data.len.uint`.
  var acc = ""
  var i = offset
  while i < data.len.uint:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

proc sutU(data: seq[byte], start: uint) =
  let (k, p) = readCStrU(data, start)
  if k.len == 2 and p == start + 3:
    symexTarget("s8aa_u_hit")

proc sutFindU(s: string) =
  ## `find`'s -1 reinterprets as `high(uint)`.
  if s.find('a').uint == high(uint) and s.len == 2:
    symexTarget("s8aa_findu")

proc sutLenU(s: string) =
  if s.len.uint == 3'u:
    symexTarget("s8aa_lenu")
  # Bounded: an unbounded `len` is past the model's search bound
  # (`maxSeqLen`), so the unbounded form is an honest `sxUnknown`.
  if s.len <= 4 and s.len.uint > high(uint) - 2'u:
    symexTarget("s8aa_lenu_dead")

suite "S8aa (4): len and find reinterpreted as uint":

  test "an unsigned B4 scan: the hit, with no decline, and it replays":
    ## RED: `feUnsupportedOpHavoc` from `lowerConvIntReinterpret`.
    let r = symexFind(sutU, tLabel("s8aa_u_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
    if r.status == sxSat:
      let (data, start) = r.witness
      let (k, p) = readCStrU(data, start)
      check k.len == 2 and p == start + 3

  test "find's -1 as uint is high(uint)":
    ## Probe: `"bb".find('a').uint == high(uint)`.
    check "bb".find('a').uint == high(uint)
    let r = symexFind(sutFindU, tLabel("s8aa_findu"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
    if r.status == sxSat:
      check r.witness[0].len == 2 and 'a' notin r.witness[0]

  test "len as uint keeps its value":
    let r = symexFind(sutLenU, tLabel("s8aa_lenu"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
    if r.status == sxSat:
      check r.witness[0].len == 3
    let r2 = symexFind(sutLenU, tLabel("s8aa_lenu_dead"))
    checkpoint show(r2.errors)
    check r2.status == sxUnsat

suite "S8aa: walker version":

  test "symexWalkerVersion >= 172":
    check parseInt(symexWalkerVersion) >= 172
