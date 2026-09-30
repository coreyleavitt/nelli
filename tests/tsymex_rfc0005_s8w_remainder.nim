## RFC-0005 (soundness channels) slice S8w -- S8t's remainder.
##
## This slice closes:
##   (1) an alternating `and`/`or` chain (`(a or b) and (c or d) and ...`)
##       forked 2^m paths when its inner operands had raising reads: S8t's
##       nested lowering (`lowerShortCircuitParts`) covered one operator,
##       and an operand of the other operator was lowered by its own
##       recursive parse, whose guard forked two paths that both went on
##       into the rest of the chain;
##   (2) a `while` guard whose first operand hoists a read, in a body that
##       uses `continue`, declined (R14 Case 2);
##   (3) an `isIntOffset` param that `promoteSound` turned down stayed an
##       unstamped, unbounded Int that never wrapped;
##   (4) the base's false `OverflowDefect` witness `(@[], -1)` on a B4 scan.
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

# ---- (1) alternating and/or chains ------------------------------------------

proc sutAndOfOrs(data: seq[byte]) =
  symexAssume(data.len == 12)
  if (data[0] == 1'u8 or data[1] == 2'u8) and
     (data[2] == 3'u8 or data[3] == 4'u8) and
     (data[4] == 5'u8 or data[5] == 6'u8) and
     (data[6] == 7'u8 or data[7] == 8'u8) and
     (data[8] == 9'u8 or data[9] == 10'u8) and
     (data[10] == 11'u8 or data[11] == 12'u8):
    if data[0] != 1'u8 and data[11] != 12'u8:
      symexTarget("s8w_and_of_ors")

proc sutOrOfAnds(data: seq[byte]) =
  symexAssume(data.len == 12)
  if (data[0] == 1'u8 and data[1] == 2'u8) or
     (data[2] == 3'u8 and data[3] == 4'u8) or
     (data[4] == 5'u8 and data[5] == 6'u8) or
     (data[6] == 7'u8 and data[7] == 8'u8) or
     (data[8] == 9'u8 and data[9] == 10'u8) or
     (data[10] == 11'u8 and data[11] == 12'u8):
    discard
  else:
    if data[0] == 1'u8 and data[2] == 3'u8 and data[10] == 11'u8:
      symexTarget("s8w_or_of_ands")

proc sutLetAlt(data: seq[byte]) =
  symexAssume(data.len == 12)
  let ok = (data[0] == 1'u8 or data[1] == 2'u8) and
           (data[2] == 3'u8 or data[3] == 4'u8) and
           (data[4] == 5'u8 or data[5] == 6'u8) and
           (data[6] == 7'u8 or data[7] == 8'u8) and
           (data[8] == 9'u8 or data[9] == 10'u8) and
           (data[10] == 11'u8 or data[11] == 12'u8)
  if ok and data[1] == 2'u8 and data[0] != 1'u8:
    symexTarget("s8w_let_alt")

proc sutAltGuarded(s: string, i, j: int) =
  ## Short-circuit: `s[i]` and `s[j]` are read only when in range.
  if (i < 0 or i >= s.len or s[i] == 'a') and
     (j < 0 or j >= s.len or s[j] == 'b') and
     (i >= 0 and i < s.len and s[i] != 'z'):
    symexTarget("s8w_alt_guarded")

proc sutAltUnguarded(s: string, i, j: int) =
  ## `s[j]` is read whenever the first `or` is true -- it can raise.
  if (i < 0 or i >= s.len or s[i] == 'a') and (s[j] == 'b' or j < 0):
    symexTarget("s8w_alt_unguarded")

suite "S8w (1): an alternating and/or chain is linear in paths":

  test "(a or b) and (c or d) and ... (6 pairs) in linearly many Z3 calls":
    ## RED: 2^6-fold path growth. GREEN: the target solve plus one UNSAT
    ## IndexDefect solve per read.
    symexZ3CallCount = 0
    let r = symexFind(sutAndOfOrs, tLabel("s8w_and_of_ors"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d.len == 12 and d[0] != 1 and d[1] == 2 and d[11] != 12 and
            d[10] == 11 and (d[2] == 3 or d[3] == 4)

  test "(a and b) or (c and d) or ... (6 pairs) in linearly many Z3 calls":
    symexZ3CallCount = 0
    let r = symexFind(sutOrOfAnds, tLabel("s8w_or_of_ands"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] == 1 and d[1] != 2 and d[2] == 3 and d[3] != 4 and
            d[10] == 11 and d[11] != 12

  test "let x = (a or b) and ... (6 pairs)":
    symexZ3CallCount = 0
    let r = symexFind(sutLetAlt, tLabel("s8w_let_alt"))
    checkpoint show(r.errors)
    checkpoint "z3 calls: " & $symexZ3CallCount
    check r.status == sxSat
    check symexZ3CallCount <= 16
    if r.status == sxSat:
      let d = r.witness[0]
      check d[0] != 1 and d[1] == 2

  test "guarded reads in an alternating chain never raise":
    ## Probe: `sutAltGuarded` never raises; `("a", 0, 5)` hits.
    sutAltGuarded("a", 0, 5)
    sutAltGuarded("", -1, 7)
    let r = symexFind(sutAltGuarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let r2 = symexFind(sutAltGuarded, tLabel("s8w_alt_guarded"))
    checkpoint show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      let (s, i, j) = r2.witness
      check i >= 0 and i < s.len and s[i] == 'a'
      check j < 0 or j >= s.len or s[j] == 'b'

  test "an unguarded read in an alternating chain still raises":
    ## Probe: `sutAltUnguarded("", -1, 0)` raises IndexDefect.
    var raised = false
    try: sutAltUnguarded("", -1, 0)
    except IndexDefect: raised = true
    check raised
    let r = symexFind(sutAltUnguarded, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      let (s, i, j) = r.raisedWitness
      var again = false
      try: sutAltUnguarded(s, i, j)
      except IndexDefect: again = true
      check again

# ---- (2) a hoisting first guard operand with `continue` in the body ---------

proc sutContGuard(s: string): (int, int) =
  ## The guard's first operand (an `or` reading `s[i]`) hoists, and the
  ## body `continue`s at i == 2: Nim re-evaluates the whole guard, reading
  ## `s[2]`.
  symexAssume(s.len <= 4)
  var i = 0
  var n = 0
  while (i >= s.len or s[i] != 'x') and i < 4:
    inc i
    if i == 2:
      continue
    inc n
  (i, n)

proc sutContHit(s: string) =
  let (i, n) = sutContGuard(s)
  if i == 2 and n == 1:
    symexTarget("s8w_cont_hit")

proc sutContDead(s: string) =
  ## Dead in Nim: reaching i == 3 means the guard passed at i == 2, so
  ## `s[2] != 'x'`. A guard left stale by the `continue` (computed at
  ## i == 1) would let the loop run on past an `x` at 2.
  let (i, n) = sutContGuard(s)
  if i == 3 and n == 2 and s.len == 3 and s[2] == 'x':
    symexTarget("s8w_cont_dead")

proc caseTwoContinue(a, b: int, s: string) =
  ## `tsymex_r14_case2_degrade`'s shape: `(a div b) > i` hoists.
  var i = 0
  while (a div b) > i and s[i] != 'z':
    inc i
    continue
  if i == 3:
    symexTarget("s8w_case2_hit")

proc sutOrGuardCont(s: string) =
  ## R14 Case 3: a plain `or` guard with a fault, and `continue`.
  symexAssume(s.len <= 3)
  var i = 0
  var n = 0
  while i >= s.len or s[i] != 'x':
    inc i
    if i >= 4:
      break
    if i == 1:
      continue
    inc n
  if n == 2 and i == 4:
    symexTarget("s8w_case3_hit")

suite "S8w (2): a while guard whose first operand hoists, with continue":

  test "the continue re-evaluates the guard: the i == 2 exit is reached":
    ## Probe: `sutContGuard("aax") == (2, 1)`, `("a") == (4, 3)`.
    check sutContGuard("aax") == (2, 1)
    check sutContGuard("a") == (4, 3)
    let r = symexFind(sutContHit, tLabel("s8w_cont_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      checkpoint "witness: " & $r.witness
      let (i, n) = sutContGuard(r.witness[0])
      check i == 2 and n == 1

  test "a stale guard's extra iteration is dead":
    ## RED: `sxUnknown` (the R14 Case 2 decline).
    let r = symexFind(sutContDead, tLabel("s8w_cont_dead"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "the guarded read never raises":
    let r = symexFind(sutContGuard, tIndexError())
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "tsymex_r14_case2_degrade's shape gets its verdict":
    ## Probe: `caseTwoContinue(3, 1, "abc")` reaches i == 3.
    let r = symexFind(caseTwoContinue, tLabel("s8w_case2_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (a, b, s) = r.witness
      check b != 0 and a div b >= 3 and s.len >= 3 and 'z' notin s[0 .. 2]

  test "an or guard with a fault and continue (R14 Case 3)":
    ## Probe: "" gives n == 2, i == 4 (i == 1 continues; i == 2, 3 count).
    let r = symexFind(sutOrGuardCont, tLabel("s8w_case3_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    let r2 = symexFind(sutOrGuardCont, tIndexError())
    checkpoint show(r2.errors)
    check r2.status == sxUnsat

# ---- (3) a B4 offset promotion turned down: wrap, or a scoped decline -------

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

{.push overflowChecks: off.}
proc sutWrapB4(data: seq[byte], start: int) =
  ## Built without overflow checks (`-d:danger`'s arithmetic): `start + 1`
  ## wraps to `low(int)` at `high(int)`.
  let bump = start + 1
  if bump < start:
    symexTarget("s8w_wrap_b4")
  let (k, p) = readCStr(data, start)
  if k.len == 2 and p == start + 3:
    symexTarget("s8w_wrap_b4_hit")

proc sutWrapMulB4(data: seq[byte], start: int) =
  ## `start * 4` wraps: `start == high(int) div 2` gives a negative product.
  let q = start * 4
  if start > 0 and q < 0:
    symexTarget("s8w_wrapmul_b4")
  let (k, p) = readCStr(data, start)
  if k.len == 1 and p == start + 2:
    symexTarget("s8w_wrapmul_b4_hit")
{.pop.}

proc sutBitB4(data: seq[byte], start: int) =
  ## A bit operation on the offset bans its promotion (ADR-0001), and the
  ## arithmetic is checked: `start + 1` raises OverflowDefect at high(int).
  ## A negative offset returns first, so no read can raise IndexDefect and
  ## the only reachable Defect is the overflow.
  if start < 0: return
  let low8 = start and 0xFF
  let bump = start + 1
  let (k, p) = readCStr(data, start)
  if low8 == 7 and k.len == 1 and p == bump + 1:
    symexTarget("s8w_bit_b4")

proc sutSignBitB4(data: seq[byte], start: int) =
  ## A mask keeps the sign: `start and -2` is negative for a negative
  ## `start`. The bridge to bit-vectors is signed, as `int` is.
  if (start and -2) < 0:
    symexTarget("s8w_signbit_b4")
  if start < 0: return
  let (k, p) = readCStr(data, start)
  if k.len == 1 and p == start + 2:
    symexTarget("s8w_signbit_b4_hit")

proc sutShiftB4(data: seq[byte], start: int) =
  ## A shift on the offset: before S8w an unstamped Int reached the shift
  ## and failed the walker's assertion.
  if start < 0: return
  let hi = start shr 2
  let (k, p) = readCStr(data, start)
  if hi == 1 and k.len == 1 and p == start + 2:
    symexTarget("s8w_shift_b4")

proc sutFindMask(s: string) =
  ## An UNSTAMPED Int (`find`'s result, -1 when absent) through a mask:
  ## `find` returns `int`, so `-1 and -2` is `-2`, negative.
  if (s.find('a') and -2) < 0:
    symexTarget("s8w_findmask")

proc sutFindShift(s: string) =
  ## A shift on an unstamped Int: `find`'s -1 shifted right stays -1
  ## (`shr` on `int` is arithmetic).
  if (s.find('a') shr 1) < 0 and s.len > 2:
    symexTarget("s8w_findshift")

proc sutB4(data: seq[byte], start: int) =
  ## The base (a58856d) shape behind S8t's "false OverflowDefect" note.
  let (k, p) = readCStr(data, start)
  if k.len == 2 and p == start + 3:
    symexTarget("s8w_b4")

const exactUnchecked = SymexSettings(integerSemantics: isExact,
                                     arithChecks: {acDivByZero, acRange})
const optUnchecked = SymexSettings(integerSemantics: isOptimised,
                                   arithChecks: {acDivByZero, acRange})

suite "S8w (3): a B4 offset whose promotion is turned down stays faithful":

  test "oracle: without overflow checks start + 1 wraps":
    var hit = false
    try: sutWrapB4(@[], high(int))
    except ScanError: hit = true
    check hit
    check (block:
      var x = high(int) div 2
      {.push overflowChecks: off.}
      let q = x * 4
      {.pop.}
      q < 0)

  test "isExact, unchecked: the wrap is reachable":
    ## RED: `sxUnsat` -- the offset was an unbounded Int, and `start + 1 <
    ## start` has no solution over the integers.
    let r = symexFind(sutWrapB4, tLabel("s8w_wrap_b4"), exactUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == high(int)

  test "isOptimised, unchecked: the wrap is reachable":
    ## RED: `sxUnsat` (the wrap scan bans the promotion; the offset stayed
    ## an unbounded Int).
    let r = symexFind(sutWrapB4, tLabel("s8w_wrap_b4"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == high(int)

  test "isOptimised, unchecked: a multiplication's wrap is reachable":
    let r = symexFind(sutWrapMulB4, tLabel("s8w_wrapmul_b4"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let start = r.witness[1]
      var q: int
      {.push overflowChecks: off.}
      q = start * 4
      {.pop.}
      check start > 0 and q < 0

  test "unchecked: the B4 hit is still reachable, and replays":
    let r = symexFind(sutWrapB4, tLabel("s8w_wrap_b4_hit"), optUnchecked)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      let (k, p) = readCStr(data, start)
      check k.len == 2 and p == start + 3

  test "a bit-banned offset keeps its OverflowDefect":
    ## Probe: `sutBitB4(@[], high(int))` raises OverflowDefect.
    var raised = false
    try: sutBitB4(@[], high(int))
    except OverflowDefect: raised = true
    check raised
    let r = symexFind(sutBitB4, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
      var real = ""
      try: sutBitB4(r.raisedWitness[0], r.raisedWitness[1])
      except OverflowDefect: real = "OverflowDefect"
      check real == "OverflowDefect"

  test "a bit-banned offset's hit is reachable, and replays":
    let r = symexFind(sutBitB4, tLabel("s8w_bit_b4"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      check (start and 0xFF) == 7
      let (k, p) = readCStr(data, start)
      check k.len == 1 and p == start + 2

  test "a mask on a signed offset keeps its sign":
    ## Probe: `(-1 and -2) < 0`.
    check (-1 and -2) < 0
    let r = symexFind(sutSignBitB4, tLabel("s8w_signbit_b4"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[1] and -2) < 0

  test "a shift on a banned offset is modelled":
    ## RED: the walker's "shift on promoted Z3Int" assertion.
    let r = symexFind(sutShiftB4, tLabel("s8w_shift_b4"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (data, start) = r.witness
      check (start shr 2) == 1
      let (k, p) = readCStr(data, start)
      check k.len == 1 and p == start + 2

  test "a mask on an unstamped int keeps its sign":
    ## Probe: `"b".find('a') == -1` and `(-1 and -2) < 0`.
    check "b".find('a') == -1
    let r = symexFind(sutFindMask, tLabel("s8w_findmask"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[0].find('a') and -2) < 0

  test "a shift on an unstamped int is modelled":
    ## Probe: `(-1 shr 1) == -1`.
    check (-1 shr 1) == -1
    let r = symexFind(sutFindShift, tLabel("s8w_findshift"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[0].find('a') shr 1) < 0 and r.witness[0].len > 2

suite "S8w (4): the base's B4 OverflowDefect finding":

  test "a negative offset raises IndexDefect, reported as IndexDefect":
    ## S8t's note read the base's `(@[], -1)` finding under
    ## `tRaisedExn("OverflowDefect")` as a false OverflowDefect. It was
    ## E6: a reachable Defect surfaces as `sxRaised` with ITS OWN type,
    ## whatever the target, and the type was IndexDefect. Probe:
    ## `sutB4(@[], -1)` raises IndexDefect (`data[-1]`).
    var real = ""
    try: sutB4(@[], -1)
    except IndexDefect: real = "IndexDefect"
    check real == "IndexDefect"
    template checkB4(tgt: static SymexTarget) =
      block:
        let r = symexFind(sutB4, tgt)
        checkpoint show(r.errors)
        check r.status == sxRaised
        if r.status == sxRaised:
          check r.raisedTypeId == "IndexDefect"
          var got = ""
          try: sutB4(r.raisedWitness[0], r.raisedWitness[1])
          except IndexDefect: got = "IndexDefect"
          except CatchableError, Defect: got = $getCurrentException().name
          check got == "IndexDefect"
    checkB4(tRaisedExn("OverflowDefect"))
    checkB4(tIndexError())

suite "S8w: walker version":

  test "symexWalkerVersion >= 171":
    check parseInt(symexWalkerVersion) >= 171
