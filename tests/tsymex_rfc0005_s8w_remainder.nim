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
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8w_remainder_b`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 63 s).

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

{.push overflowChecks: off.}
{.pop.}
