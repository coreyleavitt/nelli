## RFC-0005 S8aa (1) -- arithmetic that traps in C, checks-off build half.
## RFC-0016 W1-d2 (rule b: the property is "a division that traps in C is a
## halt, not a Defect and not a wrap"): moved from `tsymex_rfc0005_s8aa_remainder`
## and built with `--overflowChecks:off` (its `.nim.cfg`), so the `arithChecks`
## opt-outs became the build's own checks. Nothing is weakened: the same
## `halted(...)` expectations, now with settings that agree with the build and
## no `{.push overflowChecks: off.}` decline in a checks-on build.
## The default-build control (`sutCheckedZero`) stays in the original file.
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

type ScanError = object of CatchableError

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

const optUnchecked = SymexSettings(integerSemantics: isOptimised)
const exactUnchecked = SymexSettings(integerSemantics: isExact)
const noChecks = SymexSettings(integerSemantics: isOptimised)
  ## The three settings are the build's own (checks-off, range on): they agree
  ## with the build and taint nothing.

proc halted(r: SymexResult[auto]; k: UbKind): bool =
  ## RFC-0016 W1-d1a. Natively `low(T) div -1` and `low(T) mod -1` at 32 and
  ## 64 bits die of SIGFPE on x86-64 (probed, c and cpp), so the label is not
  ## reached there; but the C division is undefined, so the walk no longer
  ## claims `sxUnsat`: the path halts through `haltUndefined`, the run records
  ## the kind (`ubIntMinModMinusOne` for `mod`, `ubSignedOverflow` for the
  ## unchecked `div`) and the verdict is `sxUnknown`. The old pins
  ## (`sxUnsat`) were the hardware's outcome, not the language's. For a
  ## symbolic `x div y` the undefined input (low, -1) is reachable before the
  ## `y == 0` guard is read, so the zero-divisor pins halt too.
  r.status == sxUnknown and r.errors.hasKind(k)

suite "S8aa (1): a division that traps in C is not a Defect":

  test "unchecked x div 0 is a trap, not a DivByZeroDefect (isOptimised)":
    ## RED: `sxRaised` DivByZeroDefect, witness (0, 0) -- whose replay
    ## aborts with SIGFPE.
    let r = symexFind(sutZeroDiv, tRaisedExn("DivByZeroDefect"), optUnchecked)
    checkpoint show(r.errors)
    check r.halted(ubSignedOverflow)

  test "unchecked x div 0 is a trap, not a DivByZeroDefect (isExact)":
    let r = symexFind(sutZeroDiv, tRaisedExn("DivByZeroDefect"),
                      exactUnchecked)
    checkpoint show(r.errors)
    check r.halted(ubSignedOverflow)

  test "unsigned: unchecked x div 0 is a trap":
    ## Native (pinned toolchain, c and cpp): `10'u64 div 0` is a SIGFPE, no
    ## `except` arm runs. RFC-0016 W1-d1b: the C division is undefined there,
    ## so the zero side halts (`ubUnsignedDivZero`) instead of being a
    ## confined, trusted `sxUnsat`.
    let r = symexFind(sutZeroDivU, tRaisedExn("DivByZeroDefect"), optUnchecked)
    checkpoint show(r.errors)
    check r.status != sxRaised
    check not r.trusted
    check r.halted(ubUnsignedDivZero)

  test "no execution continues past x div 0 (no checks at all)":
    ## RED: `sxSat` with witness (0, 0): the continuation carried Z3's
    ## `x div 0 == -1`, and the witness aborts on replay.
    let r = symexFind(sutZeroDiv, tLabel("s8aa_zero_div"), noChecks)
    checkpoint show(r.errors)
    check r.halted(ubSignedOverflow)

  test "no execution continues past x mod 0 (no checks at all)":
    ## RED: `sxSat` with witness (0, 0) (Z3's `x mod 0 == x`).
    let r = symexFind(sutZeroMod, tLabel("s8aa_zero_mod"), noChecks)
    checkpoint show(r.errors)
    check r.halted(ubIntMinModMinusOne)

  test "low(T) div -1 and mod -1 at 32 and 64 bits trap (pinned)":
    template dead(fn: typed, lbl: string, st: static SymexSettings,
                  k: UbKind) =
      block:
        let r = symexFind(fn, tLabel(lbl), st)
        checkpoint lbl & " " & show(r.errors)
        check r.halted(k)
    dead(sutLowDiv, "s8aa_low_div", optUnchecked, ubSignedOverflow)
    dead(sutLowDiv, "s8aa_low_div", exactUnchecked, ubSignedOverflow)
    dead(sutLowDiv32, "s8aa_low_div32", optUnchecked, ubSignedOverflow)
    dead(sutLowMod, "s8aa_low_mod", optUnchecked, ubIntMinModMinusOne)

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
    check r.halted(ubSignedOverflow)
    let r2 = symexFind(sutOffsetDiv, tLabel("s8aa_offset_hit"), optUnchecked)
    checkpoint show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      let (data, start) = r2.witness
      let (k, p) = readCStr(data, start)
      check k.len == 1 and p == start + 2

