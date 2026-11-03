## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 3 of 7 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder_b`,
## `tsymex_rfc0005_s8ax_remainder_d`, `tsymex_rfc0005_s8ax_remainder_e`,
## `tsymex_rfc0005_s8ax_remainder_f`, `tsymex_rfc0005_s8ax_remainder_g`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template verdictS(fn: typed, lbl: string, want: SymexStatusKind,
                  s: SymexSettings) =
  block:
    let r = symexFind(fn, tLabel(lbl), s)
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  ## The verdict, with nothing recorded at all.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0

# ---- (4) every signed int heap cell is Int-sorted -----------------------------
#
# S8as made the plain `int` heap Int-sorted only when every `int` parameter
# was an Int; a ranged or narrower cell stayed a bit-vector. A cell of one
# sort holding a value of the other went through `int2bv`/`bv2int` and back,
# which Z3 decides only slowly. Measured (Linux, Z3 5.1), before -> after:
# `mx_dead` 50.6 s -> 0.03 s, `rg_dead` 71.1 s -> 0.03 s, `nw_dead`
# 18.0 s -> 0.02 s; `mw_dead` and the S8an `ab_dead` shape stay under 0.02 s.
# Each cell's sort is its type's; a bit-vector stored and read back meets
# its source unconverted (`intOfBV`, and a read at the address the heap's
# last store wrote is that store's value). The rlimit below is far under
# what the slow forms needed.

type S8axBox = object
  s: range[-5000..5000]

proc sutIntMixed(v, w: int) =
  symexAssume(v > -1000 and v < 1000)
  let r = new int
  r[] = v
  r[] += 1
  if r[] == 5 and w == 3: symexTarget("mx")
  if r[] != v + 1: symexTarget("mx_dead")

proc sutIntMixedW(v, w: int) =
  symexAssume(v > -1000 and v < 1000)
  let q = new int
  q[] = w
  if q[] != w: symexTarget("mw_dead")
  if q[] == v + 1: symexTarget("mw")

proc sutIntRanged(v: int) =
  symexAssume(v > -1000 and v < 1000)
  let b = new S8axBox
  b.s = v
  b.s = b.s + 1
  if b.s == 5: symexTarget("rg")
  if b.s != v + 1: symexTarget("rg_dead")

proc sutIntNarrow(v: int32) =
  symexAssume(v > -1000 and v < 1000)
  let r = new int32
  r[] = v
  r[] += 1
  if r[] == 5: symexTarget("nw")
  if r[] != v + 1: symexTarget("nw_dead")

proc s8axGetQ(p: ptr int): int = p[]

proc sutIntAddrBV(v: int) =
  var x = v
  if s8axGetQ(addr x) == 7: symexTarget("ab")
  if s8axGetQ(addr x) != v: symexTarget("ab_dead")

proc sutIntNarrowWiden(v: int32) =
  let r = new int32
  r[] = v
  if int(r[]) > 5 and int64(r[]) < 9: symexTarget("nwd")

# WRONG VERDICTS (found by the Windows legs on S8as's own tests): nothing
# bounded an Int-sorted cell's input value by its type. `b.x` of an `int8`
# field read as any integer, so `int(b.x) > 127` was a false sxSat, whose
# witness (`x: 128`) crashed the typed result with a RangeDefect; and
# `b.n + 1`'s overflow raise was SAT with `b.n` below `low(int)`, whose
# witness extraction raised out of the walk and ended it with nothing
# recorded: a false sxUnsat on a target after a heap write in a branch on a
# seq element (S8aa's heap join, and base too where the heap was Int).

type
  S8axBoxN = ref object
    n: int
  S8axBox8 = ref object
    x: int8
  S8axBoxR = ref object
    r: range[0..9]

proc sutCellBranch(data: seq[byte], b: S8axBoxN) =
  symexAssume(data.len == 4 and b != nil)
  let n0 = b.n
  if data[0] != 1'u8:
    b.n = b.n + 1
  if b.n == n0 + 1: symexTarget("cb")

proc sutCell8(b: S8axBox8, d: int) =
  symexAssume(b != nil and d > -5 and d < 5)
  if int(b.x) > 127: symexTarget("c8_dead")
  if int(b.x) == -128: symexTarget("c8")

proc sutCellR(b: S8axBoxR, d: int) =
  symexAssume(b != nil and d > -5 and d < 5)
  if int(b.r) > 9: symexTarget("cr_dead")
  if int(b.r) == 9: symexTarget("cr")

const s8axTight = SymexSettings(budget: ResourceBudget(queryRLimit: 5_000_000))

suite "RFC-0005 S8ax (4): Int-sorted int heap cells":
  test "a cell of a mixed Int and bit-vector run":
    verdictS(sutIntMixed, "mx", sxSat, s8axTight)
    verdictS(sutIntMixed, "mx_dead", sxUnsat, s8axTight)
    verdictS(sutIntMixedW, "mw", sxSat, s8axTight)
    verdictS(sutIntMixedW, "mw_dead", sxUnsat, s8axTight)
  test "a ranged cell":
    verdictS(sutIntRanged, "rg", sxSat, s8axTight)
    verdictS(sutIntRanged, "rg_dead", sxUnsat, s8axTight)
  test "a cell narrower than 64 bits":
    verdictS(sutIntNarrow, "nw", sxSat, s8axTight)
    verdictS(sutIntNarrow, "nw_dead", sxUnsat, s8axTight)
  test "a narrow cell widened":
    verdict(sutIntNarrowWiden, "nwd", sxSat)
  test "a bit-vector stored through `addr` and read back":
    verdictS(sutIntAddrBV, "ab", sxSat, s8axTight)
    verdictS(sutIntAddrBV, "ab_dead", sxUnsat, s8axTight)
  test "an input cell holds a value of its type":
    ## RED: `c8_dead` sxSat (then a RangeDefect building the witness), and
    ## `cb` sxUnsat with nothing recorded.
    verdict(sutCellBranch, "cb", sxSat)
    verdict(sutCell8, "c8_dead", sxUnsat)
    verdict(sutCell8, "c8", sxSat)
    verdict(sutCellR, "cr_dead", sxUnsat)
    verdict(sutCellR, "cr", sxSat)

type S8axRR = ref object
  a: int

proc sutOrdArray(v: int) =
  var x = v
  proc g(): int =
    x = 10
    0
  let a = [x, g()]
  if a[0] == 1 and v == 1: symexTarget("ok")
  if a[0] == 10 and v == 1: symexTarget("bad")

proc sutOrdSeq(v: int) =
  var x = v
  proc g(): int =
    x = 10
    0
  let a = @[x, g()]
  if a[0] == 1 and v == 1: symexTarget("ok")
  if a[0] == 10 and v == 1: symexTarget("bad")

proc sutOrdTuple(v: int) =
  var x = v
  proc g(): int =
    x = 10
    0
  let a = (x, g())
  if a[0] == 1 and v == 1: symexTarget("ok")
  if a[0] == 10 and v == 1: symexTarget("bad")

suite "RFC-0005 S8ax (7): evaluation order":
  test "a constructor's element is read before a later element's call":
    clean(sutOrdArray, "ok", sxSat)
    clean(sutOrdArray, "bad", sxUnsat)
    clean(sutOrdSeq, "ok", sxSat)
    clean(sutOrdSeq, "bad", sxUnsat)
    clean(sutOrdTuple, "ok", sxSat)
    clean(sutOrdTuple, "bad", sxUnsat)

# ---- (8) `addr` of a routine's variable is an address cell ------------------
#
# DECLINES before S8ax: `addr x` anywhere but a `let p = addr x` the alias
# rewrite took, or a `ptr` actual of a call, was `feUnsupportedExprKind`
# (CR-2a, `nnkAddr`) or `heUnsafeCast` ("unsafe pointer materialisation"):
# a pointer stored in an object, returned, compared, re-pointed on one arm,
# kept by a callee, or into a seq element. `addr x` of a routine variable
# is now a `ptr` cell that holds `x` for the frame's lifetime, with `x` kept
# equal to it after every statement. A pointer that may outlive its frame
# declines where it is dereferenced or compared; a pointer into a seq
# declines where it is used after a statement that may resize the seq.
# Every verdict probed against the compiler.

type S8axPBox = object
  p: ptr int

type S8axPair = object
  a, b: int
