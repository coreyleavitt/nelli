## RFC-0005 (soundness channels) slice S8ba -- S8au's remainder.
##
## Pinned here (the RFC's "As landed (S8ba)" note has the design and the
## measurements):
##   (1) a declined seq read left its compiler temporary (`__sym_idx_N`)
##       unbound, and the next read of it was recorded as an unmodelled
##       global (`feGlobalReadUnmodelled`). Every declining arm that owns a
##       result now binds it; a parser temporary read unbound is a walker
##       fault, never a global; a global write next to a temporary is
##       still seen;
##   (2) a `seq` of a distinct type is modelled: the backing array holds
##       the base sort, and an element is re-boxed on every read;
##   (3) every string / seq leaf has `len <= high(int)` (Nim's `len` is a
##       non-negative `int`), so an overflow or range raise path over a
##       string-derived index decides, in both integer encodings;
##   (4) a `var` / `addr` actual whose heap cell the callee can also reach
##       through a global or a capture is passed by reference through that
##       cell (S8au declined it): S8au's five dead labels are `sxUnsat`;
##   (5) a split's axioms are built once, by the first query that reaches
##       it, newly reached splits in lowering order and before any chain or
##       link fact; later queries reuse them. S8ag's B1-1 probe is the
##       canary (a unit ceiling, both Z3 versions).
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8ba_remainder_b`, `tsymex_rfc0005_s8ba_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 76 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

# ---- (1) a compiler temporary is not a global ---------------------------------

type Pair = (int, string)

proc tupSeqIdx(x: int) =
  ## `seq[(int, string)]` is not backed (a scoped decline); the element
  ## read binds the temporary `__sym_idx_N` the comparison then reads.
  var s: seq[Pair] = @[(1, "a")]
  if s[0][0] == x: symexTarget("ti")

proc tupSeqPop(x: int) =
  var s: seq[Pair] = @[(1, "a")]
  let v = s.pop()
  if v[0] == x: symexTarget("tp")

var gW: int

proc storeElem(s: seq[int]) =
  gW = s[0]

proc tempThenGlobal(x: int) =
  ## A value read into a temporary and written to a global by a callee:
  ## the global write is carried back to the caller.
  gW = 0
  storeElem(@[x, 2])
  if gW == 3 and x == 3: symexTarget("tg")
  if gW != x: symexTarget("tg_dead")

suite "S8ba (1): a compiler temporary is never read as a global":

  test "a declined element read binds its temporary":
    template one(fn: typed, lbl: string) =
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.errors.hasKind(feGlobalReadUnmodelled)
      check not r.errors.hasKind(weInternalWalkerFault)
      check "__sym_" notin show(r.errors)
    one(tupSeqIdx, "ti")
    one(tupSeqPop, "tp")

  test "a temporary is not a global name":
    check not isGlobalEnvName("__sym_idx_2")
    check isGlobalEnvName(globalEnvPrefix & "m.gW")

  test "a global written from a temporary is seen by the caller":
    discard clean(tempThenGlobal, "tg", sxSat)
    discard clean(tempThenGlobal, "tg_dead", sxUnsat)

  test "every declining arm that owns a result binds it":
    ## Source audit: inside the walker's `isIndex` and `isSeqPop` arms a
    ## tainted fork never keeps the unbound env (`p.env`): the result is
    ## bound (`declinedIndexEnv` / `declinedResultEnv`).
    const src = staticRead("../src/nelli/smt/runtime.nim")
    var arm = ""
    var bad: seq[string]
    for ln in src.splitLines:
      if ln.startsWith("  of is") and ln.endsWith(":"): arm = ln.strip
      if arm in ["of isIndex:", "of isSeqPop:"] and
         "forkPathTainted(p, p.pc, p.env," in ln:
        bad.add arm & " " & ln.strip
    checkpoint bad.join("\n")
    check bad.len == 0

# ---- (2) a seq of a distinct type --------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

proc dSeq(x: int) =
  symexAssume(x > -100 and x < 100)   # no overflow path in `+`
  var s = @[Meters(1)]
  s.add(s[0] + Meters(x))
  if s[1] == Meters(3): symexTarget("sq")
  if s[1] == Meters(3) and x != 2: symexTarget("sq_dead")

proc dSeqAssign(x: int) =
  var s = @[Meters(1), Meters(2)]
  s[1] = Meters(x)
  if s.len == 2 and s[1] < s[0]: symexTarget("sa")
  if s[1] < s[0] and x >= 1: symexTarget("sa_dead")

proc dSeqPop(x: int) =
  var s = @[Meters(x)]
  s.add Meters(7)
  let a = s.pop()
  let b = s.pop()
  if a == Meters(7) and b == Meters(4): symexTarget("sp")
  if b != Meters(x) or s.len != 0: symexTarget("sp_dead")

proc dSeqLoop(x: int) =
  symexAssume(x > -100 and x < 100)
  var s = @[Meters(x), Meters(2)]
  var t = Meters(0)
  for m in s: t = t + m
  if t == Meters(5): symexTarget("sl")
  if t == Meters(5) and x != 3: symexTarget("sl_dead")

proc addRange(x: range[0..10]) =
  ## `.add` stored an `svInt` value (a `range` param under `isOptimised`)
  ## as the constant 0: a false `sxUnsat`.
  var s: seq[int] = @[]
  s.add(x)
  if s[0] == 7: symexTarget("ar")
  if s[0] != x: symexTarget("ar_dead")

proc add32(x: int32) =
  var s: seq[int32] = @[]
  s.add(x)
  s.add(5'i32)
  if s[0] == 7 and s[1] == 5: symexTarget("a32")
  if s[0] != x: symexTarget("a32_dead")

proc addStr(x: string) =
  var s: seq[string] = @[]
  s.add(x)
  if s[0] == "ab": symexTarget("as")

proc addF(x: float) =
  var s: seq[float] = @[]
  s.add(x)
  if s[0] == 1.5: symexTarget("af")

type Mod10 = distinct int
proc `==`(a, b: Mod10): bool = int(a) mod 10 == int(b) mod 10
  ## A USER `==` (not borrowed): equality modulo 10. A builtin model that
  ## compares a seq's cells by their base values would contradict it.

proc uIn(k: int) =
  let s = @[Mod10(3)]
  if k == 13 and Mod10(k) in s: symexTarget("uin")
  if Mod10(k) in s and k mod 10 != 3: symexTarget("uin_dead")

proc uFind(k: int) =
  let s = @[Mod10(1), Mod10(3)]
  if k == 23 and s.find(Mod10(k)) == 1: symexTarget("ufind")

proc uEq(k: int) =
  let a = @[Mod10(k)]
  let b = @[Mod10(3)]
  if k == 13 and a == b: symexTarget("ueq")

proc dParam(s: seq[Meters]) =
  if s.len > 0 and s[0] == Meters(3): symexTarget("dp")

suite "S8ba (2): a seq of a distinct type is modelled":

  test "a user `==` over the cells is never replaced by base equality":
    for (st, lbl) in [(symexFind(uIn, tLabel("uin")).status, "uin"),
                      (symexFind(uFind, tLabel("ufind")).status, "ufind"),
                      (symexFind(uEq, tLabel("ueq")).status, "ueq")]:
      checkpoint lbl & " " & $st
      check st != sxUnsat
    let d = symexFind(uIn, tLabel("uin_dead"))
    checkpoint "uin_dead " & $d.status & " " & show(d.errors)
    check d.status != sxSat

  test "add and index read":
    let r = clean(dSeq, "sq", sxSat)
    if r.status == sxSat: check r.witness[0] == 2
    discard clean(dSeq, "sq_dead", sxUnsat)

  test "index assignment":
    let r = clean(dSeqAssign, "sa", sxSat)
    if r.status == sxSat: check r.witness[0] < 1
    discard clean(dSeqAssign, "sa_dead", sxUnsat)

  test "pop":
    let r = clean(dSeqPop, "sp", sxSat)
    if r.status == sxSat: check r.witness[0] == 4
    discard clean(dSeqPop, "sp_dead", sxUnsat)

  test "a loop over the seq":
    let r = clean(dSeqLoop, "sl", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard clean(dSeqLoop, "sl_dead", sxUnsat)

  test "`.add` stores every backed element kind (was int64 / bool only)":
    let r = clean(addRange, "ar", sxSat)
    if r.status == sxSat: check r.witness[0] == 7
    discard clean(addRange, "ar_dead", sxUnsat)
    discard clean(add32, "a32", sxSat)
    discard clean(add32, "a32_dead", sxUnsat)
    discard clean(addStr, "as", sxSat)
    discard clean(addF, "af", sxSat)

  test "a seq[distinct] parameter has a witness (RFC-0005 S8bd)":
    ## S8ba pinned this as a scoped `feUnsupportedWitnessType` decline;
    ## S8bd renders it (`tsymex_rfc0005_s8bd_remainder.nim`).
    let r = symexFind(dParam, tLabel("dp"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.errors.len == 0

  test "nim":
    var s = @[Meters(1)]
    s.add(s[0] + Meters(2))
    check s[1] == Meters(3)

# ---- (4) by reference through a heap cell --------------------------------------

type Box = ref object
  x: int
