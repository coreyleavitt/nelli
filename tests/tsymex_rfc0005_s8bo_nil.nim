## RFC-0005 (soundness channels) slice S8bo -- S8be's remainder: the
## bodiless `isNil` magic and its kin on pointer-like values.
##
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
import std/[unittest, strutils]
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

template declines(fn: typed, tgt: SymexTarget, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

template verdict(fn: typed, tgt: SymexTarget, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (1) `isNil` -------------------------------------------------------------
#
# WRONG VERDICT before S8bo: `r.isNil` over a `ref` parameter was a false
# `sxUnsat` with `errors` empty, where `r == nil` was `sxSat`: the
# bodiless `isNil` magic was walked as a constant.

type S8boObj = ref object
  v: int

proc sutNilRefObj(r: S8boObj) =
  if r.isNil: symexTarget("nil")
  if not r.isNil: symexTarget("some")

proc sutNilRefInt(r: ref int) =
  if r.isNil: symexTarget("nil")
  if not isNil(r): symexTarget("some")

proc sutNilRefEq(r: ref int) =
  if r == nil: symexTarget("nil")

proc sutNilPtr(p: ptr int) =
  if p.isNil: symexTarget("nil")
  if not p.isNil: symexTarget("some")

proc sutNilLocal(v: int) =
  var r: ref int
  if v > 0: r = new int
  if r.isNil and v == 0: symexTarget("nil")
  if r.isNil and v == 3: symexTarget("dead")

type S8boNode = ref object
  next: S8boNode
  v: int

proc sutNilField(n: S8boNode) =
  symexAssume(not n.isNil)
  if n.next.isNil: symexTarget("nil")
  if not n.next.isNil: symexTarget("some")

# A proc value against nil is not modelled (S8z): `isNil` declines exactly
# as `== nil` does, never a constant.
proc sutNilProc(f: proc(x: int): int {.closure.}) =
  if f.isNil: symexTarget("nil")

# ---- (1) a conversion or cast to `pointer` -----------------------------------
#
# CRASH before S8bo: `pointer(p) == nil` over a `ptr int` was a
# `weInternalWalkerFault` ("coerceIntLit: composite prototype"), and
# `cast[pointer](r) == nil` declined (`feUnsupportedExprKind`). Neither
# changes the address: each is nil exactly when the operand is.

proc sutConvPtr(p: ptr int) =
  if pointer(p) == nil: symexTarget("nil")

proc sutCastRef(r: ref int) =
  if cast[pointer](r) == nil: symexTarget("nil")
  if not isNil(cast[pointer](r)): symexTarget("some")

# ---- (1) the guard: an unlowered magic is never a constant -------------------
#
# WRONG VERDICT before S8bo: `ashr` is a `{.magic.}` whose body is only its
# doc comment, walked as an empty body returning 0, so `ashr(-1, 1) == -1`
# was a false `sxUnsat` with `errors` empty (Nim: -1). CRASH before S8bo:
# `wasMoved(x)` and `move(x)` failed the whole compile in the parser.

proc sutAshr(v: int) =
  if ashr(v, 1) == -1 and v == -1: symexTarget("a")

proc sutSwap(v: int) =
  var a = v
  var b = 3
  swap(a, b)
  if a == 3 and v == 1: symexTarget("a")

proc sutWasMoved(v: int) =
  var x = v
  wasMoved(x)
  if x == 0 and v == 1: symexTarget("a")

suite "RFC-0005 S8bo: walker version":
  test "symexWalkerVersion is at least 216":
    check parseInt(symexWalkerVersion) >= 216

suite "RFC-0005 S8bo (1): `isNil` is the nil comparison":
  test "a ref object parameter":
    verdict(sutNilRefObj, tLabel("nil"), sxSat)
    verdict(sutNilRefObj, tLabel("some"), sxSat)
  test "a ref int parameter":
    verdict(sutNilRefInt, tLabel("nil"), sxSat)
    verdict(sutNilRefInt, tLabel("some"), sxSat)
  test "`== nil` agrees":
    verdict(sutNilRefEq, tLabel("nil"), sxSat)
  test "a ptr parameter":
    verdict(sutNilPtr, tLabel("nil"), sxSat)
    verdict(sutNilPtr, tLabel("some"), sxSat)
  test "a local ref":
    verdict(sutNilLocal, tLabel("nil"), sxSat)
    verdict(sutNilLocal, tLabel("dead"), sxUnsat)
  test "a ref field":
    verdict(sutNilField, tLabel("nil"), sxSat)
    verdict(sutNilField, tLabel("some"), sxSat)
  test "a proc value declines as `== nil` does":
    declines(sutNilProc, tLabel("nil"), ceUnsupportedHof, "compared with nil")

suite "RFC-0005 S8bo (1): a conversion or cast to `pointer`":
  test "`pointer(p) == nil`":
    verdict(sutConvPtr, tLabel("nil"), sxSat)
  test "`cast[pointer](r)` against nil":
    verdict(sutCastRef, tLabel("nil"), sxSat)
    verdict(sutCastRef, tLabel("some"), sxSat)

suite "RFC-0005 S8bo (1): an unlowered magic declines":
  test "a value magic with a doc-only body":
    declines(sutAshr, tLabel("a"), feUnsupportedOp, "compiler magic `ashr`")
  test "a statement magic":
    declines(sutSwap, tLabel("a"), feUnsupportedOp, "compiler magic `swap`")
  test "a compiler-generated hook compiles and declines":
    declines(sutWasMoved, tLabel("a"), feUnsupportedOp, "`=wasMoved`")
