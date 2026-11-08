## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder, item 2 (no set conversion; subrange checks).
##
## Item 2 was replaced; see the RFC's "As landed (S8bv)". Nim has no set
## conversion between two base domains -- every one is a type mismatch, and a
## literal is typed as its target, converting (and range-checking) each
## ELEMENT. The precision gap the probes found instead is an enum SUBRANGE
## (`range[a1..a2]`), which was unclassified: as a parameter, a local, a field
## and a set's base type it is the enum narrowed to its bounds, and Nim's range
## checks (assignment, conversion, argument, set element) raise `RangeDefect`.
## Split so each file stays under 60 s on Windows.
import std/[unittest, strutils, sets, macros]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc hasMsg(errs: seq[SymexErrorInfo]; k: SymexErrorKind; sub: string): bool =
  for e in errs:
    if e.kind == k and sub in e.msg: return true
  false

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

from ./s8cu_helpers import nativeHits

proc setConvNodes(n: NimNode): int =
  if n.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and
     n.getTypeInst.typeKind == ntySet:
    inc result
  for c in n: result += setConvNodes(c)

macro setConvCount(n: typed): int =
  ## The set-typed conversion nodes in `n`'s typed AST.
  newLit(setConvNodes(n))

macro curlyTypes(n: typed): string =
  ## The type of every `{..}` in `n`'s typed AST.
  var acc: seq[string]
  proc walk(x: NimNode) =
    if x.kind == nnkCurly: acc.add x.getTypeInst.repr
    for c in x: walk(c)
  walk(n)
  newLit(acc.join(";"))

proc takeRJ(s: set[RJ]): int = card(s)
proc takeSE(s: set[SE]): int = card(s)
proc takeE(s: set[E4]): int = card(s)

proc subParam(x: SE) =
  if ord(x) == 0 or ord(x) == 3: symexTarget("bv_sub_param_out")
  if x == e2: symexTarget("bv_sub_param")

proc subAssign(e: E4) =
  var x: SE = e1
  try:
    x = e
  except RangeDefect:
    if e == e3: symexTarget("bv_sub_assign_raise")
    if e == e1 or e == e2: symexTarget("bv_sub_assign_bad")
  if ord(x) == 0: symexTarget("bv_sub_assign_out")

proc subConv(e: E4) =
  try:
    let x = SE(e)
    if x == e2: symexTarget("bv_sub_conv")
  except RangeDefect:
    if e == e0: symexTarget("bv_sub_conv_raise")
    if e == e2: symexTarget("bv_sub_conv_bad")

proc subArg(e: E4) =
  try:
    subParam(e)
    if e == e1: symexTarget("bv_sub_arg")
  except RangeDefect:
    if e == e3: symexTarget("bv_sub_arg_raise")
    if e == e1: symexTarget("bv_sub_arg_bad")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 250

suite "S8bv (2): no set conversion between domains":
  test "Nim rejects every conversion between two set domains":
    var r: set[range[0'i8..3'i8]]
    var s8: set[int8]
    var rc: set[RC]
    var cs: set[char]
    var es: set[SE]
    var ef: set[E4]
    var ri: set[RI]
    check not compiles(set[int8](r))
    check not compiles(set[range[0'i8..3'i8]](s8))
    check not compiles(set[char](rc))
    check not compiles(set[uint8](cs))
    check not compiles(set[E4](es))
    check not compiles(set[SE](ef))
    check not compiles(set[RJ](ri))
    check not compiles(takeRJ(ri))
    check not compiles(takeE(es))
    check not compiles((ef = es))
    check not compiles(ef + es)
  test "a literal is typed as its target; only elements convert":
    var x: RI = 3
    var se: SE = e1
    check setConvCount(takeRJ({x, 4})) == 0
    check setConvCount(takeE({se})) == 0
    check setConvCount((var w: set[RI] = {1, 2}; w)) == 0
    check curlyTypes(takeRJ({x, 4})) == "set[RJ]"
    check curlyTypes(takeE({se})) == "set[E4]"
    check curlyTypes(takeSE({e1})) == "set[SE]"
  test "natively, a set literal's element is range-checked":
    var e = e3
    expect RangeDefect:
      discard takeSE({e1, e})

suite "S8bv (2): enum subranges":
  test "a subrange parameter":
    check verdict(subParam, "bv_sub_param_out").status == sxUnsat
    let r = verdict(subParam, "bv_sub_param")
    check r.status == sxSat
    check r.errors.len == 0
    check $r.witness == "(e2,)"
    check "bv_sub_param" in nativeHits(subParam(e2))
  test "assigning the enum to a subrange local is range-checked":
    check verdict(subAssign, "bv_sub_assign_raise").status == sxSat
    check verdict(subAssign, "bv_sub_assign_bad").status == sxUnsat
    check verdict(subAssign, "bv_sub_assign_out").status == sxUnsat
    check "bv_sub_assign_raise" in nativeHits(subAssign(e3))
  test "a conversion to the subrange is range-checked":
    check verdict(subConv, "bv_sub_conv").status == sxSat
    check verdict(subConv, "bv_sub_conv_raise").status == sxSat
    check verdict(subConv, "bv_sub_conv_bad").status == sxUnsat
    check "bv_sub_conv_raise" in nativeHits(subConv(e0))
  test "an enum argument to a subrange parameter is range-checked":
    check verdict(subArg, "bv_sub_arg").status == sxSat
    check verdict(subArg, "bv_sub_arg_raise").status == sxSat
    check verdict(subArg, "bv_sub_arg_bad").status == sxUnsat
    check "bv_sub_arg_raise" in nativeHits(subArg(e3))
