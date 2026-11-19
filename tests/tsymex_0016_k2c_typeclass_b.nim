## RFC-0016 K2c -- the child-shape corpus, part b of 3 with
## `tsymex_0016_k2c_typeclass_a`, `_b` and `_c` (the original single suite
## ran 150.9 s on msvc, over the CI-D ceiling; INT-51). This part: the pointer and view kinds.
## The parameter types are shared (`s0016_k2c_fixtures`).
##
## One snippet per `NimTypeKind` a Nim source can write as a parameter type,
## run through `symexFind`, and the named-feature rows of the type-class axis
## (`owned`, `Atomic`, `c_longdouble`). A modelled kind is pinned exact against
## native; a refused kind is pinned to the decline its row names. The
## omitted-variant-field rows and `array/enumIndex` are pinned in
## tsymex_0016_k20_probes{,_child}.
import std/[unittest, os, strutils, atomics, macros]
import nelli
import nelli/symex
import nelli/smt/typeaxes
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/canonicalize
import ./s8cu_helpers
import ./s0016_k2c_fixtures

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("k2c_pins_" & $getCurrentProcessId()))

proc pcstr(x: cstring) = (if x != nil: symexTarget("hit"))
proc ppointer(x: pointer) = (if x != nil: symexTarget("hit"))
proc pptr(x: ptr int) = (if x != nil: symexTarget("hit"))
proc popenarr(x: openArray[int]) = (if x.len == 2: symexTarget("hit"))
proc pvarargs(x: varargs[int]) = (if x.len == 2: symexTarget("hit"))
proc punchecked(x: UncheckedArray[int]) = symexTarget("hit")
proc pvarCallee(x: var int) = (if x == 3: symexTarget("hit"))
proc pvar(x: int) =
  ## pinExact's native call cannot pass a `var` argument, so the `var`
  ## parameter is the callee's: the walker classifies its formal.
  var y = x
  pvarCallee(y)

type
  UcObj = object       ## a flexible array member: Nim cannot hold one in a tuple
    n: int
    data: UncheckedArray[int]
  PtrObj = object
    n: int
    p: pointer
proc pucobj(x: UcObj) = (if x.n == 2: symexTarget("hit"))
proc pptruc(x: ptr UncheckedArray[int]) = (if x != nil: symexTarget("hit"))
proc pptrobj(x: PtrObj) = (if x.n == 2: symexTarget("hit"))

var gInt = 1

proc psplit(s: string) =
  if s.len > 2: return
  var n = 0
  for l in s.splitLines: inc n
  if n == 2: symexTarget("hit")

proc gen[T](x: seq[T]): int =
  var y = x
  y.add(x[0])
  result = y.len
proc pgen(x: seq[int]) =
  if x.len > 0 and gen(x) == 3: symexTarget("hit")
proc gen2[T](x: T) =
  if x.len == 2: symexTarget("hit")
proc pgen2(x: seq[int]) = gen2(x)

suite "RFC-0016 K2c: the pointer and view kinds":
  test "ptr, pointer, openArray and var are classified, varargs and UncheckedArray are not":
    for k in [ntyPtr, ntyPointer, ntyOpenArray, ntyVar]:
      check admitTypeClass(k, tcClassify).admitted
    for k in [ntyVarargs, ntyUncheckedArray]:
      check not admitTypeClass(k, tcClassify).admitted

  test "ptr, openArray and var parameters are modelled":
    discard pinExact(pptr, cellKey(axTypeClass, "ptr"),
                     domain = sampled([cast[ptr int](nil), addr gInt]))
    discard pinExact(popenarr, cellKey(axTypeClass, "openArray"),
                     domain = sampled([@[1, 2], @[], @[1]]))
    discard pinExact(pvar, cellKey(axTypeClass, "var"), domain = sampled([3, 0]))

  test "a pointer parameter is modelled (RFC-0016 INT-83), pinned on its witness":
    let r = pinFind(ppointer, tLabel("hit"))
    checkpoint $r.errors
    check r.status == sxSat
    check r.trusted

  test "a cstring parameter is modelled (RFC-0016 INT-87), pinned on its witness":
    check admitTypeClass(ntyCString, tcClassify).admitted
    let r = pinFind(pcstr, tLabel("hit"))
    checkpoint $r.errors
    check r.status == sxSat
    check r.trusted

  test "varargs and UncheckedArray parameters decline with their row's kind":
    pinDecline(pvarargs, cellKey(axTypeClass, "varargs"), feUnsupportedParamType)
    pinDecline(punchecked, cellKey(axTypeClass, "uncheckedArray"), feUnsupportedParamType)

  test "a ptr to an UncheckedArray is still a modelled ptr (the demotion is for a value)":
    let r = symexFind(pptruc, tLabel("hit"), pinSettingsConst)
    check r.status == sxSat
    check r.trusted

  test "CRH-01 (HRV-44): a generic proc using .len/.add/index on its generic param runs":
    check symexFind(pgen, tLabel("hit"), pinSettingsConst).trusted
    check symexFind(pgen2, tLabel("hit"), pinSettingsConst).trusted

  test "CRH-01 (INT-09): splitLines over a bounded string was a compile stop, now declines":
    # the formal `keepEol = false` has an empty type slot in the iterator's
    # impl; its type comes from the signature. An UNBOUNDED string does not
    # terminate (a loop-cap matter, K7), so the input is bounded.
    pinDecline(psplit, cellKey(axTypeClass, "string"), seUnsupportedStringOp)

  test "CRH-01: a pointer field is modelled (RFC-0016 INT-83), pinned on its witness":
    # It declined (`feUnsupportedParamType`) until INT-83; before CRH-01 the
    # witness reader gave the `int` placeholder to a `pointer` slot.
    let r = pinFind(pptrobj, tLabel("hit"))
    checkpoint $r.errors
    check r.status == sxSat
    check r.trusted

  test "CRH-01: an UncheckedArray field was a compile stop, now declines":
    # a witness tuple cannot hold one.
    pinDecline(pucobj, cellKey(axTypeClass, "uncheckedArray"), feUnsupportedWitnessType)
