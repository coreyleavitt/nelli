## RFC-0016 K2c -- the child-shape corpus: one snippet per `NimTypeKind` a
## Nim source can write as a parameter type, run through `symexFind`, and the
## named-feature rows of the type-class axis (`owned`, `Atomic`, `c_longdouble`)
## that `classifyType` now reads through `admitTypeClass`/`admitTypeFeature`.
##
## A modelled kind is pinned exact against native; a refused kind is pinned to
## the decline its row names. The omitted-variant-field rows and
## `array/enumIndex` are pinned in tsymex_0016_k20_probes{,_child}.
import std/[unittest, os, strutils, atomics, macros]
import nelli
import nelli/symex
import nelli/smt/typeaxes
import nelli/smt/types
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/canonicalize
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("k2c_pins_" & $getCurrentProcessId()))

type
  E = enum ea, eb, ec
  Obj = object
    a: int
    b: bool
  Dist = distinct int
  RefO = ref object
    v: int
  Box[T] = object
    v: T
  Al = int

proc `$`(d: Dist): string = $int(d)
proc `$`(r: RefO): string = (if r == nil: "nil" else: $r.v)

proc pint(x: int) = (if x == 3: symexTarget("hit"))
proc pint8(x: int8) = (if x == 3: symexTarget("hit"))
proc pint16(x: int16) = (if x == 3: symexTarget("hit"))
proc pint32(x: int32) = (if x == 3: symexTarget("hit"))
proc pint64(x: int64) = (if x == 3: symexTarget("hit"))
proc puint(x: uint) = (if x == 3: symexTarget("hit"))
proc puint8(x: uint8) = (if x == 3: symexTarget("hit"))
proc puint16(x: uint16) = (if x == 3: symexTarget("hit"))
proc puint32(x: uint32) = (if x == 3: symexTarget("hit"))
proc puint64(x: uint64) = (if x == 3: symexTarget("hit"))
proc pfloat(x: float) = (if x > 1.5: symexTarget("hit"))
proc pfloat32(x: float32) = (if x > 1.5'f32: symexTarget("hit"))
proc pfloat64(x: float64) = (if x > 1.5'f64: symexTarget("hit"))
proc pbool(x: bool) = (if x: symexTarget("hit"))
proc pchar(x: char) = (if x == 'a': symexTarget("hit"))
proc pstr(x: string) = (if x == "ab": symexTarget("hit"))
proc pcstr(x: cstring) = (if x != nil: symexTarget("hit"))
proc penum(x: E) = (if x == eb: symexTarget("hit"))
proc prange(x: range[1..5]) = (if x == 3: symexTarget("hit"))
proc pseq(x: seq[int]) = (if x.len == 2: symexTarget("hit"))
proc parr(x: array[3, int]) = (if x[1] == 2: symexTarget("hit"))
proc pset(x: set[E]) = (if eb in x: symexTarget("hit"))
proc ptup(x: (int, bool)) = (if x[0] == 2: symexTarget("hit"))
proc pobj(x: Obj) = (if x.a == 2: symexTarget("hit"))
proc pdist(x: Dist) = (if int(x) == 2: symexTarget("hit"))
proc pref(x: RefO) = (if x != nil and x.v == 2: symexTarget("hit"))
proc pproc(x: proc (a: int): int) = (if x != nil: symexTarget("hit"))
proc palias(x: Al) = (if x == 3: symexTarget("hit"))
proc pgeneric(x: Box[int]) = (if x.v == 3: symexTarget("hit"))
proc patomic(x: Atomic[int]) = symexTarget("hit")
proc powned(x: owned RefO) = symexTarget("hit")
proc pf128(x: c_longdouble) = (if x > 1.5: symexTarget("hit"))

const rangeVals: array[3, range[1..5]] = [3, 1, 5]

suite "RFC-0016 K2c: one snippet per NimTypeKind":
  test "scalar kinds are modelled":
    discard pinExact(pint, cellKey(axTypeClass, "int"), domain = sampled([3, 0]))
    discard pinExact(pint8, cellKey(axTypeClass, "int8"), domain = sampled([3'i8, 0]))
    discard pinExact(pint16, cellKey(axTypeClass, "int16"), domain = sampled([3'i16, 0]))
    discard pinExact(pint32, cellKey(axTypeClass, "int32"), domain = sampled([3'i32, 0]))
    discard pinExact(pint64, cellKey(axTypeClass, "int64"), domain = sampled([3'i64, 0]))
    discard pinExact(puint, cellKey(axTypeClass, "uint"), domain = sampled([3'u, 0]))
    discard pinExact(puint8, cellKey(axTypeClass, "uint8"), domain = sampled([3'u8, 0]))
    discard pinExact(puint16, cellKey(axTypeClass, "uint16"), domain = sampled([3'u16, 0]))
    discard pinExact(puint32, cellKey(axTypeClass, "uint32"), domain = sampled([3'u32, 0]))
    discard pinExact(puint64, cellKey(axTypeClass, "uint64"), domain = sampled([3'u64, 0]))
    discard pinExact(pfloat, cellKey(axTypeClass, "float"), domain = sampled([2.0, 0.0]))
    discard pinExact(pfloat32, cellKey(axTypeClass, "float32"), domain = sampled([2.0'f32, 0.0]))
    discard pinExact(pfloat64, cellKey(axTypeClass, "float64"), domain = sampled([2.0'f64, 0.0]))
    discard pinExact(pbool, cellKey(axTypeClass, "bool"), domain = sampled([true, false]))
    discard pinExact(pchar, cellKey(axTypeClass, "char"), domain = sampled(['a', 'b']))
    discard pinExact(penum, cellKey(axTypeClass, "enum"), domain = sampled([ea, eb, ec]))
    discard pinExact(prange, cellKey(axTypeClass, "range"), domain = sampled(rangeVals))
    discard pinExact(palias, cellKey(axTypeClass, "alias"), domain = sampled([3, 0]))

  test "aggregate and container kinds are modelled":
    discard pinExact(pstr, cellKey(axTypeClass, "string"), domain = sampled(["ab", "", "abc"]))
    discard pinExact(pseq, cellKey(axTypeClass, "sequence"), domain = sampled([@[1, 2], @[], @[1]]))
    discard pinExact(parr, cellKey(axTypeClass, "array"), domain = sampled([[0, 2, 0], [0, 0, 0]]))
    discard pinExact(pset, cellKey(axTypeClass, "set"), domain = sampled([{eb}, {ea}, {}]))
    discard pinExact(ptup, cellKey(axTypeClass, "tuple"), domain = sampled([(2, true), (0, false)]))
    discard pinExact(pobj, cellKey(axTypeClass, "object"), domain = sampled([Obj(a: 2), Obj()]))
    discard pinExact(pdist, cellKey(axTypeClass, "distinct"), domain = sampled([Dist(2), Dist(0)]))
    discard pinExact(pref, cellKey(axTypeClass, "ref"), domain = sampled([RefO(v: 2), RefO(v: 0), nil]))
    discard pinExact(pgeneric, cellKey(axTypeClass, "genericInst"),
                     domain = sampled([Box[int](v: 3), Box[int]()]))

  test "refused kinds decline with the kind their row names":
    for k in [ntyCString, ntyProc]:
      check not admitTypeClass(k, tcClassify).admitted
    pinDecline(pcstr, cellKey(axTypeClass, "cstring"), feUnsupportedParamType)
    pinDecline(pproc, cellKey(axTypeClass, "proc"), ceUnsupportedHof)

  test "classified kinds are the table's tcClassify rows":
    for k in [ntyInt, ntyString, ntySequence, ntyTuple, ntyObject, ntyDistinct]:
      check admitTypeClass(k, tcClassify).admitted
    check not admitTypeClass(ntyForward, tcClassify).admitted

suite "RFC-0016 K2c: classifyType reads the named-feature rows":
  test "STY-04: Atomic[T] and owned T decline (heUnsupportedOwnership), not a compile stop":
    check not admitTypeFeature("atomic").admitted
    check not admitTypeFeature("owned").admitted
    pinDecline(patomic, cellKey(axTypeClass, "atomic"), heUnsupportedOwnership)
    pinDecline(powned, cellKey(axTypeClass, "owned"), heUnsupportedOwnership)

  test "STY-06: c_longdouble is float128, refused by its row, so it declines":
    check not admitTypeClass(ntyFloat128, tcClassify).admitted
    pinDecline(pf128, cellKey(axTypeClass, "float128"), feUnsupportedParamType)

suite "RFC-0016 K2c: walker version":
  test "version floor: K2c bumped the walker to 292":
    check parseInt(symexWalkerVersion) >= 292
