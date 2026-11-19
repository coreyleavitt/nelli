## RFC-0016 K2c -- the child-shape corpus, part c of 3 with
## `tsymex_0016_k2c_typeclass_a`, `_b` and `_c` (the original single suite
## ran 150.9 s on msvc, over the CI-D ceiling; INT-51). This part: the named-feature rows, the walker version floor and the by-value-formal site.
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

proc patomic(x: Atomic[int]) = symexTarget("hit")
proc powned(x: owned RefO) = symexTarget("hit")
proc pf128(x: c_longdouble) = (if x > 1.5: symexTarget("hit"))

var gInt = 1

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
  test "version floor: K2c bumped the walker to 298":
    check parseInt(symexWalkerVersion) >= 298

# E2 (W3-z): `cstring`, `pointer` and `proc` are modelled at the by-value-formal
# site (`typeCopiedByValue`): the formal is the caller's bytes, so a callee that
# overwrites the global it was handed a copy of does not change what it holds.
# The `cstring` and `proc` parameter sites decline (a `pointer` parameter is
# modelled since INT-83, pinned above); these pin the by-value site, where the
# walk's copy is Nim's and the verdict is exact against native. A `proc` value
# is a local (a global one is held by name and declines).
var
  gByCs: cstring
  gByPtr: ptr int

proc incByProc(a: int): int = a + 1

proc rewriteCs(c: cstring): bool =
  gByCs = "zz"
  c == "abc"
proc dropPtr(p: pointer): bool =
  gByPtr = nil
  true
proc callF(f: proc (a: int): int; x: int): bool = f(x) == 6

proc bvCs(x: int) =
  gByCs = (if x > 3: "abc" else: "x")
  if rewriteCs(gByCs) and x == 5: symexTarget("hit")
proc bvPtr(q: ptr int) =
  gByPtr = q
  let r = dropPtr(gByPtr)
  if r and gByPtr == nil: symexTarget("hit")
proc bvProc(x: int) =
  let f = incByProc
  if callF(f, x): symexTarget("hit")

suite "RFC-0016 W3-z E2: the by-value-formal site of cstring, pointer, proc":
  test "the leaf kinds are admitted at the by-value formal and decided":
    for k in [ntyCString, ntyPointer, ntyProc]:
      check admitTypeClass(k, tcByValueFormal).admitted
    discard pinExact(bvCs, cellKey(axTypeClass, "cstring"), domain = sampled([5, 2]))
    discard pinExact(bvPtr, cellKey(axTypeClass, "pointer"),
                     domain = sampled([cast[ptr int](nil), addr gInt]))
    discard pinExact(bvProc, cellKey(axTypeClass, "proc"), domain = sampled([5, 2]))
