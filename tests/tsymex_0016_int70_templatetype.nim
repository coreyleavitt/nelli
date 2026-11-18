## RFC-0016 INT-70: a type section in a template a routine declares. The
## template's body is not semchecked where it is defined, so the type symbol
## its `type` section declares has no type: the route scan (`routeScan`'s
## `nskType` arm, then `routeType`'s `getTypeImpl`) stopped the compile with
## "node has no type" (`dsl_typebridge.viewTypeImpl`), for any pragma on the
## type or none. The expanded copy of the body carries the typed symbol, which
## the scan reads where the template is called.
##
## Red at 2206eb51: this file does not compile. Found by K8b's pragma axis
## suite (INT-56): `pragma_e`'s `twTemplate` relation wrapped the then-local
## `type/dynlib` and `type/nosinks` fragments (a type section in the routine)
## in a template. Each fragment alone only declined: a type section in a
## routine is `feUnsupportedStmtKind`, which is unchanged.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8b_pragmas

proc i70Plain(a, b: int8) =
  let t = int(a)
  template w() =
    var acc = 0
    type V_O = object
      x: int
    acc = acc + V_O(x: t).x
    if acc == 5: symexTarget("hit")
  w()

proc i70Pragma(a, b: int8) =
  let t = int(a)
  template w() =
    var acc = 0
    template mine() {.pragma.}
    type V_O {.mine.} = object
      x: int
    acc = acc + V_O(x: t).x
    if acc == 5: symexTarget("hit")
  w()

proc i70N_h(x: int): int = x + 1

proc i70ProcTy(a, b: int8) =
  let t = int(a)
  template w() =
    var acc = 0
    type V_P = proc (x: int): int {.nimcall.}
    acc = acc + (let p: V_P = i70N_h; p(t))
    if acc == 5: symexTarget("hit")
  w()

proc i70Generic(a, b: int8) =
  let t = int(a)
  template w() =
    var acc = 0
    type V_G[T] = object
      x: T
    acc = acc + V_G[int](x: t).x
    if acc == 5: symexTarget("hit")
  w()

# the K8b fragments' shape since 2206eb51: the type at top level, read in a
# template (`twTemplate`)
proc i70TopDyn(a, b: int8) =
  let t = int(a)
  template w() =
    var acc = 0
    acc = acc + K8bDynO(x: t).x
    if acc == 5: symexTarget("hit")
  w()

proc i70TopSinks(a, b: int8) =
  let t = int(a)
  template w() =
    var acc = 0
    acc = acc + (let p: K8bNoSinksP = i70N_h; p(t))
    if acc == 5: symexTarget("hit")
  w()

proc declinesCleanly(r: SymexResult) =
  checkpoint $r.status & " trusted=" & $r.trusted & " errors " & show(r.errors)
  check not r.trusted
  check r.errors.named(feUnsupportedStmtKind)
  check not r.errors.anyIt(it.kind == weInternalWalkerFault)

suite "INT-70: a type section in a routine's template compiles and declines":
  test "an object type, no pragma":
    declinesCleanly(symexFind(i70Plain, tLabel("hit"), pinSettingsConst))
  test "an object type with a custom pragma":
    declinesCleanly(symexFind(i70Pragma, tLabel("hit"), pinSettingsConst))
  test "a proc type":
    declinesCleanly(symexFind(i70ProcTy, tLabel("hit"), pinSettingsConst))
  test "a generic object type":
    declinesCleanly(symexFind(i70Generic, tLabel("hit"), pinSettingsConst))

suite "INT-70: the K8b fragments under a template are exact":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "`type/dynlib`: a field of a top-level `{.dynlib.}` object (sat)":
    let r = pinExact(i70TopDyn, cellKey(axPragma, "type/dynlib"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "`type/nosinks`: a call through a `{.nosinks.}` proc type (sat)":
    let r = pinExact(i70TopSinks, cellKey(axPragma, "type/nosinks"),
                     tLabel("hit"), all)
    check r.status == sxSat
