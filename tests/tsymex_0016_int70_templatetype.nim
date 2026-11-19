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
## routine was `feUnsupportedStmtKind`.
##
## RFC-0016 S8cp-r (PRC-34, walker 391) walks a type section in a routine
## body as a no-op (the typed body reads its types through their symbols),
## so the four shapes below now decide; each is pinned exact against the
## native run over its whole `int8` domain.
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

template typeSectionDecides(fn: untyped; a: int) =
  let r = pinFind(fn, tLabel("hit"))
  checkpoint $r.status & " trusted=" & $r.trusted & " errors " & show(r.errors)
  check r.status == sxSat
  check r.trusted
  check int(r.witness[0]) == a
  check not r.errors.anyIt(it.kind == weInternalWalkerFault)

suite "INT-70: a type section in a routine's template compiles and decides":
  test "an object type, no pragma":
    typeSectionDecides(i70Plain, 5)
  test "an object type with a custom pragma":
    typeSectionDecides(i70Pragma, 5)
  test "a proc type":
    typeSectionDecides(i70ProcTy, 4)
  test "a generic object type":
    typeSectionDecides(i70Generic, 5)

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
