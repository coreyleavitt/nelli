import std/unittest
import proptest/symex
import std/tables

# Phase 15 — field-container assert regression: the four `doAssert == iekVar`
# guards added in commit cecc36a crash on VALID programs where the container /
# receiver is a FIELD access (iekField) rather than a bare env var (iekVar).
#
# The parser A-normalises so that the INDEX EXPRESSION and the VALUE being
# assigned are always plain vars/literals, but the CONTAINER EXPRESSION for
# isIndex/isVariantField and the POINTER EXPRESSION for isDeref/isDerefWrite
# can legally be an `iekField` — e.g. when the seq / ref / variant value
# lives INSIDE an object parameter, not at the top env level.
#
# Examples:
#   type Bag = object; xs: seq[int]
#   bag.xs[i]     → isIndex(ixArr=mkField(bag,0,"xs"), ...)   ← iekField!
#
#   type Holder = object; p: ref int
#   h.p[]         → isDeref(dPtr=mkField(h,0,"p"), ...)       ← iekField!
#   h.p[] = v     → isDerefWrite(dwPtr=mkField(h,0,"p"), ...)  ← iekField!
#
#   type Inner = object; case k: bool; ...
#   type Outer = object; inner: Inner
#   o.inner.x     → isVariantField(vfRecv=mkField(o,0,"inner"),..) ← iekField!
#
#   type MapHolder = object; t: Table[string,int]
#   m.t["k"]      → isIndex(ixArr=mkField(m,0,"t"), ...)      ← iekField!
#
# RED STATE (before fix): each SUT crashes with AssertionDefect:
#   "isIndex: ixArr must be an env-resident var (iekVar); got iekField ..."
#   "isVariantField: vfRecv must be an env-resident var (iekVar); got iekField ..."
#   "isDeref: dPtr must be an env-resident var (iekVar); got iekField ..."
#   "isDerefWrite: dwPtr must be an env-resident var (iekVar); got iekField ..."
#
# GREEN STATE (after fix): relax each `doAssert` to `in {iekVar, iekField}`;
# the AssertionDefect crash is eliminated; each SUT produces a verdict
# (sxSat for value-typed containers; sxUnknown for ref-field derefs due to
# the separate pre-existing sort-mismatch between classifyFieldType's named
# placeholder and the isDeref dElemTy path — a bug beyond this fix's scope).

# ---- Shape 1: object field as seq index container ---------------------------
type
  Bag = object
    xs: seq[int]

proc seqFieldIndex(bag: Bag, i: int) =
  ## `bag.xs[i]` — the seq container is an object field (iekField), not a bare var.
  ## Phase 16 D1c: restored flat-and chain; D1c short-circuit prevents spurious
  ## IndexDefect when bounds guards precede the index access.
  if bag.xs.len > 0 and i >= 0 and i < bag.xs.len and bag.xs[i] == 99:
    symexTarget("seqField")

# ---- Shape 2: deref of a field -----------------------------------------------
type
  Holder = object
    p: ref int

proc derefField(h: Holder) =
  ## `h.p[]` — the pointer is an object field (iekField).
  ## Nil guard before deref: D1a fires NilAccessDefect unconditionally otherwise.
  if h.p != nil:
    if h.p[] == 7:
      symexTarget("derefField")

# ---- Shape 3: deref-write of a field -----------------------------------------
proc derefWriteField(h: Holder, v: int) =
  ## `h.p[] = v` — the pointer in the write is an object field (iekField).
  ## Nil guard before deref-write: D1a fires NilAccessDefect unconditionally otherwise.
  if h.p != nil:
    h.p[] = v
    if h.p[] == v:
      symexTarget("derefWriteField")

# ---- Shape 4: variant field of a field ----------------------------------------
type
  Inner = object
    case k: bool
    of true:  x: int
    of false: n: int
  Outer = object
    inner: Inner

proc variantFieldOfField(o: Outer) =
  ## `o.inner.x` — the variant receiver `o.inner` is an object field (iekField).
  ## Phase 16 D1c: restored flat-and form.
  if o.inner.k and o.inner.x > 0:
    symexTarget("variantField")

# ---- Shape 5: table access via a field ----------------------------------------
type
  MapHolder = object
    t: Table[string, int]

proc tableViaField(m: MapHolder) =
  ## `m.t["k"]` — the table container `m.t` is an object field (iekField).
  if "k" in m.t and m.t["k"] == 42:
    symexTarget("tableField")

suite "symex Phase 15 — field-container assert (iekField containers)":

  test "field-container-1: seq field index bag.xs[i]==99 — sxSat (RED: doAssert crash before fix)":
    ## Before fix: `doAssert stmt.ixArr.kind == iekVar` fires because
    ## `bag.xs` lowers to iekField. After fix: both iekVar and iekField accepted.
    ## Value-typed seq field: no sort mismatch; sxSat.
    let r = symexFind(seqFieldIndex, tLabel("seqField"))
    check r.status == sxSat

  test "field-container-2: deref of field h.p[] — sxSat (CR-19 sort-mismatch fixed)":
    ## Before field-container-assert fix: `doAssert stmt.dPtr.kind == iekVar` fires.
    ## After that fix but before CR-19: sxUnknown due to classifyFieldType returning
    ## tRef(tTuple([],"int")) while isDeref's dElemTy = tInt(64,true) → Z3Sort mismatch.
    ## After CR-19: classifyFieldType for ref-of-primitive falls through to classifyType
    ## → tRef(tInt(64,true)), matching dElemTy exactly → sxSat.
    let r = symexFind(derefField, tLabel("derefField"))
    check r.status == sxSat

  test "field-container-3: deref-write of field h.p[]=v — sxSat (CR-19 sort-mismatch fixed)":
    ## Same sort-mismatch as shape 2; fixed by the same CR-19 change.
    let r = symexFind(derefWriteField, tLabel("derefWriteField"))
    check r.status == sxSat

  test "field-container-4: variant field of field o.inner.x>0 — sxSat (RED: doAssert crash before fix)":
    ## Before fix: `doAssert stmt.vfRecv.kind == iekVar` fires because
    ## `o.inner` lowers to iekField (the variant is a field of the outer object).
    ## After fix: sxSat with o.inner.k==true, o.inner.x>0.
    let r = symexFind(variantFieldOfField, tLabel("variantField"))
    check r.status == sxSat

  test "field-container-5: table via field m.t[\"k\"]==42 — sxSat (RED: doAssert crash before fix)":
    ## Before fix: `doAssert stmt.ixArr.kind == iekVar` fires because
    ## `m.t` lowers to iekField. After fix: sxSat via the table model.
    let r = symexFind(tableViaField, tLabel("tableField"))
    check r.status == sxSat
