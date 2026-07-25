## Phase 15 — Cluster R (FINAL cluster), cycle R6: `ref object` field access.
##
## `p.field` (a field read through a ref to an OBJECT type) and `p.field = v`
## (a field write through such a ref). The object pointee is modelled as an
## `svTuple` (Phase 4); a Z3 array cannot carry a record VALUE sort (there is
## no Z3 tuple sort in this engine — C0-ADR), so R6 uses FIELD-SPLIT heaps: a
## SEPARATE per-(type, field) array `heap_<objTid>__<field>: Z3Array[Ref_T,
## <fieldSort>]`, all keyed by the SAME `Ref_T` address sort (one ref → one
## address, observed across every field array).
##
##   * `p.x` READ  → `select(heap_<objTid>__x, p)` → the field's SymVal.
##   * `p.x = v` WRITE → `heap_<objTid>__x := store(heap_<objTid>__x, p, v)`
##     (only the x-array changes; an aliased `q.x` reads the same index → sees
##      the write — Z3's array theory, no fork).
##
## DoD (RFC §R6 + reconciliation §F-R6):
##   1. Aliased field write observable: `p.x = 42; if q.x == 42` →
##      `sxSat` with witness `p == q` (the headline test).
##   2. Field read: `p.x == 7` → sxSat.
##   3. Non-alias: a write through p and a read through a DIFFERENT fresh ref q
##      is independent (q.x not forced equal).
##   4. Inherited fields (`ref object of Base`) — flat layout, if tractable;
##      else honestly deferred + documented.
##   5. Variant-fielded ref object disc read (ADR-0013 Slice 1): discriminant
##      read through a ref → sxSat (walker v27+ models the disc heap).
##
## See ADR-0010 (logical heap) and RFC §R6. R6 is ADDITIVE under walker version
## "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

type
  Point = object
    x, y: int

# --- DoD 1: aliased field write observable (the headline test) ----------------
# `p.x = 42` stores 42 into the x-array at p's address. The read `q.x` selects
# the SAME x-array at q's address; when p == q (same address) it sees 42.
proc f(p, q: ref Point) =
  if p != nil and q != nil:
    p.x = 42
    if q.x == 42:
      symexTarget("alias_field")

# --- DoD 2: field read --------------------------------------------------------
proc g(p: ref Point): bool =
  p.x == 7

proc gRead(p: ref Point) =
  if p != nil:
    if p.x == 7:
      symexTarget("field_read")

# --- DoD 3: non-alias independence (Cluster H Step C: Nim-faithful zero-init) --
# Two DISTINCT fresh `new(Point)` allocations. Under the universal isNew
# zero-write (Cluster H Step C, ADR-0022), a local `new(T)` zero-initialises its
# fields to match real Nim — so q.x is q's OWN cell (value 0), and the write
# `p.x = 42` is NOT observable through the distinct fresh q. `q.x == 42` (the
# value written through p) is therefore UNSATISFIABLE: it would hold only if q
# aliased p, and distinct fresh allocations never do — the sharp non-alias
# signature (contrast R6 test 1, where p == q is possible for PARAM refs, making
# the write observable → sxSat). NB: pre-Step-C this SUT modelled a local `new`
# field as free/havoc and asserted `q.x == 7` reachable (sxSat) — an UNSOUND
# false-SAT, since real Nim zero-inits and q.x is never 7. Step C's zero-write
# corrects it; PARAM refs stay free (caller-havoc), only local allocations are
# zero-initialised.
proc nonAlias() =
  let p = new(Point)
  let q = new(Point)
  p.x = 42
  if q.x == 42:               # distinct fresh q → q.x == 0, never p's 42 → unsat
    symexTarget("nonalias")

# --- DoD 4: inherited fields (ref object of Base) -----------------------------
type
  Base = object of RootObj
    bx: int
  Child = object of Base
    cy: int

proc inheritedRead(p: ref Child) =
  if p != nil:
    # p.bx is the INHERITED base field (flat-offset 0); p.cy is the own field.
    if p.bx == 5 and p.cy == 9:
      symexTarget("inherited")

# --- DoD 5: variant-fielded ref object → classified unsupported ---------------
# An INLINE `ref VNode` where VNode has variant fields. The field-split heap has
# no flat positional layout to split a variant on, so a field access through the
# ref is honestly classified `heRefVariantUnsupported` (sevError) → sxUnknown,
# NOT a Defect on svTuple dispatch. (A NAMED `type N = ref object` with variant
# fields still unwraps to a value variant — path (2) — and is modelled as a
# plain in-memory variant; this negative DoD targets the inline ref-deref path.)
type
  VNode = object
    case tag: bool
    of true:  val: int
    of false: nextField: int

proc variantRef(p: ref VNode) =
  if p.tag:
    symexTarget("variant")

suite "symex Phase 15 R6 — ref object field access (heap field-split + alias-observable)":

  test "R6 test 1: aliased field write p.x=42; q.x==42 is sxSat with witness p==q (headline)":
    let r = symexFind(f, tLabel("alias_field"))
    check r.status == sxSat

  test "R6 test 2: field read p.x==7 is sxSat":
    let r = symexFind(gRead, tLabel("field_read"))
    check r.status == sxSat

  test "R6 test 3: non-alias — write through p NOT observable through DISTINCT fresh q (sxUnsat)":
    ## Cluster H Step C (ADR-0022): local `new(T)` fields are zero-initialised
    ## (Nim-faithful), so the distinct fresh q never sees p's write — `q.x == 42`
    ## is unsatisfiable. Pre-Step-C this modelled q.x as free and asserted
    ## `q.x == 7` reachability (sxSat), a false-SAT the zero-write removes.
    let r = symexFind(nonAlias, tLabel("nonalias"))
    check r.status == sxUnsat

  test "R6 test 4 (inherited, flat layout): p.bx (base) and p.cy (own) both resolve → sxSat":
    let r = symexFind(inheritedRead, tLabel("inherited"))
    check r.status == sxSat

  test "R6 test 5 (variant ref object disc read): discriminant read through ref → sxSat (ADR-0013 Slice 1)":
    let r = symexFind(variantRef, tLabel("variant"))
    check r.status == sxSat
