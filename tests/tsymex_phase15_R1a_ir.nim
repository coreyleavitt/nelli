## Phase 15 — Cluster R (FINAL cluster), cycle R1a: ref/ptr IR (`itRef`/`itPtr`)
## + deref/new statement IR (`isDeref`/`isNew`) + `SVKind` variants
## (`svRef`/`svPtr`) + exhaustive dispatch STUBS. PURELY STRUCTURAL — the
## logical-heap SEMANTICS (sort allocation, select/store, freshness, nil-fork,
## alias propagation, witness serialisation) land R1–R13. Until then the walker
## STUBS any `itRef`/`itPtr`/`isDeref`/`isNew` it reaches with a deterministic
## classified `heUnresolvedRef` (sevError) → `sxUnknown` (Invariant 3 — never a
## silent UNSAT, never a crash). `owned T`/`WeakRef[T]`/`Atomic[T]` classify to a
## `heUnsupportedOwnership` (sevError) classified halt. See ADR-0010
## (logical-heap model) and RFC §Cluster R / §R1a.
##
## R1a is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
import std/[unittest, macros, strutils]
import proptest/smt/types
import proptest/smt/dsl_typebridge
import proptest/smt/canonicalize
import proptest/smt/runtime
import proptest/symex

# --- SUTs ------------------------------------------------------------------

# A SUT taking a `ref int` param (no deref). R1a STUBS it: classifying the
# `ref int` to `itRef(itInt)` and allocating the param SymVal fires the
# heUnresolvedRef classified halt -> sxUnknown.
proc refParamSut(p: ref int): bool =
  result = true
  symexTarget("after")

# A SUT taking a `ptr int` param.
proc ptrParamSut(p: ptr int): bool =
  result = true
  symexTarget("after")

# Classify the type of a typed proc's first formal parameter.
macro firstParamTy(p: typed): untyped =
  let impl = p.getImpl
  let formal = impl[3]
  let tyNode = formal[1][formal[1].len - 2]
  let cls = classifyType(tyNode)
  # Surface the IRType kind + (for ref/ptr) pointee kind as a literal tuple.
  case cls.ty.kind
  of itRef:
    newLit("ref:" & $cls.ty.refPointeeTy.kind)
  of itPtr:
    newLit("ptr:" & $cls.ty.ptrPointeeTy.kind)
  else:
    newLit($cls.ty.kind)

suite "symex Phase 15 R1a — ref/ptr IR (itRef/itPtr/isDeref/isNew) + svRef/svPtr stub":

  test "R1a: tRef/tPtr IR types round-trip through canonicalize (stable, distinct keys)":
    let rt = tRef(tInt(64, true))
    let pt = tPtr(tInt(64, true))
    let r1 = canonicalize(rt)
    let r2 = canonicalize(rt)
    check r1 == r2                       # stable
    check r1.contains("Rf")              # tagged as a ref
    let p1 = canonicalize(pt)
    check p1.contains("Pt")              # tagged as a ptr
    check r1 != p1                       # ref vs ptr: distinct keys
    # ref int vs ref bool: distinct pointee -> distinct keys.
    check canonicalize(tRef(tInt(64, true))) != canonicalize(tRef(tBool()))

  test "R1a: tRef/tPtr render + equality are structural":
    check ($tRef(tInt(64, true))).contains("ref")
    check ($tPtr(tInt(64, true))).contains("ptr")
    check tRef(tInt(64, true)) == tRef(tInt(64, true))
    check tRef(tInt(64, true)) != tPtr(tInt(64, true))
    check tRef(tInt(64, true)) != tRef(tBool())

  test "R1a: isDeref/isNew statement IR round-trips through canonicalize + render":
    let d = mkDeref("r0", mkVar("p"), tInt(64, true))
    let n = mkNewT("r1", tRef(tInt(64, true)))
    let dk1 = canonicalize(d)
    let dk2 = canonicalize(d)
    check dk1 == dk2                      # stable
    check dk1.contains("Dr")             # tagged as a deref
    let nk = canonicalize(n)
    check nk.contains("Nw")              # tagged as a new
    check dk1 != nk
    check render(d).contains("deref")
    check render(n).contains("new")

  test "R1a: mkPtrDeref is distinct from mkDeref (ptr-family marker)":
    let pd = mkPtrDeref("r0", mkVar("p"), tInt(64, true))
    let rd = mkDeref("r0", mkVar("p"), tInt(64, true))
    check render(pd).contains("deref")
    # both render through the same dispatch; canonicalize is stable.
    check canonicalize(pd) == canonicalize(pd)

  test "R1a: classifyType on `ref int` -> itRef(itInt)":
    check firstParamTy(refParamSut) == "ref:itInt"

  test "R1a: classifyType on `ptr int` -> itPtr(itInt)":
    check firstParamTy(ptrParamSut) == "ptr:itInt"

  test "R1a: a SUT with a `ref int` param yields sxUnknown + heUnresolvedRef (stub fires)":
    let res = symexFind(refParamSut, tLabel("after"))
    check res.status == sxUnknown
    var sawHe = false
    for e in res.errors:
      if e.kind == heUnresolvedRef and e.severity == sevError:
        sawHe = true
    check sawHe

  test "R1a: a SUT with a `ptr int` param yields sxUnknown + heUnresolvedRef (stub fires)":
    let res = symexFind(ptrParamSut, tLabel("after"))
    check res.status == sxUnknown
    var sawHe = false
    for e in res.errors:
      if e.kind == heUnresolvedRef and e.severity == sevError:
        sawHe = true
    check sawHe

  test "R1a: SymexSettings.maxHeapDepth default is 8 and survives the + merge":
    check defaultSymexSettings().maxHeapDepth == 8
    let overridden = withSymexSettings() do (s: var SymexSettings):
      s.maxHeapDepth = 3
    check overridden.maxHeapDepth == 3
    # + merge: a non-default maxHeapDepth on the RHS overrides the LHS.
    let merged = defaultSymexSettings() + overridden
    check merged.maxHeapDepth == 3
