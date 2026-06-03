## Phase 11 — `tFieldDefect()` target coverage.
##
## Consolidates the behavioural contract for the new symex target
## kind shipped in cycle 5. The walker A-normalises every variant
## arm-field access into an `isVariantField` statement that forks:
## the in-arm path continues; the out-of-arm path satisfies
## `tFieldDefect`. This file exercises the four shapes that matter:
##   1. Unconditional arm-field access — `sxSat` under tFieldDefect.
##   2. Properly-gated access — `sxUnsat` under tFieldDefect.
##   3. Nested variant: inner arm-field access without inner gate.
##   4. `assertCoveredBy(fn, tFieldDefect())` round-trip.
import std/unittest
import proptest/symex

# ---- Shape 1: simple variant ------------------------------------------------

type
  ShapeKind = enum skCircle, skSquare
  Shape = object
    case kind: ShapeKind
    of skCircle: radius: int
    of skSquare: side: int

proc unsafeReadRadius(s: Shape) =
  let r = s.radius  # unconditional — FieldDefect when kind = skSquare
  discard r

proc safeReadRadius(s: Shape) =
  if s.kind == skCircle:
    let r = s.radius  # gated — never FieldDefects
    discard r

# ---- Shape 2: nested variant -----------------------------------------------

type
  InnerKind = enum ikLeaf, ikBranch
  Inner = object
    case kind: InnerKind
    of ikLeaf:   value: int
    of ikBranch: count: int

  OuterKind = enum okA, okB
  Outer = object
    case kind: OuterKind
    of okA: inner: Inner
    of okB: tag:   int

proc unsafeNestedRead(o: Outer) =
  # Gates the OUTER arm but NOT the inner — `o.inner.value` can
  # FieldDefect when o.inner.kind = ikBranch.
  if o.kind == okA:
    let v = o.inner.value
    discard v

suite "symex Phase 11 — tFieldDefect target":
  test "unconditional arm-field access finds a witness":
    let r = symexFind(unsafeReadRadius, tFieldDefect())
    check r.status == sxSat
    # The found witness is a Shape; under cycle 7's case-dispatch
    # construction the witness reflects the arm Z3 picked. For
    # the FieldDefect branch Z3 chose the OUT-of-arm side, so the
    # witness's kind is NOT skCircle.
    check r.witness[0].kind != skCircle

  test "properly-gated access — tFieldDefect proves unreachable":
    let r = symexFind(safeReadRadius, tFieldDefect())
    check r.status == sxUnsat

  test "nested variant — inner arm-field access without inner gate":
    let r = symexFind(unsafeNestedRead, tFieldDefect())
    check r.status == sxSat
    # The witness must put the outer in okA (gated) AND inner in
    # a tag that doesn't have `value` (i.e., ikBranch).
    let o = r.witness[0]
    check o.kind == okA
    check o.inner.kind == ikBranch

  test "assertCoveredBy(fn, tFieldDefect()) — testFn raises FieldDefect":
    # The verifier: assertCoveredBy invokes `unsafeReadRadius` on
    # the witness and catches FieldDefect. With the unconditional
    # access SUT, the witness's kind ≠ skCircle, so the call DOES
    # raise FieldDefect — coverage proven.
    assertCoveredBy(unsafeReadRadius, tFieldDefect())

  test "assertCoveredBy(safe-fn, tFieldDefect()) — UNSAT vacuously passes":
    # When symex proves tFieldDefect unreachable, assertCoveredBy
    # passes vacuously (no witness to run testFn on).
    assertCoveredBy(safeReadRadius, tFieldDefect())
