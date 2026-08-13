## Phase 16 D1c — model `and`/`or` short-circuit evaluation in the DSL parser.
##
## Root cause (pre-D1c):
##   The `nnkInfix` arm of `parseExpr` parsed LHS and RHS into the SAME preamble.
##   Any defect-fork stmts hoisted by the RHS (e.g., `isVariantField`, `isIndex`,
##   `isDeref`) landed UNCONDITIONALLY — even when the LHS already made the RHS
##   unreachable at runtime (Nim's `and`/`or` short-circuits).
##
## D1c fix: for `and`/`or`, parse the RHS into a SEPARATE preamble; if it is
## non-empty, emit an `isLet` + `isIf` guard pair so the RHS preamble only runs
## when the LHS value demands it (`true` for `and`, `false` for `or`).
##
## Fast path unchanged: when RHS preamble is empty (no hoisted stmts), the
## resulting IR is IDENTICAL to the pre-D1c form — pure bool `a and b` still
## lowers to a single `mkBinop(bAnd, a, b)`.
import std/unittest
import nelli/symex

# ---- Type fixtures -----------------------------------------------------------

type
  Inner = object
    case k: bool
    of true:  x: int
    of false: n: int

  Outer = object
    inner: Inner

# ---- SUT 1: and-guarded variant field (the D1c tracer) ----------------------

proc guardedAndField(o: Outer) =
  ## D1c tracer. Pre-D1c: `o.inner.x` is hoisted unconditionally before the
  ## isIf; the FieldDefect fork fires even when `o.inner.k` is false.
  ## Post-D1c: the RHS preamble (isVariantField for `o.inner.x`) is wrapped in
  ## an `if __sc:` guard — no spurious FieldDefect.
  if o.inner.k and o.inner.x > 0:
    symexTarget("guarded-and-field")

# ---- SUT 2: and-guarded nil deref -------------------------------------------

proc guardedNilDeref(p: ref int) =
  ## `p != nil and p[] == 99` — the RHS deref is guarded by the nil check.
  ## Pre-D1c: `p[]` is hoisted unconditionally → spurious NilAccessDefect.
  ## Post-D1c: RHS preamble is wrapped in `if (p != nil):` — no false positive.
  if p != nil and p[] == 99:
    symexTarget("guarded-nil-deref")

# ---- SUT 3: and-guarded index -----------------------------------------------

proc guardedIndex(a: array[5, int], i: int) =
  ## `i >= 0 and i < 5 and a[i] == 7` — index is guarded by both bounds checks.
  ## Pre-D1c: `a[i]` hoisted unconditionally → spurious IndexDefect.
  ## Post-D1c: RHS preamble is wrapped; no OOB finding when i >= 0 and i < 5.
  if i >= 0 and i < 5 and a[i] == 7:
    symexTarget("guarded-index")

# ---- SUT 4: or short-circuit ------------------------------------------------

type
  OrInner = object
    case hasX: bool
    of true:  xval: int
    of false: nval: int

proc orShortCircuit(s: OrInner) =
  ## `s.hasX or s.nval > 0` — when LHS (s.hasX) is true, RHS (s.nval) is not
  ## evaluated (short-circuit). `s.nval` lives in the `false` arm; accessing it
  ## when `hasX=true` would be a FieldDefect.
  ## Pre-D1c: `s.nval` hoisted unconditionally → spurious FieldDefect even when
  ## `s.hasX` is true. Post-D1c: RHS wrapped in `if not sc:` guard.
  if s.hasX or s.nval > 0:
    symexTarget("or-hit")

# ---- SUT 5: value-position desugar ------------------------------------------

proc valuePosAnd(o: Outer) =
  ## The short-circuit desugar must also work when `and` is NOT the condition
  ## of an `if` — i.e., when it appears on the RHS of a `let` binding.
  ## `let ok = o.inner.k and o.inner.x > 0; if ok: symexTarget(…)`
  let ok = o.inner.k and o.inner.x > 0
  if ok:
    symexTarget("value-pos")

# ---- SUT 6: real defect still found (no false negative) ---------------------

proc bareFieldAccess(o: Outer) =
  ## Unconditional arm-field access — NO guard. A FieldDefect is genuinely
  ## reachable when `o.inner.k == false`. D1c must NOT suppress real defects.
  if o.inner.x > 0:
    discard

# ---- SUT 7: pure-bool fast path unchanged -----------------------------------

proc pureBoolAnd(a, b: bool) =
  ## `a and b` — both params are plain bools; no defect-fork stmts hoisted.
  ## D1c fast path: zero-preamble RHS → emit mkBinop(bAnd, a, b) unchanged.
  if a and b:
    symexTarget("pure-bool")

# ---- Tests ------------------------------------------------------------------

suite "symex Phase 16 D1c — and/or short-circuit modeling":

  test "and-guarded variant field: no spurious FieldDefect, target reachable":
    ## The tracer. Pre-D1c: sxRaised{FieldDefect}. Post-D1c: sxSat.
    let r = symexFind(guardedAndField, tLabel("guarded-and-field"))
    check r.status == sxSat
    check r.witness[0].inner.k == true
    check r.witness[0].inner.x > 0

  test "and-guarded nil deref: no spurious NilAccessDefect":
    let r = symexFind(guardedNilDeref, tLabel("guarded-nil-deref"))
    check r.status == sxSat

  test "and-guarded index: no spurious IndexDefect when guards precede access":
    let r = symexFind(guardedIndex, tLabel("guarded-index"))
    check r.status == sxSat
    check r.witness[1] >= 0
    check r.witness[1] < 5

  test "or short-circuit: no spurious FieldDefect when LHS true guards RHS":
    let r = symexFind(orShortCircuit, tLabel("or-hit"))
    check r.status == sxSat

  test "value-position: and desugar works outside condition position":
    let r = symexFind(valuePosAnd, tLabel("value-pos"))
    check r.status == sxSat
    check r.witness[0].inner.k == true
    check r.witness[0].inner.x > 0

  test "real defect still found: unguarded arm-field access still raises FieldDefect":
    ## D1c must NOT suppress real defects — only false positives from guarded RHS.
    let r = symexFind(bareFieldAccess, tFieldDefect())
    check r.status == sxRaised
    check r.raisedTypeId == "FieldDefect"

  test "pure-bool fast path: plain `a and b` still reaches label target":
    let r = symexFind(pureBoolAnd, tLabel("pure-bool"))
    check r.status == sxSat
    check r.witness[0] == true
    check r.witness[1] == true
