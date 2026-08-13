## Uninitialized `var x: T` (no initializer) — Nim zero-initializes, so the
## symex model binds each name to its type's ZERO value. Zero-init (not a fresh
## free symbol) is the SOUND model: a read-before-write must observe Nim's
## guaranteed default, never an arbitrary value (Invariant 3 — no false paths).
##
## Before this fix, `var bs: int` reached parseExpr on an nnkEmpty value node →
## `error("unsupported expression kind nnkEmpty")`, a compile-time MACRO failure
## (strictly worse than a classified sxUnknown). Additive coverage of
## previously-erroring input; no walker-version bump (no existing verdict/canon
## changes — nothing with an uninitialized var could be analyzed before).
import std/[unittest, strutils]
import nelli/symex

# --- the chapulin structural case: uninit var, assigned, then gated ----------
proc sutAssignThenGate(n: int) =
  var bs: int
  bs = n + 1
  if bs == 5:
    symexTarget("hit")

# --- zero-init faithfulness: read BEFORE assign sees 0 -----------------------
proc sutReadZeroInt(n: int) =
  var x: int
  if x == 0:            # Nim guarantees x == 0 here
    symexTarget("zero")

# --- SOUNDNESS: an unassigned int is 0, so it can NEVER equal 7 --------------
proc sutUnassignedNeverSeven(n: int) =
  var x: int            # never assigned
  if x == 7:            # unreachable — x is 0 (must be UNSAT, not a false sat)
    symexTarget("seven")

# --- bool zero-init is false -------------------------------------------------
proc sutReadZeroBool(n: int) =
  var b: bool
  if not b:             # b == false
    symexTarget("false")

# --- chapulin-like: uninit var feeding a parseInt/validate path --------------
proc sutParseValidate(s: string) =
  var bs: int
  try:
    bs = parseInt(s)
  except ValueError:
    bs = -1
  if bs == 512:
    symexTarget("got512")

suite "symex: uninitialized var zero-init (nnkEmpty)":
  test "U1: `var bs: int` assigned then gated → sxSat":
    let r = symexFind(sutAssignThenGate, tLabel("hit"))
    check r.status == sxSat

  test "U2: uninit int read before assign sees 0 → sxSat":
    let r = symexFind(sutReadZeroInt, tLabel("zero"))
    check r.status == sxSat

  test "U3: SOUNDNESS — unassigned int can never be 7 → sxUnsat":
    let r = symexFind(sutUnassignedNeverSeven, tLabel("seven"))
    check r.status == sxUnsat

  test "U4: uninit bool is false → sxSat":
    let r = symexFind(sutReadZeroBool, tLabel("false"))
    check r.status == sxSat

  test "U5: uninit var in a parseInt/try-except validator → sxSat (got 512)":
    let r = symexFind(sutParseValidate, tLabel("got512"))
    check r.status == sxSat
