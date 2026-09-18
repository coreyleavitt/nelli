## Issue #163 review finding R22 -- the FOUR remaining unmodelled RangeDefect
## assignment sites R22's own report enumerated (R22 itself, commit
## `e09a286`, scoped to ONLY the plain-local-variable assignment site;
## R27/R28 extended the SAME `IRStmt.isAssign.aty` plumbing to two more
## dispatch shapes -- see `tsymex_163rev_assign_scope.nim` and
## `tsymex_163rev_scan_counter_range.nim`):
##
##   1. A plain OBJECT FIELD write through a ref (`p.field = expr`).
##   2. A variant ARM FIELD write through a ref (`p.field = expr` where
##      `field` belongs to one non-else `of` arm).
##   3. A seq ELEMENT write (`xs[i] = expr`).
##   4. A `var`/`out` PARAMETER reassignment inside its own callee.
##
## Each site forks exactly like `forkAssignRangeCheck` (`runtime.nim`,
## reused unchanged here, not re-derived): the out-of-range sub-path is a
## routed `RangeDefect` raise; the survivor's path condition is hard-narrowed
## to the in-range domain; a provably-in-range RHS (via `SymVal.ziIvl`,
## issue #161) discharges statically with no fork at all.
##
## Do NOT read this as a range CONSTRAINT at the write site -- that would
## tell the solver an out-of-range write cannot happen, silently hiding a
## genuine `RangeDefect` (the exact trap `tsymex_163rev_armfield_write.nim`'s
## header documents R17 rejecting). The model here is a FORK, not a ban.
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation executed for real in Nim, in this file.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

# =============================================================================
# Site 1 -- a plain OBJECT FIELD write through a ref
# =============================================================================

type
  BoxR = ref object
    v: range[1..100]

proc writeFieldOutOfRange(p: BoxR, x, y: range[0..100]) =
  if p != nil:
    p.v = x + y               # x+y can reach 200 -- outside [1,100]
    symexTarget("t")
    discard p.v

proc writeFieldProvablyInRange(p: BoxR, x, y: range[1..50]) =
  if p != nil:
    p.v = x + y               # x+y in [2,100] -- always inside [1,100]
    symexTarget("t")
    discard p.v

type
  BoxPlain = ref object
    v: int

proc writeFieldPlainInt(p: BoxPlain, x, y: range[0..100]) =
  ## Non-regression: an ordinary unranged `ref object` field is unaffected.
  if p != nil:
    p.v = x + y
    symexTarget("t")
    discard p.v

suite "#163 review R22 site 1 -- the oracle (ref object field write)":

  test "Nim itself raises RangeDefect writing an out-of-range sum into a ranged ref field":
    proc rt(x, y: range[0..100]): range[1..100] =
      var b = BoxR(v: 1)
      b.v = x + y
      b.v
    expect RangeDefect:
      discard rt(100, 100)
    check rt(1, 0) == 1

  test "the oracle -- the precision-case sum never leaves the declared range":
    proc rt(x, y: range[1..50]): range[1..100] =
      var b = BoxR(v: 1)
      b.v = x + y
      b.v
    check rt(1, 1) == 2
    check rt(50, 50) == 100

suite "#163 review R22 site 1 -- an out-of-range ref field write raises instead of vanishing":

  test "a genuinely out-of-range field write is found as sxRaised(RangeDefect)":
    let r = symexFind(writeFieldOutOfRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(writeFieldOutOfRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 site 1 -- a provably-in-range field write does not fork":

  test "no RangeDefect is found when the sum cannot leave the declared range":
    let r = symexFind(writeFieldProvablyInRange, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached normally":
    let r = symexFind(writeFieldProvablyInRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 site 1 non-regression -- an ordinary unranged ref field is unaffected":

  test "no RangeDefect fork on a plain int ref field":
    let r = symexFind(writeFieldPlainInt, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached":
    let r = symexFind(writeFieldPlainInt, tLabel("t"))
    check r.status == sxSat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138 (no bump owed by this round -- forks reuse forkAssignRangeCheck/rangeCondsIfNeeded unchanged)":
    check parseInt(symexWalkerVersion) >= 138
