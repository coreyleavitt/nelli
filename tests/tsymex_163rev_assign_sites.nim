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


# =============================================================================
# Site 2 -- a variant ARM FIELD write through a ref
# =============================================================================
##
## `tsymex_163rev_armfield_write.nim` (R17) fixed the WITNESS CLAMP for this
## exact shape (a ranged arm field written but never read back) and its own
## header is explicit that the RAISE FORK at the write site itself was
## deliberately left as a separate, pre-existing gap -- this is that gap.

type
  NKindS2 = enum nkBS2, nkAS2
  NodeS2 = object
    case kind: NKindS2
    of nkAS2: v: range[1..100]
    of nkBS2: discard

proc writeArmFieldOutOfRange(p: ref NodeS2, x, y: range[0..100]) =
  if p != nil and p.kind == nkAS2:
    p.v = x + y               # x+y can reach 200 -- outside [1,100]
    symexTarget("t")
    discard p.v

proc writeArmFieldProvablyInRange(p: ref NodeS2, x, y: range[1..50]) =
  if p != nil and p.kind == nkAS2:
    p.v = x + y               # x+y in [2,100] -- always inside [1,100]
    symexTarget("t")
    discard p.v

type
  NKindPlainS2 = enum nkBPS2, nkAPS2
  NodePlainS2 = object
    case kind: NKindPlainS2
    of nkAPS2: v: int
    of nkBPS2: discard

proc writeArmFieldPlainInt(p: ref NodePlainS2, x, y: range[0..100]) =
  ## Non-regression: an ordinary unranged arm field is unaffected.
  if p != nil and p.kind == nkAPS2:
    p.v = x + y
    symexTarget("t")
    discard p.v

suite "#163 review R22 site 2 -- the oracle (variant arm field write)":

  test "Nim itself raises RangeDefect writing an out-of-range sum into a ranged arm field":
    proc rt(x, y: range[0..100]): range[1..100] =
      var n = NodeS2(kind: nkAS2, v: 1)
      n.v = x + y
      n.v
    expect RangeDefect:
      discard rt(100, 100)
    check rt(1, 0) == 1

  test "the oracle -- the precision-case sum never leaves the declared range":
    proc rt(x, y: range[1..50]): range[1..100] =
      var n = NodeS2(kind: nkAS2, v: 1)
      n.v = x + y
      n.v
    check rt(1, 1) == 2
    check rt(50, 50) == 100

suite "#163 review R22 site 2 -- an out-of-range arm field write raises instead of vanishing":

  test "a genuinely out-of-range arm field write is found as sxRaised(RangeDefect)":
    let r = symexFind(writeArmFieldOutOfRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(writeArmFieldOutOfRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 site 2 -- a provably-in-range arm field write does not fork":

  test "no RangeDefect is found when the sum cannot leave the declared range":
    let r = symexFind(writeArmFieldProvablyInRange, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached normally":
    let r = symexFind(writeArmFieldProvablyInRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 site 2 non-regression -- an ordinary unranged arm field is unaffected":

  test "no RangeDefect fork on a plain int arm field":
    let r = symexFind(writeArmFieldPlainInt, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached":
    let r = symexFind(writeArmFieldPlainInt, tLabel("t"))
    check r.status == sxSat


# =============================================================================
# Site 3 -- a seq ELEMENT write (`xs[i] = expr`)
# =============================================================================
##
## `isIndexAssign` (`runtime.nim`, N14) already rebinds `stmt.iaRecvName` to a
## new `svSeq` via `storeSeqElem` -- the declared element type is already
## live on the receiver's own `SymVal.seqElemTy` (the SAME field
## `seqElemLitProto` already reads to shape the RHS proto), so this needs no
## new IR field either.

proc writeSeqElemOutOfRange(xs: seq[range[1..100]], i: int, x, y: range[0..100]) =
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = x + y              # x+y can reach 200 -- outside [1,100]
  symexTarget("t")
  discard ys[i]

proc writeSeqElemProvablyInRange(xs: seq[range[1..100]], i: int, x, y: range[1..50]) =
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = x + y              # x+y in [2,100] -- always inside [1,100]
  symexTarget("t")
  discard ys[i]

proc writeSeqElemPlainInt(xs: seq[int], i: int, x, y: range[0..100]) =
  ## Non-regression: an ordinary unranged seq element is unaffected.
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = x + y
  symexTarget("t")
  discard ys[i]

suite "#163 review R22 site 3 -- the oracle (seq element write)":

  test "Nim itself raises RangeDefect writing an out-of-range sum into a ranged seq element":
    proc rt(x, y: range[0..100]): range[1..100] =
      var ys = @[range[1..100](1)]
      ys[0] = x + y
      ys[0]
    expect RangeDefect:
      discard rt(100, 100)
    check rt(1, 0) == 1

  test "the oracle -- the precision-case sum never leaves the declared range":
    proc rt(x, y: range[1..50]): range[1..100] =
      var ys = @[range[1..100](1)]
      ys[0] = x + y
      ys[0]
    check rt(1, 1) == 2
    check rt(50, 50) == 100

suite "#163 review R22 site 3 -- an out-of-range seq element write raises instead of vanishing":

  test "a genuinely out-of-range seq element write is found as sxRaised(RangeDefect)":
    let r = symexFind(writeSeqElemOutOfRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(writeSeqElemOutOfRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 site 3 -- a provably-in-range seq element write does not fork":

  test "no RangeDefect is found when the sum cannot leave the declared range":
    let r = symexFind(writeSeqElemProvablyInRange, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached normally":
    let r = symexFind(writeSeqElemProvablyInRange, tLabel("t"))
    check r.status == sxSat

suite "#163 review R22 site 3 non-regression -- an ordinary unranged seq element is unaffected":

  test "no RangeDefect fork on a plain int seq element":
    let r = symexFind(writeSeqElemPlainInt, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

  test "the label is still reached":
    let r = symexFind(writeSeqElemPlainInt, tLabel("t"))
    check r.status == sxSat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138 (no bump owed by this round -- forks reuse forkAssignRangeCheck/rangeCondsIfNeeded unchanged)":
    check parseInt(symexWalkerVersion) >= 138
