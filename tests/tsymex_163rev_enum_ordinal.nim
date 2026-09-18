## Issue #163 review finding R15 (Critical, soundness regression): the #141
## enum-value resolver in `dsl_parser.nim`'s `parseExpr` `nnkSym` arm
## (~line 2470) embeds an enum CONSTANT referenced in expression position
## (the RHS of `x == roLess`) as its DECLARATION-POSITION loop index
## (`i - 1`), never its actually-assigned ORDINAL:
##
##     if fieldSym.strVal == s:
##       return mkIntLit(int64(i - 1))
##
## This is a different code path from finding R2
## (`tsymex_163rev_enum_domain.nim`): R2 fixed the CLASSIFIER's domain
## computation (`dsl_typebridge.classifyType`'s enum arm, `[minOrd, maxOrd]`)
## for a plain enum-typed PARAM/field. This file's bug is in the PARSER's
## literal-embedding path for an enum constant NAME used as a value in an
## expression -- e.g. the `roLess` in `x == roLess`. Both loops walk the same
## `nnkEnumTy` child list and both must track a real ordinal (explicit
## `nnkEnumFieldDef` value, else previous-ordinal-plus-one); a divergence
## between the two reintroduces exactly this class of bug in the other
## direction (the classifier's domain and the parser's embedded constant
## would then disagree about what is legal).
##
## On `type Ordering = enum roLess = -1, roEqual = 0, roGreater = 1`
## (declaration positions 0, 1, 2 respectively), the buggy `i - 1` embeds:
##   `roLess`    -> 0   (should be -1)
##   `roEqual`   -> 1   (should be  0)
##   `roGreater` -> 2   (should be  1; 2 is OUTSIDE the domain [-1, 1], so
##                       this arm flips a REACHABLE target to sxUnsat)
##
## Per house style (`tsymex_163audit_range_domain.nim`,
## `tsymex_163rev_enum_domain.nim`), every symbolic expectation here is
## paired with an ORACLE computed by real Nim execution. For THIS defect the
## oracle must specifically REPLAY the reported witness: cast the raw
## int/uint `symexFind` returns back to the enum type, and check in real Nim
## that the cast value genuinely satisfies the comparison the target was
## gated on. Checking only `r.status == sxSat` is not enough -- two of the
## three `Ordering` arms are `sxSat` even pre-fix, just with a witness that
## does not actually take the claimed branch.
##
## No version-floor pin in this file: the round's single `symexWalkerVersion`
## bump lands centrally from the control loop, not per-fix.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/dsl_typebridge

## ---------------------------------------------------------------------------
## Cross-check: the parser's embedded constant and the classifier's declared
## domain must agree on what "in range" means for the SAME enum type. Reuse
## R2's typedesc-classifying helper so this file does not have to touch
## `dsl_typebridge.nim` to observe its output.

import std/macros

macro classifyEnumTypedesc(T: typedesc): (bool, int64, int64, bool) =
  var inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst = inst[1]
  let cls = classifyType(inst)
  newTree(nnkTupleConstr, newLit(cls.ty.hasRange), newLit(cls.ty.rangeLo),
          newLit(cls.ty.rangeHi), newLit(cls.ty.signed))

## ---------------------------------------------------------------------------
## Negative-ordinal enum: all three arms, each with witness replay. The
## middle two are false-SAT (wrong witness) pre-fix; the last is a false
## NEGATIVE (wrong verdict) pre-fix.

type
  Ordering = enum
    roLess = -1
    roEqual = 0
    roGreater = 1

const orderingInfo = classifyEnumTypedesc(Ordering)

proc checkRoLess(x: Ordering) =
  if x == roLess:
    symexTarget("less")

proc checkRoEqual(x: Ordering) =
  if x == roEqual:
    symexTarget("equal")

proc checkRoGreater(x: Ordering) =
  if x == roGreater:
    symexTarget("greater")

suite "#163 review R15 -- enum constants embed their ordinal, not position":

  test "the oracle -- Ordering's real ordinals are -1, 0, 1":
    check ord(roLess) == -1
    check ord(roEqual) == 0
    check ord(roGreater) == 1

  test "cross-check -- classifier domain agrees with what the parser must embed":
    ## R2 already fixed the classifier's domain to [-1, 1] signed. The
    ## parser's embedded constants must land INSIDE this same domain at
    ## their true ordinal -- if the two ever disagree, one of them is wrong.
    check orderingInfo == (true, -1'i64, 1'i64, true)

  test "x == roLess is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): sxSat, but the embedded RHS was 0 (roLess's
    ## declaration-position index), not -1 (roLess's real ordinal) -- so the
    ## solver actually satisfied `x == 0`, and the returned witness casts
    ## back to roEqual, NOT roLess. A test checking only `status == sxSat`
    ## would have passed against this broken witness.
    let r = symexFind(checkRoLess, tLabel("less"))
    check r.status == sxSat
    check Ordering(r.witness[0]) == roLess

  test "x == roEqual is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): sxSat with embedded RHS 1 (roEqual's declaration-position
    ## index, not its real ordinal 0) -- witness casts back to roGreater,
    ## NOT roEqual.
    let r = symexFind(checkRoEqual, tLabel("equal"))
    check r.status == sxSat
    check Ordering(r.witness[0]) == roEqual

  test "x == roGreater is reachable -- was falsely sxUnsat pre-fix":
    ## RED (pre-fix): sxUnsat. roGreater's declaration-position index is 2,
    ## which is OUTSIDE the classifier's own domain [-1, 1] -- a genuinely
    ## reachable target flipped to a false NEGATIVE, not merely a wrong
    ## witness. This is the sharpest form of the defect: replaying a
    ## reported witness is moot when no witness is reported at all.
    let r = symexFind(checkRoGreater, tLabel("greater"))
    require r.status == sxSat
    let witnessed = Ordering(r.witness[0])
    check witnessed == roGreater

## ---------------------------------------------------------------------------
## Sparse/holed enum, no negatives: ordinal diverges from declaration
## position without needing a negative ordinal to expose it.

type
  Holed = enum
    hoA = 0
    hoB = 5
    hoC = 6

const holedInfo = classifyEnumTypedesc(Holed)

proc checkHoA(x: Holed) =
  if x == hoA:
    symexTarget("a")

proc checkHoB(x: Holed) =
  if x == hoB:
    symexTarget("b")

proc checkHoC(x: Holed) =
  if x == hoC:
    symexTarget("c")

suite "#163 review R15 -- sparse/holed enum, ordinal diverges without negatives":

  test "the oracle -- Holed's real ordinals are 0, 5, 6":
    check ord(hoA) == 0
    check ord(hoB) == 5
    check ord(hoC) == 6

  test "cross-check -- classifier domain is [0, 6], unsigned":
    check holedInfo == (true, 0'i64, 6'i64, false)

  test "x == hoA is reachable with a genuinely correct witness":
    ## Declaration position 0 happens to equal hoA's real ordinal 0, so this
    ## arm is correct even pre-fix -- a same-position sanity check.
    let r = symexFind(checkHoA, tLabel("a"))
    check r.status == sxSat
    check Holed(r.witness[0]) == hoA

  test "x == hoB is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): sxSat with embedded RHS 1 (hoB's declaration-position
    ## index), not 5 (hoB's real ordinal) -- the witness casts back to a
    ## holey non-member value, never hoB.
    let r = symexFind(checkHoB, tLabel("b"))
    check r.status == sxSat
    check Holed(r.witness[0]) == hoB

  test "x == hoC is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): sxSat with embedded RHS 2 (hoC's declaration-position
    ## index), not 6 (hoC's real ordinal) -- the witness casts back to a
    ## holey non-member value, never hoC. (Unlike `roGreater` above, 2 is
    ## still inside the classifier's [0, 6] domain, so this stays a
    ## false-WITNESS case, not a false-negative one -- the false-negative
    ## shape is already covered by `roGreater`.)
    let r = symexFind(checkHoC, tLabel("c"))
    check r.status == sxSat
    check Holed(r.witness[0]) == hoC

## ---------------------------------------------------------------------------
## Non-regression: a dense enum starting at 0, where declaration position and
## ordinal always coincide, must keep behaving exactly as before.

type
  Color = enum
    clRed
    clGreen
    clBlue

const colorInfo = classifyEnumTypedesc(Color)

proc checkRed(x: Color) =
  if x == clRed:
    symexTarget("red")

proc checkGreen(x: Color) =
  if x == clGreen:
    symexTarget("green")

proc checkBlue(x: Color) =
  if x == clBlue:
    symexTarget("blue")

suite "#163 review R15 -- non-regression: dense enum, ordinal == position":

  test "the oracle -- Color's real ordinals are 0, 1, 2":
    check ord(clRed) == 0
    check ord(clGreen) == 1
    check ord(clBlue) == 2

  test "cross-check -- classifier domain is [0, 2], unsigned":
    check colorInfo == (true, 0'i64, 2'i64, false)

  test "every arm is reachable with a witness that genuinely matches":
    let rRed = symexFind(checkRed, tLabel("red"))
    check rRed.status == sxSat
    check Color(rRed.witness[0]) == clRed

    let rGreen = symexFind(checkGreen, tLabel("green"))
    check rGreen.status == sxSat
    check Color(rGreen.witness[0]) == clGreen

    let rBlue = symexFind(checkBlue, tLabel("blue"))
    check rBlue.status == sxSat
    check Color(rBlue.witness[0]) == clBlue


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. Compared numerically, not lexicographically:
    ## `"1000" < "135"` as strings.
    check parseInt(symexWalkerVersion) >= 135
