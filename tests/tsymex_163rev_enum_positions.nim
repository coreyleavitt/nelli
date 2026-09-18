## Issue #163 review findings R21 and R20 (test half).
##
## R21 (Medium) -- Finding R2 (`tsymex_163rev_enum_domain.nim`, commit
## `6f2e0ed`) fixed `classifyType`'s enum arm to carry a true `minOrd`/
## `maxOrd`/width/signedness, and R18 (`81040e5`) routed both the classifier
## and the parser through one shared `enumFieldOrdinals`. Every existing test
## of that domain, though, exercises only a TOP-LEVEL enum PARAMETER. The
## mechanism is believed to generalize because array/seq elements and
## discriminators share `allocateSym`'s recursion -- but nothing had proven
## it for:
##   - an enum ARRAY element (`array[N, MyEnum]`)
##   - an enum SEQ element (`seq[MyEnum]`)
##   - an ENUM-TYPED variant discriminator (`tsymex_163audit_wave2.nim`'s W6
##     used a RANGE-ALIAS discriminator, not an enum one -- genuinely
##     different code: enum domains come from `enumFieldOrdinals`, range-alias
##     domains come from `parseRangeBracket`)
##
## OUT OF SCOPE: enum as a plain OBJECT FIELD cannot reach `symexFind` at all
## -- witness reconstruction emits `readUInt8`/`readUInt16` for an enum field,
## which Nim will not implicitly convert back into the enum-typed field, so
## the generated call fails to COMPILE (`docs/issue-0163-opaque-call-taint
## .handoff.md:~525-533`). Not attempted here.
##
## R20 (Medium, test half) -- `classifyType`'s enum arm derives
## `signed := minOrd < 0`. A NEGATIVE-ordinal enum param therefore satisfies
## all three of `promoteSound`'s conditions (`hasRange`, `signed`,
## `fitsBVWindow`) and takes the Z3Int-promotion route instead of BV -- under
## `isOptimised`, which is the DEFAULT (`types.nim`'s `SymexSettings`). No
## wrong verdict is known through this route, but it was untested. Pinned
## below by running the SAME negative-ordinal enum SUT under BOTH `isExact`
## and `isOptimised` and asserting the two AGREE -- the strongest assertion
## available; disagreement would be a genuine finding.
##
## Method note (inherited from #162/#163): every symbolic expectation is
## paired with the same computation run for real in this file.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

type
  Ordering = enum
    roLess = -1
    roEqual = 0
    roGreater = 1

const ExactMode = SymexSettings(integerSemantics: isExact)
const OptMode = SymexSettings(integerSemantics: isOptimised)   ## same as default

# =============================================================================
# R21a -- enum as an ARRAY element.
# =============================================================================

proc arrNegReachable(a: array[2, Ordering]) =
  if ord(a[0]) == -1:
    symexTarget("neg")

proc arrOOB(a: array[2, Ordering]) =
  ## No real `Ordering` value has an ordinal outside [-1, 1]. If the array
  ## element were left unconstrained (the pre-R21-coverage worry: maybe the
  ## domain only ever reached the top-level-param allocation site, not the
  ## per-element recursion into it), this would be falsely satisfiable.
  if ord(a[0]) < -1 or ord(a[0]) > 1:
    symexTarget("oob")

suite "#163 review R21a -- enum ARRAY element carries the same domain":

  test "oracle -- every real Ordering value has ord in [-1, 1]":
    for e in Ordering:
      check ord(e) >= -1 and ord(e) <= 1

  test "a negative-ordinal element is reachable, with a genuine witness":
    let r = symexFind(arrNegReachable, tLabel("neg"))
    check r.status == sxSat
    check Ordering(r.witness[0][0]) == roLess

  test "an out-of-domain element ordinal stays excluded":
    let r = symexFind(arrOOB, tLabel("oob"))
    check r.status == sxUnsat

# =============================================================================
# R21b -- enum as a SEQ element.
# =============================================================================

proc seqNegReachable(s: seq[Ordering]) =
  if s.len > 0 and ord(s[0]) == -1:
    symexTarget("neg")

proc seqOOB(s: seq[Ordering]) =
  if s.len > 0 and (ord(s[0]) < -1 or ord(s[0]) > 1):
    symexTarget("oob")

proc seqOnlyLen(s: seq[Ordering]) =
  ## An "unread" element, mirroring `tsymex_163audit_range_elem.nim`'s
  ## `onlyLen` idiom: `s` is never indexed, only `.len` is compared, so any
  ## element the solver leaves unconstrained on the winning path must still
  ## extract to a legal `Ordering` value under witness reconstruction.
  if s.len == 1:
    symexTarget("hit")

suite "#163 review R21b -- enum SEQ element carries the same domain":

  test "a negative-ordinal element is reachable, with a genuine witness":
    let r = symexFind(seqNegReachable, tLabel("neg"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check Ordering(r.witness[0][0]) == roLess

  test "an out-of-domain element ordinal stays excluded":
    let r = symexFind(seqOOB, tLabel("oob"))
    check r.status == sxUnsat

  test "an unread element's witness is still a legal Ordering value":
    let r = symexFind(seqOnlyLen, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 1
    let v = ord(r.witness[0][0])
    check v >= -1 and v <= 1   ## does not crash/misclassify converting back

# =============================================================================
# R21c -- an ENUM-TYPED (not range-alias) variant discriminator.
# =============================================================================
## `DKind` is deliberately sparse (holes at ordinals 2, 3, 4), so this
## exercises the else-arm-coverage question W6 already proved for a
## RANGE-ALIAS discriminator, now for a discriminator whose domain comes
## from the ENUM path (`enumFieldOrdinals`) instead -- a third, independent
## domain-construction site (`discriminatorDomain` in `runtime.nim`, per
## R12's shared-decision refactor), distinct from both the range-alias
## discriminator (W6) and the plain enum PARAM (R2).
##
## A negative-ordinal enum discriminator was considered and dropped: Nim's
## own compiler rejects it outright ("low(kind) must be 0 for discriminant")
## -- a case-object discriminant must have ordinal floor 0, so R2's
## negative-ordinal shape is not expressible in this position at all. That
## is a Nim language restriction, not a gap in nelli's own domain handling.

type
  DKind = enum
    dkA = 0
    dkB = 1
    dkC = 5

  DObj = object
    case kind: DKind
    of dkA: a: int
    of dkB: b: int
    else: c: int   ## covers the declared dkC plus the holes at 2, 3, 4

proc gatedAArm(v: DObj) =
  if v.kind == dkA:
    if v.a == 9:
      symexTarget("a-hit")

proc gatedElseArm(v: DObj) =
  if v.kind == dkC:
    if v.c == 42:
      symexTarget("else-hit")

suite "#163 review R21c -- enum-typed variant discriminator, both int modes":

  test "oracle -- DKind's real ordinals are 0, 1, 5; each arm holds its field":
    check ord(dkA) == 0
    check ord(dkB) == 1
    check ord(dkC) == 5
    let va = DObj(kind: dkA, a: 9)
    check va.kind == dkA and va.a == 9
    let vc = DObj(kind: dkC, c: 42)
    check vc.kind == dkC and vc.c == 42

  test "the zero-ordinal `of` arm is reachable in both modes":
    check symexFind(gatedAArm, tLabel("a-hit"), ExactMode).status == sxSat
    check symexFind(gatedAArm, tLabel("a-hit"), OptMode).status == sxSat

  test "the else arm (covering the declared dkC and the domain holes) is reachable in both modes":
    check symexFind(gatedElseArm, tLabel("else-hit"), ExactMode).status == sxSat
    check symexFind(gatedElseArm, tLabel("else-hit"), OptMode).status == sxSat

# =============================================================================
# R20 (test half) -- a negative-ordinal enum PARAM under isExact vs isOptimised.
# =============================================================================
## `checkNegOrdinal`/`checkOOB` reuse the same `Ordering` type as the
## already-covered top-level-param position (`tsymex_163rev_enum_domain.nim`,
## `tsymex_163rev_enum_ordinal.nim`), which already implicitly runs under
## `isOptimised` by default -- but neither file explicitly forces `isExact`
## and cross-checks agreement. That comparison is the entire point of R20:
## it is the newly-reachable Z3Int-promotion route (vs. the BV route) under
## the mode users actually get by default, and disagreement between the two
## would itself be the finding.

proc checkNegOrdinal(x: Ordering) =
  if ord(x) == -1:
    symexTarget("neg")

proc checkOOB(x: Ordering) =
  if ord(x) < -1 or ord(x) > 1:
    symexTarget("oob")

suite "#163 review R20 -- negative-ordinal enum param: isExact and isOptimised agree":

  test "oracle -- roLess really is the only ordinal -1 value":
    check ord(roLess) == -1

  test "both modes find the negative ordinal, with a genuine matching witness":
    let rExact = symexFind(checkNegOrdinal, tLabel("neg"), ExactMode)
    let rOpt = symexFind(checkNegOrdinal, tLabel("neg"), OptMode)
    check rExact.status == sxSat
    check rOpt.status == sxSat
    check Ordering(rExact.witness[0]) == roLess
    check Ordering(rOpt.witness[0]) == roLess

  test "both modes agree an out-of-domain ordinal stays excluded":
    check symexFind(checkOOB, tLabel("oob"), ExactMode).status == sxUnsat
    check symexFind(checkOOB, tLabel("oob"), OptMode).status == sxUnsat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 135
