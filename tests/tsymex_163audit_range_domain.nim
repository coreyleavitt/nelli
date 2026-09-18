## Wiring-audit findings W3 and W7 (issue #163) — `dsl_typebridge.classifyType`
## reaches a real verdict for a char-bounded range ALIAS, and a plain enum
## param/field carries the same `[0..ordHigh]` domain a variant discriminator
## already gets.
##
## Every symbolic expectation below is paired with the same computation run
## for real in the same file (the #162 discipline) wherever a real Nim
## computation exists to pair it with. W7's central claim -- that an
## out-of-domain ordinal is unreachable -- has no such computation (Nim's own
## type system never lets a real program construct one); its oracle is the
## complementary fact that every value Nim CAN construct is in-domain.

import std/[unittest, macros, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/dsl_typebridge

## ---------------------------------------------------------------------------
## W3 -- a char-bounded range ALIAS degrades the whole run
##
## `classifyType`'s named-alias arm guarded both bounds with
## `impl[2][1][1].kind in nnkIntLit..nnkUInt64Lit`. `nnkCharLit` sorts BEFORE
## `nnkIntLit` in the `NimNodeKind` enum, so it was never in that range --
## `type Letter = range['a'..'z']` fell through to the `__unsupported:`
## catch-all and degraded the WHOLE run to `sxUnknown`. The inline spelling
## (`proc f(c: range['a'..'z'])`) reaches the structural arm, which has no
## kind guard at all, and classified fine all along.

type
  Letter = range['a'..'z']

# `c > 'm'` (a bare comparison against a char literal) is NOT used here: Nim
# widens a `range[..]`-of-char operand to plain `char` for the comparison via
# an `nnkHiddenSubConv` node, which is a pre-existing, unrelated gap in
# `dsl_parser.nim`'s expression fragment (`feUnsupportedExprKind`) -- present
# for BOTH spellings, nothing to do with the alias-route guard this finding
# fixes. `ord(c)` sidesteps it: `dsl_parser.nim`'s `ord` special-case treats
# an itInt-classified operand as an identity passthrough (the same mechanism
# A7/Rune uses), and a char-range classifies to itInt either way.
proc fInline(c: range['a'..'z']) =
  if ord(c) > ord('m'):
    symexTarget("upperhalf")

proc fAlias(c: Letter) =
  if ord(c) > ord('m'):
    symexTarget("upperhalf")

proc boundInline(c: range['a'..'z']) =
  if ord(c) > ord('z'):
    symexTarget("outofbounds")

proc boundAlias(c: Letter) =
  if ord(c) > ord('z'):
    symexTarget("outofbounds")

suite "#163 W3 -- a char-range ALIAS reaches the same verdict as inline":

  test "the oracle -- Nim char-range comparisons over the declared bounds":
    proc rt(c: range['a'..'z']): bool = ord(c) > ord('m')
    check rt('n') == true
    check rt('a') == false

  test "the inline spelling reaches a real verdict":
    let r = symexFind(fInline, tLabel("upperhalf"))
    check r.status == sxSat

  test "the alias spelling used to degrade to sxUnknown -- now matches inline":
    ## RED (pre-fix): sxUnknown (feUnsupportedParamType) -- the alias route
    ## fell through the literal-kind guard into the `__unsupported:` catch-all
    ## before ever reaching `rangeBaseType`.
    let r = symexFind(fAlias, tLabel("upperhalf"))
    check r.status == sxSat

  test "both spellings classify identically -- declared bounds still tighten":
    ## If the alias route classified the range differently from the inline
    ## route (e.g. a different width or signedness), the two would not agree
    ## on whether a value past the declared upper bound is reachable. Both
    ## must answer sxUnsat here: `range['a'..'z']` cannot exceed 'z'.
    check symexFind(boundInline, tLabel("outofbounds")).status == sxUnsat
    check symexFind(boundAlias, tLabel("outofbounds")).status == sxUnsat

  # NOTE: no version-floor test here. Per the control loop this fix does NOT
  # bump `symexWalkerVersion` -- that lands in a single shared bump covering
  # every agent's semantic change in this round. A floor pin belongs with
  # that bump, not here.

## ---------------------------------------------------------------------------
## W7 -- plain enum params/fields get no domain constraint
##
## The enum arm returned `unranged(tInt(bits, signed = false))`, with a
## comment reasoning that attaching `hasRange` would route an unsigned reader
## into promotion. #162 made that reasoning obsolete: `promoteSound`
## (`runtime.nim`) now requires `p.ty.signed`, and an enum's lifted `IRType`
## is always `signed = false` -- so `hasRange` on an enum can never reach
## `promoteSound` regardless. Left unranged, out-of-domain ordinals were
## model-reachable: `e != A and e != B` over a two-value enum was falsely
## `sxSat`. Variant DISCRIMINATORS already get an ordinal disjunction; plain
## enum values got nothing -- that asymmetry is the finding.

type
  TwoVal = enum
    tvA, tvB

  Cfg = object
    mode: TwoVal

  # A sparse/holed enum: ordinals 0 and 3, with 1 and 2 unoccupied. The fix's
  # `[0..maxOrd]` is a sound REFINEMENT here, not exact -- it excludes 4+ but
  # still admits the 1/2 holes.
  Sparse = enum
    sA = 0
    sB = 3

proc outOfDomain(e: TwoVal) =
  if e != tvA and e != tvB:
    symexTarget("oob")

proc reachesB(e: TwoVal) =
  if e == tvB:
    symexTarget("is_b")

proc sparseHole(e: Sparse) =
  if e != sA and e != sB:
    symexTarget("hole")

proc sparseBeyond(e: Sparse) =
  if ord(e) > 3:
    symexTarget("beyond")

# ---------------------------------------------------------------------------
# The FIELD route, checked directly against the classifier rather than
# through `symexFind`. `Cfg.mode` (a plain, non-discriminator enum field) hits
# a SEPARATE, pre-existing gap in `symex.nim`'s witness reconstruction: a
# nominal object's witness is rebuilt via a real `nnkObjConstr` (e.g.
# `Cfg(mode: <reader-expr>)`), and an enum-typed field's reader expression is
# the plain unsigned-int reader (`readUInt8`/`readUInt16` -- enums have no
# dedicated reader; see `primTyAndReader`), which Nim does NOT implicitly
# convert to the enum type the way it implicitly range-checks an int literal
# into a `range[..]` field. That is orthogonal to W3/W7 -- it exists whether
# or not the field carries `hasRange` -- and is out of scope for this file's
# two findings (both confined to `dsl_typebridge.nim`). It blocks calling
# `symexFind` on ANY proc taking an object with a plain enum field at all, so
# the field claim is checked here at the classifier level instead: does
# `classifyFieldType` (the actual function `classifyObjectRecordFields` calls
# for every plain field, per `dsl_typebridge.nim:~259`) attach the same
# range a bare top-level enum param gets?
macro classifyEnumTypedesc(T: typedesc): (bool, int64, int64, bool) =
  ## Mirrors `tsymex_h_stepA_nominalid.nim`'s `nominalIdOfType` idiom: peel
  ## the `typeDesc[X]` wrapper `typedesc` params arrive in, then classify the
  ## bare symbol exactly as the enum arm's caller (a top-level param) would.
  var inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst = inst[1]
  let cls = classifyType(inst)
  newTree(nnkTupleConstr, newLit(cls.ty.hasRange), newLit(cls.ty.rangeLo),
          newLit(cls.ty.rangeHi), newLit(cls.ty.signed))

macro classifyEnumField(x: typed): (bool, int64, int64, bool) =
  ## `x` is a field-access expression (`cfgVal.mode`) -- the same NimNode
  ## shape `classifyObjectRecordFields` passes to `classifyFieldType` for a
  ## plain `nnkIdentDefs` member's type, one level removed (there it is the
  ## DECLARED type node; here it is a typed access expression whose
  ## `getTypeInst` resolves to the same enum symbol -- `classifyFieldType`
  ## reads through `.getTypeInst` either way, so both reach the identical
  ## enum arm in `classifyType`).
  let cls = classifyFieldType(x)
  newTree(nnkTupleConstr, newLit(cls.ty.hasRange), newLit(cls.ty.rangeLo),
          newLit(cls.ty.rangeHi), newLit(cls.ty.signed))

const twoValParamInfo = classifyEnumTypedesc(TwoVal)
var cfgProbe: Cfg
const twoValFieldInfo = classifyEnumField(cfgProbe.mode)

static:
  doAssert twoValParamInfo == twoValFieldInfo

suite "#163 W7 -- plain enum params carry a domain constraint":

  test "the oracle -- every real TwoVal value is tvA or tvB":
    ## Ground truth: Nim's type system never lets a real program construct an
    ## enum value outside its declared constants. The symbolic engine's job
    ## is to stop pretending otherwise.
    for e in TwoVal:
      check e == tvA or e == tvB

  test "an out-of-domain enum ordinal is no longer model-reachable":
    ## RED (pre-fix): sxSat -- the free BV8 backing `e` could take any value
    ## in [0, 255], not just {0, 1}.
    let r = symexFind(outOfDomain, tLabel("oob"))
    check r.status == sxUnsat

  test "a legal ordinal is still reachable -- not an over-constraint":
    ## The complement: the fix must not ban legal values either.
    let r = symexFind(reachesB, tLabel("is_b"))
    check r.status == sxSat

  test "the classifier attaches [0, maxOrd] to a bare TwoVal param":
    ## RED (pre-fix): (false, 0, 0, false) -- `unranged` never sets hasRange.
    check twoValParamInfo == (true, 0'i64, 1'i64, false)

  test "an enum-typed FIELD gets the identical range from the classifier":
    ## The finding calls out fields as well as params: an extracted
    ## out-of-domain ordinal for a field flows into witness construction the
    ## same way a param's does. `classifyFieldType` falls through to the same
    ## `classifyType` enum arm for a plain (non-ref) field, and `allocateSym`'s
    ## `itInt` arm asserts `bvRangeConds` off `ty.hasRange` for every int
    ## allocation -- so once the classifier stops declining, the field route
    ## is free; no separate field-plumbing fix is needed (unlike #162, which
    ## needed one). End-to-end confirmation via `symexFind` is blocked by a
    ## separate, pre-existing gap in `symex.nim`'s enum-field witness
    ## reconstruction (see the comment above `classifyEnumField`) -- this
    ## checks the mechanism the fix actually relies on directly.
    check twoValFieldInfo == twoValParamInfo
    check twoValFieldInfo == (true, 0'i64, 1'i64, false)

  test "sparse enum -- the hole is a known, recorded imprecision":
    ## `Sparse` occupies ordinals {0, 3}; the fix's range is [0, 3]. Ordinals
    ## 1 and 2 are holes: illegal enum values that the sound-refinement
    ## range does not exclude. This must stay sxSat both before and after
    ## the fix -- it is not a regression, it is the documented limitation.
    let r = symexFind(sparseHole, tLabel("hole"))
    check r.status == sxSat

  test "sparse enum -- a genuinely out-of-range ordinal IS excluded":
    ## The complement that proves the refinement still does real work: an
    ## ordinal beyond maxOrd (here, past 3) is excluded even though the enum
    ## is sparse. RED (pre-fix): sxSat (fully free BV8, e.g. ord 200).
    let r = symexFind(sparseBeyond, tLabel("beyond"))
    check r.status == sxUnsat

  # NOTE: no version-floor test here -- see the matching note in the W3
  # suite above.

suite "#163 audit -- walker version pin":

  test "walker version floor >= 134 (the audit remediation's single bump)":
    ## One bump covers W2/W3/W4/W6/W7 -- all verdict changes. Compared
    ## numerically, not lexicographically: `"1000" < "133"` as strings.
    check parseInt(symexWalkerVersion) >= 134
