## RFC-0016 K10a-axis (sections 8.1 and 9.1 item 1) -- the definedness axis.
##
## One `AxisTable` over the ADM-1 machinery: `(operation, operand class)` to
## what the C the build compiles makes of it. A row answers by build profile
## (`DefProfile`): *defined* (exact, including a wrap the profile defines),
## *Defect* (Nim's checked operation: the existing raise fork) or *undefined*
## (a `UbKind`, decided at the operation by `haltUndefined`). A row the walker
## does not answer is a refused one and a `never` row where the behaviour stays
## as it is.
##
## The decision sites read it:
##
## * `runtime.lowerArith` and `depositSignedOverflow`: the `add`/`sub`/`mul`,
##   `div`/`mod` zero-divisor and `low(T) by -1` rows (`definedness`);
## * `runtime.unwrittenUb`: the `read/uninitialised` row;
## * `runtime.refEqOrder`: `order/pointer` (STY-03, `never`);
## * the index sites (`walkIndexArm`, `walkIndexAssignArm`, the string and
##   `pop` arms and the two raise-fork drains): `index/unchecked` (PRC-07);
## * `runtime.drainConvFloatToIntFresh`: `convert/floatToInt` and `convert/floatToIntVia` (K10a-float);
## * `dsl_parser`'s stale element pointer marker: `grow/elemAddr` (STY-07,
##   `never`);
## * `dsl_parser.withCheckDeclines`: `call/noalias`, the routine that declares
##   a parameter `restrict` (`noalias` is an `OperandClass`, K10a-axis; the
##   pragma axis K3c lists the pragma itself).
##
## Unsigned `+`, `-`, `*` have no row: they are modular in Nim and C, there is
## no decision to make. The default build is a profile of each row, not prose.
import std/options
import ./admission
import ./errorkind
import ./magic_rows   ## RFC-0016 ADM-IR: `MagicModel`, the magic axis's proof type

type
  ArithOp* = enum                     ## the operation a row is about
    aoAdd, aoSub, aoMul               ## signed overflow
    aoDiv, aoMod                      ## zero divisor, `low(T)` by `-1`
    aoRead                            ## a read of a value no write reached
    aoOrder                           ## `<`, `<=` over addresses
    aoGrow                            ## a resize while an element address lives
    aoCall                            ## a call through a declared contract
    aoConvert                         ## a float converted to an integer type
    aoIndex                           ## an element access with no bound check
    aoConv                            ## a `ref` object down-conversion
    aoField                           ## a variant field access
  OperandClass* = enum                ## what the operand is, for this op
    ocSignedWide                      ## signed, 32 or 64 bits
    ocSignedNarrow                    ## signed, 8 or 16 bits: C computes in `int`
    ocZeroDivisorSigned
    ocZeroDivisorUnsigned
    ocLowByMinusOneWide               ## `low(T) div/mod -1` at 32 or 64 bits
    ocLowByMinusOneNarrow             ## the same at 8 or 16 bits
    ocUninitialised                   ## a `{.noinit.}` local, no write yet
    ocPointer                         ## a `ptr` or `ref` value
    ocElemAddr                        ## `addr s[i]` of a seq
    ocNoalias                         ## a parameter declared `{.noalias.}`
    ocFloatToInt                      ## `int(f)`, `int64(f)`, `uint8(f)`: the
                                      ## C cast goes straight to the target;
                                      ## NaN, infinite or out of ITS range
    ocFloatToIntVia                   ## `int8/16/32(f)`: Nim casts through a
                                      ## wider signed C integer (`floatToIntLowering`);
                                      ## undefined outside THAT type's range,
                                      ## a defined wrap inside it
    ocOpaqueBody                      ## RFC-0016 K10b: an opaque call whose
                                      ## body the defect scan cannot read
                                      ## (foreign, a closure, a method, too
                                      ## deep): what it does is not modelled
    ocUncheckedAccess                 ## RFC-0016 PRC-07: an element access
                                      ## Nim emits with no check (an array
                                      ## indexed by its own `range`/enum type
                                      ## under `rangeChecks: off`; any index
                                      ## under `boundChecks: off`)
    ocObjDowncast                     ## RFC-0016 PRC-07: `Derived(b)` with no
                                      ## `isObjDisplayCheck` (`objChecks: off`)
    ocInactiveBranch                  ## RFC-0016 PRC-07: a variant field read
                                      ## or written outside its branch with no
                                      ## `fieldChecks`, where C++ calls it
                                      ## undefined
    ocInactiveBytes                   ## the same access where C defines it as
                                      ## the overlapping bytes (the c backend)
  DefProfile* = enum                  ## the build's arithmetic
    dpChecked                         ## Nim's overflow and zero checks are on
    dpUnchecked                       ## checks off, the C operation as is
    dpFwrapv                          ## checks off and `-fwrapv` (K5a)
  DefKind* = enum
    dkDefined, dkDefect, dkUndefined
  Definedness* = object
    kind*: DefKind
    ub*: UbKind = ubUnsignedDivZero   ## read only when `dkUndefined`; a
                                      ## default, the range omits 0
  DefRule* = array[DefProfile, Definedness]
  DefSite* = enum
    dsArith                           ## `lowerArith`
    dsRead                            ## `unwrittenUb`
    dsOrder                           ## the ref/ptr comparison
    dsGrow                            ## the stale element pointer marker
    dsRoutine                         ## a routine's parameters
    dsConvert                         ## the float -> int conversion drain
    dsOpaque                          ## RFC-0016 K10b: the opaque-call scan
    dsIndex                           ## RFC-0016 PRC-07: the index sites
    dsConv                            ## RFC-0016 PRC-07: the object conversion
    dsField                           ## RFC-0016 PRC-07: the variant field sites
  DefKey = tuple[key: string, row: Row[DefSite, DefRule]]

func defined(): Definedness = Definedness(kind: dkDefined)
func defect(): Definedness = Definedness(kind: dkDefect)
func undef(k: UbKind): Definedness = Definedness(kind: dkUndefined, ub: k)

func opKey(op: ArithOp): string =
  case op
  of aoAdd: "add"
  of aoSub: "sub"
  of aoMul: "mul"
  of aoDiv: "div"
  of aoMod: "mod"
  of aoRead: "read"
  of aoOrder: "order"
  of aoGrow: "grow"
  of aoCall: "call"
  of aoConvert: "convert"
  of aoIndex: "index"
  of aoConv: "conv"
  of aoField: "field"

func classKey(c: OperandClass): string =
  case c
  of ocSignedWide: "signedWide"
  of ocSignedNarrow: "signedNarrow"
  of ocZeroDivisorSigned: "zeroDivisorSigned"
  of ocZeroDivisorUnsigned: "zeroDivisorUnsigned"
  of ocLowByMinusOneWide: "lowByMinusOneWide"
  of ocLowByMinusOneNarrow: "lowByMinusOneNarrow"
  of ocUninitialised: "uninitialised"
  of ocPointer: "pointer"
  of ocElemAddr: "elemAddr"
  of ocNoalias: "noalias"
  of ocFloatToInt: "floatToInt"
  of ocFloatToIntVia: "floatToIntVia"
  of ocOpaqueBody: "opaqueBody"
  of ocUncheckedAccess: "unchecked"
  of ocObjDowncast: "objDowncast"
  of ocInactiveBranch: "inactiveBranch"
  of ocInactiveBytes: "inactiveBytes"

func defKey*(op: ArithOp; c: OperandClass): string =
  opKey(op) & "/" & classKey(c)

func arith(op: ArithOp; c: OperandClass; checked, unchecked, fwrapv:
           Definedness; note: string): DefKey =
  (defKey(op, c),
   modelled[DefSite, DefRule]([checked, unchecked, fwrapv], {dsArith}, note))

func defRows(): seq[DefKey] =
  for op in [aoAdd, aoSub, aoMul]:
    result.add arith(op, ocSignedWide, defect(), undef(ubSignedOverflow),
      defined(),
      "signed 32 or 64 bit overflow: Nim's OverflowDefect when checked, " &
      "undefined in C otherwise, a defined wrap under -fwrapv")
    result.add arith(op, ocSignedNarrow, defect(), defined(), defined(),
      "signed 8 or 16 bit: C computes in the promoted `int` and the " &
      "narrowing wraps, so only Nim's own check can object")
  for op in [aoDiv, aoMod]:
    result.add arith(op, ocZeroDivisorUnsigned, undef(ubUnsignedDivZero),
      undef(ubUnsignedDivZero), undef(ubUnsignedDivZero),
      "Nim has no check on an unsigned divisor; the C division is undefined")
    result.add arith(op, ocZeroDivisorSigned, defect(),
      undef(ubSignedDivZero), undef(ubSignedDivZero),
      "Nim's zero check belongs to the overflow checks: with them off the " &
      "C division is undefined")
  result.add arith(aoDiv, ocLowByMinusOneWide, defect(),
    undef(ubSignedOverflow), undef(ubSignedOverflow),
    "`low(T) div -1` at 32 or 64 bits: Nim's OverflowDefect when checked, " &
    "an undefined C division otherwise (-fwrapv does not cover it)")
  result.add arith(aoMod, ocLowByMinusOneWide, undef(ubIntMinModMinusOne),
    undef(ubIntMinModMinusOne), undef(ubIntMinModMinusOne),
    "`low(T) mod -1` at 32 or 64 bits: Nim has no check, the C division " &
    "is undefined")
  result.add arith(aoDiv, ocLowByMinusOneNarrow, defect(), defined(),
    defined(), "`low(T) div -1` at 8 or 16 bits: computed in `int`, wraps back")
  result.add arith(aoMod, ocLowByMinusOneNarrow, defined(), defined(),
    defined(), "`low(T) mod -1` at 8 or 16 bits: computed in `int`, is 0")
  result.add (defKey(aoRead, ocUninitialised),
    modelled[DefSite, DefRule](
      [undef(ubIndeterminateRead), undef(ubIndeterminateRead),
       undef(ubIndeterminateRead)], {dsRead},
      "a `{.noinit.}` local read before any write holds whatever the stack " &
      "held: the path is tainted, not halted"))
  result.add (defKey(aoOrder, ocPointer),
    refused[DefSite, DefRule](some(feUnsupportedOp),
      "STY-03: the order of two addresses is the allocator's, not a value " &
      "of the program; `<` over `ptr` is declined", iNever, nrUnobservable))
  result.add (defKey(aoGrow, ocElemAddr),
    refused[DefSite, DefRule](some(feUnsupportedOp),
      "STY-07: `addr s[i]` then a resize of `s`: Nim may move the elements " &
      "and the pointer then names freed memory; whether it does depends on " &
      "the capacity, so the use after a resize is declined", iNever,
      nrUnobservable))
  result.add (defKey(aoCall, ocNoalias),
    refused[DefSite, DefRule](some(feUnsupportedOp),
      "a `{.noalias.}` parameter is C `restrict`: an access through another " &
      "pointer to the same object is undefined, and the walk does not " &
      "track which parameters may alias. A routine that declares one beside " &
      "another pointer-like parameter is declined"))

  result.add (defKey(aoConvert, ocFloatToInt),
    modelled[DefSite, DefRule](
      [undef(ubFloatToIntRange), undef(ubFloatToIntRange),
       undef(ubFloatToIntRange)], {dsConvert},
      "float -> int64/int or an unsigned target: Nim 2.2.10 emits a plain C " &
      "cast straight to the target and range-checks the cast value (a " &
      "tautology), so no check profile raises. NaN, an infinity or a value " &
      "whose truncation does not fit the target is undefined. Inside a " &
      "`range` target the converted value's own range check still raises, " &
      "and that is a separate fork"))
  result.add (defKey(aoConvert, ocFloatToIntVia),
    modelled[DefSite, DefRule](
      [undef(ubFloatToIntRange), undef(ubFloatToIntRange),
       undef(ubFloatToIntRange)], {dsConvert},
      "float -> int8/16/32: Nim 2.2.10 emits `(NI8)((NI64)f)` (through int32 " &
      "for a float32 operand to int8/16). The inner cast is undefined for " &
      "NaN, an infinity or a truncation outside the INTERMEDIATE type; a " &
      "value inside it that does not fit the target converts to the target " &
      "by the C integer conversion, which gcc defines as modulo 2^n " &
      "(implementation-defined, documented) and is not undefined"))
  result.add (defKey(aoCall, ocOpaqueBody),
    modelled[DefSite, DefRule](
      [undef(ubTailUnverified), undef(ubTailUnverified),
       undef(ubTailUnverified)], {dsOpaque},
      "RFC-0016 K10b: an opaque call whose body the defect scan cannot read " &
      "(foreign code with no row, a closure, a method, a re-raise, a body " &
      "deeper than the scan reads) may do anything, undefined operations " &
      "included. Under the whole-run gate it answers `may be undefined`; the " &
      "explore walk forks its Defects as before and walks on"))

  result.add (defKey(aoIndex, ocUncheckedAccess),
    modelled[DefSite, DefRule](
      [undef(ubArrayOutOfBounds), undef(ubArrayOutOfBounds),
       undef(ubArrayOutOfBounds)], {dsIndex},
      "RFC-0016 PRC-07: Nim emits no bound check for an array indexed by " &
      "its own `range`/enum type (a checked build bounds the VALUE at the " &
      "conversion instead, and `rangeChecks: off` removes that), nor for any " &
      "`s[i]` / `a[i]` under `boundChecks: off`. The access is a plain C " &
      "subscript: outside the container it reads or writes memory the " &
      "object does not own, which is undefined. Whether a site is unchecked " &
      "is decided by the build's own option, so the row answers the same " &
      "under every profile"))

  result.add (defKey(aoConv, ocObjDowncast),
    modelled[DefSite, DefRule](
      [undef(ubInvalidObjConversion), undef(ubInvalidObjConversion),
       undef(ubInvalidObjConversion)], {dsConv},
      "RFC-0016 PRC-07: `Derived(b)` of a `ref` whose dynamic type is not a " &
      "`Derived`. A checked build raises `ObjectConversionDefect` " &
      "(`isObjDisplayCheck`); `objChecks: off` removes it, the conversion " &
      "succeeds, and the reference is used as a type it is not: an access " &
      "through an incompatible type, past the allocation when `Derived` is " &
      "the larger. Undefined whichever the profile"))
  result.add (defKey(aoField, ocInactiveBranch),
    modelled[DefSite, DefRule](
      [undef(ubInactiveVariantField), undef(ubInactiveVariantField),
       undef(ubInactiveVariantField)], {dsField},
      "RFC-0016 PRC-07: with `fieldChecks: off` a variant field is a plain " &
      "union member access. Outside its branch it reads (or writes) a member " &
      "that is not the active one, which C++ calls undefined (cpp backend). " &
      "No sanitizer sees it and gcc defines it as punning, so the cell has " &
      "no native pin"))
  result.add (defKey(aoField, ocInactiveBytes),
    refused[DefSite, DefRule](some(feUnsupportedOp),
      "RFC-0016 PRC-07 (`fieldChecksOffLayout`): with `fieldChecks: off` on " &
      "the c backend the same access is defined, as the overlapping bytes of " &
      "the active branch (C11 6.5.2.3 note 95). The walker keeps one slot " &
      "per field and has no per-target byte layout of a variant, so the " &
      "wrong-branch side is declined path-locally"))

const definednessTable* = axisTable[DefSite, DefRule](axDefinedness, defRows())

func admitDefined*(op: ArithOp; c: OperandClass; site: DefSite):
    Admit[DefRule] =
  ## Whether the walker answers `(op, c)` at `site`; an absent key is a
  ## decline with no kind of its own (`none`).
  definednessTable.admit(defKey(op, c), site, absent = none(SymexErrorKind))

func definedness*(op: ArithOp; c: OperandClass; p: DefProfile): Definedness =
  ## The arithmetic sites' read: the answer of an admitted `dsArith` row.
  ## A row that is not there is a compile-time-visible bug in the caller, not
  ## a decline: the sites ask only for pairs the table lists.
  let a = admitDefined(op, c, dsArith)
  doAssert a.admitted, "definedness: no dsArith row " & defKey(op, c)
  a.payload[p]

func arithClass*(signedWide: bool): OperandClass =
  if signedWide: ocSignedWide else: ocSignedNarrow

func ubOf*(d: Definedness): Option[UbKind] =
  if d.kind == dkUndefined: some(d.ub) else: none(UbKind)

type FloatToIntLowering* = object
  ## The C a float -> int conversion compiles to (K10a-float; Nim 2.2.10, read
  ## from the generated C and checked with UBSan in `tsymex_0016_k10c_ubsan`).
  cls*: OperandClass       ## the row: `ocFloatToInt` or `ocFloatToIntVia`
  via*: int                ## the width of the type the value is undefined
                           ## outside of: the target's own when direct, else
                           ## the signed intermediate

func floatToIntLowering*(srcWidth, tgtWidth: int; tgtSigned: bool):
    FloatToIntLowering =
  ## `int64(f)`, `int(f)` and every unsigned target are one C cast to the
  ## target. A signed target narrower than the operand's natural integer is
  ## `(NI8)((NI64)f)`: int64 for a `float64` operand, int32 for a `float32`
  ## one (`float32 -> int32` is direct).
  let natural = if srcWidth == 32: 32 else: 64
  if tgtSigned and tgtWidth < natural:
    FloatToIntLowering(cls: ocFloatToIntVia, via: natural)
  else:
    FloatToIntLowering(cls: ocFloatToInt, via: tgtWidth)

func convertDefinedness*(c: OperandClass; p: DefProfile): Definedness =
  ## The float -> int drain's read: the answer of the admitted `dsConvert`
  ## row of class `c` for the build's profile (undefined under every one).
  let a = admitDefined(aoConvert, c, dsConvert)
  doAssert a.admitted, "definedness: no dsConvert row " & defKey(aoConvert, c)
  a.payload[p]

func opaqueBodyDefinedness*(p: DefProfile): Definedness =
  ## RFC-0016 K10b. The opaque-call scan's read for a body it cannot see:
  ## the answer of the admitted `dsOpaque` row (undefined under every
  ## profile, `ubTailUnverified`).
  let a = admitDefined(aoCall, ocOpaqueBody, dsOpaque)
  doAssert a.admitted, "definedness: no dsOpaque row"
  a.payload[p]

func uncheckedIndexUb*(): UbKind =
  ## RFC-0016 PRC-07. The kind of an out-of-container access at a site Nim
  ## emits without a bound check: the admitted `dsIndex` row, the same under
  ## every profile.
  let a = admitDefined(aoIndex, ocUncheckedAccess, dsIndex)
  doAssert a.admitted, "definedness: no dsIndex row"
  a.payload[dpChecked].ub

func objDowncastUb*(): UbKind =
  ## RFC-0016 PRC-07. The kind of a `ref` down-conversion that fails its type
  ## test in a build with `objChecks` off: the admitted `dsConv` row.
  let a = admitDefined(aoConv, ocObjDowncast, dsConv)
  doAssert a.admitted, "definedness: no dsConv row"
  a.payload[dpChecked].ub

func inactiveFieldUb*(): UbKind =
  ## RFC-0016 PRC-07. The kind of a variant field access outside its branch
  ## with `fieldChecks` off, on the cpp backend (the `dsField` row).
  let a = admitDefined(aoField, ocInactiveBranch, dsField)
  doAssert a.admitted, "definedness: no dsField row"
  a.payload[dpChecked].ub

func readUb*(): UbKind =
  ## The kind of an uninitialised read, from its row (`dsRead`).
  let a = admitDefined(aoRead, ocUninitialised, dsRead)
  doAssert a.admitted
  a.payload[dpChecked].ub

# ---------------------------------------------------------------------------
# RFC-0016 ADM-IR: the opaque-call scan is a proof the IR demands.
# ---------------------------------------------------------------------------

type
  OpaqueScan* = object
    ## What the defect scan found in an opaque call's body: the `Defect`
    ## names the explore walk forks and the undefined-behaviour kinds the
    ## whole-run gate reads (`IRStmt.opaqueDefects`, `opaqueUndefined`).
    ## The fields are private to this module, so a kind enters only through
    ## an admitted definedness proof (`noteUndefined`) and a magic's defect
    ## only through an admitted magic proof (`noteMagicDefect`): the IR
    ## constructor `mkOpaqueCall` takes the scan, so a parser arm that
    ## answers either axis without its table does not type-check.
    undef: set[UbKind]
    defs: seq[string]

func ubMaskOf*(ks: set[UbKind]): int =
  ## RFC-0016 K10b. A `set[UbKind]` as a bit mask over `ord(k) - ord(low)`:
  ## the form the parser's IR emit writes `IRStmt.opaqueUndefined` in (a set
  ## literal of a range type does not round-trip through `newLit`; the
  ## W1-d3 `static` pin keeps the range under 30 members).
  for k in ks: result = result or (1 shl (ord(k) - ord(low(UbKind))))

func ubSetOf*(mask: int): set[UbKind] =
  ## RFC-0016 K10b. `ubMaskOf`'s inverse.
  for k in low(UbKind) .. high(UbKind):
    if ((mask shr (ord(k) - ord(low(UbKind)))) and 1) == 1: result.incl k

const unscanned* = OpaqueScan()
  ## The scan of a call whose body the parser does not read: nothing found.
  ## The two expression-position and annotation-violation arms that never
  ## ran the scan name it, and `tests/tsymex_0016_admir.nim` counts the uses.

func undefinedKinds*(s: OpaqueScan): set[UbKind] = s.undef
func defectNames*(s: OpaqueScan): seq[string] = s.defs

proc noteUndefined*(s: var OpaqueScan; a: Admit[DefRule]; p: DefProfile) =
  ## The body may reach the undefined behaviour the admitted row `a` says it
  ## is under profile `p`. A declined row, or one that is not undefined
  ## there, is a bug in the caller.
  doAssert a.admitted, "noteUndefined: " & a.decline[1]
  let u = ubOf(a.payload[p])
  doAssert u.isSome, "noteUndefined: " & render(a.cell) & " is not undefined under " & $p
  s.undef.incl u.get

proc noteMagicDefect*(s: var OpaqueScan; a: Admit[MagicModel]; name: string) =
  ## A call of the magic row `a` raises the `Defect` `name`. The row must be
  ## admitted (a defect site of the magic axis).
  doAssert a.admitted, "noteMagicDefect: " & a.decline[1]
  if name notin s.defs: s.defs.add name

proc noteDefect*(s: var OpaqueScan; name: string) =
  ## A `Defect` the scan names from the syntax, not a magic: an index, a
  ## field of a variant, a range-checked conversion, a `raise`, or `anyDefect`
  ## for what it cannot read. No axis keys these.
  if name notin s.defs: s.defs.add name

func replayScan*(defects: seq[string]; mask: int): OpaqueScan =
  ## The IR emit's rebuild of a scan it already read (the macro-time
  ## `IRStmt` is written out as constructor calls). The parser's emit is
  ## the only caller; `tests/tsymex_0016_admir.nim` counts the uses.
  OpaqueScan(undef: ubSetOf(mask), defs: defects)
