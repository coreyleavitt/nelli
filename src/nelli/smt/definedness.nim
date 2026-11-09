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
## * `runtime.drainConvFloatToIntFresh`: `convert/floatToInt` (K10a-float);
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

type
  ArithOp* = enum                     ## the operation a row is about
    aoAdd, aoSub, aoMul               ## signed overflow
    aoDiv, aoMod                      ## zero divisor, `low(T)` by `-1`
    aoRead                            ## a read of a value no write reached
    aoOrder                           ## `<`, `<=` over addresses
    aoGrow                            ## a resize while an element address lives
    aoCall                            ## a call through a declared contract
    aoConvert                         ## a float converted to an integer type
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
    ocFloatToInt                      ## `int(f)`, `int32(f)`, `uint8(f)`: NaN,
                                      ## infinite or out of the target's range
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
      "float -> int of NaN, an infinity or a value whose truncation does not " &
      "fit the target: Nim 2.2.10 emits a plain C cast and range-checks the " &
      "cast value (a tautology), so no check profile raises and the cast is " &
      "undefined. Inside a `range` target the converted value's own range " &
      "check still raises, and that is a separate fork"))

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

func convertDefinedness*(p: DefProfile): Definedness =
  ## The float -> int drain's read: the answer of the admitted `dsConvert`
  ## row for the build's profile (undefined under every one).
  let a = admitDefined(aoConvert, ocFloatToInt, dsConvert)
  doAssert a.admitted, "definedness: no dsConvert row"
  a.payload[p]

func readUb*(): UbKind =
  ## The kind of an uninitialised read, from its row (`dsRead`).
  let a = admitDefined(aoRead, ocUninitialised, dsRead)
  doAssert a.admitted
  a.payload[dpChecked].ub
