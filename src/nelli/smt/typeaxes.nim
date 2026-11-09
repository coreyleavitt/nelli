## RFC-0016 K3a (section 8.1) -- the type-class axis and the type x memory-op
## axis.
##
## Two `AxisTable`s over the ADM-1 machinery, and the verbs that read them.
##
## * `typeClassTable` (`typeclass:`): one row per `NimTypeKind`, keyed by the
##   kind's name (`int32`, `cstring`, `sequence`), plus the type features the
##   walker declines or models by name (`variant/omittedField/Table`,
##   `array/enumIndex`) and the `never` cells of STY-04 and STY-06 (`owned`,
##   `atomic`, `float128`, `float/sNaNPayload`). `admitTypeClass(kind,
##   tcByValueFormal)` is the S8cq by-value allowlist: `dsl_parser.
##   typeCopiedByValue` reads the payload instead of a `case` of its own. A
##   kind with no listed model is a refused `iModel` row, so it is open work in
##   the ledger and a decline here.
## * `typeOpTable` (`typeop:`): memory operations by IR type kind, keyed
##   `<op>/<kind>` (`letCursor/variant`). `holdsSharedMemory` reads the
##   `letCursor` rows. The classification is an exhaustive `case` over
##   `IRTypeKind`, so a new kind is a compile error until it has an answer, and
##   an answer the table lacks reads as "shares memory" (fail closed): the old
##   function ended in `else: false`, which is how a variant holding a seq arm
##   passed as a value (B-04).
##
## The `fieldDefault/*` cells (W-12, K3b) and the conversion, comparison and
## set-membership cells the K2-0 probes name (`cast/int32`, `ptr/lt`,
## `set/char/in`) are not memory operations on a type; they belong to K3b and
## to the construct and definedness axes.
import std/[macros, options, strutils]
import ./admission
import ./errorkind
import ./types

type
  TypeClassSite* = enum
    tcByValueFormal     ## `typeCopiedByValue`: a by-value formal of this kind
    tcFeature           ## a named feature of a type, read by no dispatch
                        ## point: classifyType is a chain of guards (K2c)
  TypeClassModel* = enum
    tmLeaf              ## the value is its own bytes; nothing to look through
    tmStructural        ## copied when its components are (distinct, object, tuple)
    tmNone              ## a feature row: no by-value meaning

  MemOp* = enum
    moLetCursor         ## `let c = lv`: a copy, or a view of lv's memory
  TypeOpSite* = enum
    toHoldsSharedMemory
  MemShare* = enum
    msValue             ## the value is the whole of it: the `let` is a copy
    msShared            ## owns heap memory a `let` may view (seq, string, ...)
    msComponents        ## decided by the components
  OpKey = tuple[key: string, row: Row[TypeOpSite, MemShare]]
  ClassKey = tuple[key: string, row: Row[TypeClassSite, TypeClassModel]]

# ---------------------------------------------------------------------------
# The type-class axis.
# ---------------------------------------------------------------------------

func lowerLead(s: string): string =
  s[0 ..< 1].toLowerAscii & s[1 .. ^1]

func classKey*(k: NimTypeKind): string =
  ## `ntyInt32` -> `int32`, `ntyCString` -> `cstring`, `ntyOpenArray` ->
  ## `openArray`: the name without `nty`, its leading capitals lowered.
  let s = ($k)[3 .. ^1]
  var run = 0
  while run < s.len and s[run] in {'A' .. 'Z'}: inc run
  var upperAfter = false
  for i in run ..< s.len:
    if s[i] in {'A' .. 'Z'}: upperAfter = true
  if run >= 2 and not upperAfter: s.toLowerAscii
  else: lowerLead(s)

const
  byValueLeaf = {ntyBool, ntyChar, ntyEnum, ntyRange, ntyRef, ntyPtr,
                 ntyPointer, ntyProc, ntyCString} +
                {ntyInt .. ntyInt64} + {ntyUInt .. ntyUInt64} +
                {ntyFloat .. ntyFloat64}
  byValueStructural = {ntyDistinct, ntyAlias, ntyObject, ntyTuple,
                       ntyGenericInst}

func classRows(): seq[ClassKey] =
  for k in NimTypeKind:
    let key = classKey(k)
    if k in byValueLeaf:
      result.add (key, modelled[TypeClassSite, TypeClassModel](
        tmLeaf, {tcByValueFormal},
        "a scalar, handle or routine value: its own bytes on every setting " &
        "pinned in tsymex_rfc0005_s8cq_native"))
    elif k in byValueStructural:
      result.add (key, modelled[TypeClassSite, TypeClassModel](
        tmStructural, {tcByValueFormal},
        "copied when its components are, at most three words, final, " &
        "no pragma on the type (ccgIntroducedPtr)"))
    elif k == ntyFloat128:
      result.add (key, refused[TypeClassSite, TypeClassModel](
        none(SymexErrorKind),
        "STY-06: `c_long_double` is x87 80-bit on x86-64 and 64-bit on " &
        "MSVC and some ARM targets, so its value is the C target's, not Nim's",
        iNever, nrPlatform))
    else:
      result.add (key, refused[TypeClassSite, TypeClassModel](
        none(SymexErrorKind),
        "not on the by-value allowlist: not known to be copied, so a by-value " &
        "formal falls to `byValueWritten`, never to a verdict"))
  for f in ["array", "distinct", "tuple"]:
    result.add ("variant/omittedField/" & f,
      modelled[TypeClassSite, TypeClassModel](tmNone, {tcFeature},
        "an omitted variant field of this type takes its zero value (HRV-06)"))
  for f in ["Table", "HashSet"]:
    result.add ("variant/omittedField/" & f,
      refused[TypeClassSite, TypeClassModel](some(feUnsupportedOpHavoc),
        "an omitted variant field of this type has no zero value in the " &
        "model (HRV-06): havoc, declined"))
  result.add ("array/enumIndex",
    modelled[TypeClassSite, TypeClassModel](tmNone, {tcFeature},
      "an array indexed by an enum"))
  result.add ("owned",
    refused[TypeClassSite, TypeClassModel](none(SymexErrorKind),
      "STY-04: `owned T` is the newruntime ownership marker (it is not a " &
      "`NimTypeKind`); the walker models plain refs and has no ownership " &
      "state", iNever, nrByDesign))
  result.add ("atomic",
    refused[TypeClassSite, TypeClassModel](none(SymexErrorKind),
      "STY-04: `Atomic[T]` is a concurrent-memory primitive; the walker runs " &
      "one thread of control", iNever, nrByDesign))
  result.add ("float/sNaNPayload",
    refused[TypeClassSite, TypeClassModel](none(SymexErrorKind),
      "STY-06: the IEEE theory has one NaN, so a signalling-NaN payload " &
      "cannot be represented", iNever, nrTheory))

const typeClassTable* = axisTable[TypeClassSite, TypeClassModel](
  axTypeClass, classRows())

func admitTypeClass*(k: NimTypeKind; site: TypeClassSite):
    Admit[TypeClassModel] =
  ## Whether a type of this kind is modelled at `site`, and how.
  typeClassTable.admit(classKey(k), site, absent = none(SymexErrorKind))

# ---------------------------------------------------------------------------
# The type x memory-op axis.
# ---------------------------------------------------------------------------

func irKey*(k: IRTypeKind): string =
  ## `itMultiVariant` -> `multiVariant`.
  lowerLead(($k)[2 .. ^1])

func opKey(op: MemOp; k: IRTypeKind): string =
  lowerLead(($op)[2 .. ^1]) & "/" & irKey(k)

func letCursorShare(k: IRTypeKind): tuple[m: MemShare, note: string] =
  ## Exhaustive: a new `IRTypeKind` does not compile until it is answered.
  case k
  of itInt, itBool, itFloat32, itFloat64, itBitSet:
    (msValue, "a number or a bit vector: the `let` is a copy")
  of itRef, itPtr, itUninterp:
    (msValue, "a handle is copied; the cell it names is the heap's")
  of itString, itSeq, itTable, itSet:
    (msShared, "owns heap memory: the `let` shares it under refc, and under " &
               "orc and arc when cursor inference proves it")
  of itTuple, itArray, itVariant, itMultiVariant, itDistinct:
    (msComponents, "shares memory when a component does")

func opRows(): seq[OpKey] =
  for k in IRTypeKind:
    let s = letCursorShare(k)
    result.add (opKey(moLetCursor, k),
                modelled[TypeOpSite, MemShare](s.m, {toHoldsSharedMemory}, s.note))

const typeOpTable* = axisTable[TypeOpSite, MemShare](axTypeOp, opRows())

func admitTypeOp*(k: IRTypeKind; op: MemOp; site = toHoldsSharedMemory):
    Admit[MemShare] =
  typeOpTable.admit(opKey(op, k), site, absent = none(SymexErrorKind))

func holdsSharedMemory*(t: IRType): bool =
  ## RFC-0005 S8cn. `t` is, or holds, a seq, a string, a Table or a HashSet,
  ## through any component: a tuple field, an array element, a distinct base,
  ## a variant's plain fields and arms, a multi-variant's axes. A kind the
  ## table does not answer holds shared memory.
  if t == nil: return false
  let a = admitTypeOp(t.kind, moLetCursor)
  if not a.admitted: return true
  case a.payload
  of msValue: false
  of msShared: true
  of msComponents:
    case t.kind
    of itTuple:
      for f in t.fields:
        if holdsSharedMemory(f): return true
      false
    of itArray: holdsSharedMemory(t.elemTy)
    of itDistinct: holdsSharedMemory(t.distinctBase)
    of itVariant:
      for f in t.vPlainFieldTypes:
        if holdsSharedMemory(f): return true
      for arm in t.vArms:
        for f in arm.fieldTypes:
          if holdsSharedMemory(f): return true
      false
    of itMultiVariant:
      for f in t.mvPlainFieldTypes:
        if holdsSharedMemory(f): return true
      for ax in t.mvAxes:
        for arm in ax.arms:
          for f in arm.fieldTypes:
            if holdsSharedMemory(f): return true
      false
    else: true      # a components row with no walk: fail closed
