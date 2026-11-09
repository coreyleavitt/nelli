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
## * K3b adds the `fieldDefault` operation to the same table: how a value of
##   an IR kind is zeroed (`fieldDefault/int`, `fieldDefault/seq`).
##   `zeroValueForType` (`var o: T`, `wasMoved`, `reset`, `move`, a
##   constructor's omitted field) reads the row. A field's `= default` is
##   never applied here: Nim writes it into the typed AST of `default(T)`,
##   `T()` and `new`, and a `wasMoved` leaves the bitwise zero.
##
## The conversion, comparison and set-membership cells the K2-0 probes name
## (`cast/int32`, `ptr/lt`, `set/char/in`) are not memory operations on a
## type; they belong to the construct and definedness axes.
import std/[macros, options, strutils]
import ./admission
import ./errorkind
import ./types
export MemOp, MemShare, ZeroModel, TypeOpModel   ## ADM-IR: they live in types.nim

type
  TypeClassSite* = enum
    tcByValueFormal     ## `typeCopiedByValue`: a by-value formal of this kind
    tcClassify          ## `classifyType`: a type of this kind becomes an IR
                        ## type (modelled) or the `__unsupported:` placeholder
    tcFeature           ## a named feature of a type (`owned`, `Atomic`,
                        ## an omitted variant field of a kind): read through
                        ## `admitTypeFeature` by the decision point naming it
  TypeClassModel* = enum
    tmLeaf              ## the value is its own bytes; nothing to look through
    tmStructural        ## copied when its components are (distinct, object, tuple)
    tmNone              ## a feature row: no by-value meaning

  TypeOpSite* = enum
    toHoldsSharedMemory
    toZeroValue         ## `zeroValueForType`
  OpKey = tuple[key: string, row: Row[TypeOpSite, TypeOpModel]]
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
  ## The kinds `classifyType` turns into an IR type (pinned per kind in
  ## tsymex_0016_k2c_typeclass). A leaf kind outside it (`cstring`, `pointer`,
  ## `proc`) is on the by-value allowlist but classifies to the
  ## `__unsupported:`/`__closure` placeholder.
  classified = {ntyBool, ntyChar, ntyEnum, ntyRange, ntyRef, ntyPtr} +
               {ntyInt .. ntyInt64} + {ntyUInt .. ntyUInt64} +
               {ntyFloat, ntyFloat32, ntyFloat64} +
               {ntyString, ntySequence, ntyOpenArray, ntyArray, ntySet,
                ntyTuple, ntyObject, ntyDistinct, ntyAlias, ntyGenericInst,
                ntyVar}
  byValueLeaf = {ntyBool, ntyChar, ntyEnum, ntyRange, ntyRef, ntyPtr,
                 ntyPointer, ntyProc, ntyCString} +
                {ntyInt .. ntyInt64} + {ntyUInt .. ntyUInt64} +
                {ntyFloat .. ntyFloat64}
  byValueStructural = {ntyDistinct, ntyAlias, ntyObject, ntyTuple,
                       ntyGenericInst}

func classRows(): seq[ClassKey] =
  for k in NimTypeKind:
    let key = classKey(k)
    var sites: set[TypeClassSite]
    if k in byValueLeaf or k in byValueStructural: sites.incl tcByValueFormal
    if k in classified: sites.incl tcClassify
    if k in byValueLeaf:
      result.add (key, modelled[TypeClassSite, TypeClassModel](
        tmLeaf, sites,
        "a scalar, handle or routine value: its own bytes on every setting " &
        "pinned in tsymex_rfc0005_s8cq_native",
        elsewhere = some(feUnsupportedParamType)))
    elif k in byValueStructural:
      result.add (key, modelled[TypeClassSite, TypeClassModel](
        tmStructural, sites,
        "copied when its components are, at most three words, final, " &
        "no pragma on the type (ccgIntroducedPtr)",
        elsewhere = some(feUnsupportedParamType)))
    elif k in classified:
      result.add (key, modelled[TypeClassSite, TypeClassModel](
        tmNone, sites,
        "classifyType gives it an IR type; not on the by-value allowlist, " &
        "so a by-value formal falls to `byValueWritten`, never to a verdict",
        elsewhere = some(feUnsupportedParamType)))
    elif k == ntyFloat128:
      result.add (key, refused[TypeClassSite, TypeClassModel](
        some(feUnsupportedParamType),
        "STY-06: `c_long_double` is x87 80-bit on x86-64 and 64-bit on " &
        "MSVC and some ARM targets, so its value is the C target's, not Nim's",
        iNever, nrPlatform))
    else:
      result.add (key, refused[TypeClassSite, TypeClassModel](
        some(feUnsupportedParamType),
        "not modelled: classifyType gives it the `__unsupported:` placeholder " &
        "(or a closure placeholder), and it is not on the by-value " &
        "allowlist, so a by-value formal falls to `byValueWritten`"))
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

func admitTypeFeature*(feature: string): Admit[TypeClassModel] =
  ## Whether a named type feature (`owned`, `atomic`, `variant/omittedField/
  ## Table`, `array/enumIndex`) is modelled. A feature with no row is refused
  ## (fail closed): the decision point declines.
  typeClassTable.admit(feature, tcFeature, absent = none(SymexErrorKind))

func omittedFieldFeature*(k: IRTypeKind): string =
  ## The feature row that decides an omitted variant field of IR kind `k`
  ## (HRV-06), or "" when the zero of that kind is not in question.
  case k
  of itTable: "variant/omittedField/Table"
  of itSet: "variant/omittedField/HashSet"
  of itArray: "variant/omittedField/array"
  of itDistinct: "variant/omittedField/distinct"
  of itTuple: "variant/omittedField/tuple"
  else: ""

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

func fieldDefaultZero(k: IRTypeKind): tuple[ok: bool, z: ZeroModel,
                                           note: string] =
  ## Exhaustive: a new `IRTypeKind` does not compile until it is answered.
  case k
  of itInt, itBool, itFloat32, itFloat64, itString, itRef, itPtr:
    (true, zmLiteral, "its bitwise zero is a literal: 0, false, 0.0, \"\", nil")
  of itTable, itSet, itBitSet, itTuple, itArray, itSeq, itVariant,
     itMultiVariant:
    (true, zmZeroValue, "the zero of every field and element; a seq, table " &
      "and set start empty. A field's `= default` is not applied: Nim " &
      "writes it into default(T), T() and new, and wasMoved leaves zero")
  of itDistinct:
    (true, zmBase, "a distinct is its base value in the IR")
  of itUninterp:
    (false, zmLiteral, "a placeholder sort (`__ownership:*`, `__closure`, " &
      "`__unsupported:*`) has no representation to build a zero of: the " &
      "caller declines with the placeholder's own kind")

func opRows(): seq[OpKey] =
  for k in IRTypeKind:
    let s = letCursorShare(k)
    result.add (opKey(moLetCursor, k),
                modelled[TypeOpSite, TypeOpModel](
                  TypeOpModel(op: moLetCursor, share: s.m),
                  {toHoldsSharedMemory}, s.note))
    let z = fieldDefaultZero(k)
    result.add (opKey(moFieldDefault, k),
      if z.ok:
        modelled[TypeOpSite, TypeOpModel](
          TypeOpModel(op: moFieldDefault, zero: z.z), {toZeroValue}, z.note)
      else:
        refused[TypeOpSite, TypeOpModel](none(SymexErrorKind), z.note))

const typeOpTable* = axisTable[TypeOpSite, TypeOpModel](axTypeOp, opRows())

func admitTypeOp*(k: IRTypeKind; op: MemOp; site = toHoldsSharedMemory):
    Admit[TypeOpModel] =
  typeOpTable.admit(opKey(op, k), site, absent = none(SymexErrorKind))

func admitZeroValue*(k: IRTypeKind): Admit[TypeOpModel] =
  ## RFC-0016 ADM-IR. The proof `mkZeroValue` takes: the kind's
  ## `fieldDefault` row, read at the zero-value site. The parser's
  ## `zeroValueForType` and the IR emitter's generated code both ask here.
  admitTypeOp(k, moFieldDefault, toZeroValue)

func holdsSharedMemory*(t: IRType): bool =
  ## RFC-0005 S8cn. `t` is, or holds, a seq, a string, a Table or a HashSet,
  ## through any component: a tuple field, an array element, a distinct base,
  ## a variant's plain fields and arms, a multi-variant's axes. A kind the
  ## table does not answer holds shared memory.
  if t == nil: return false
  let a = admitTypeOp(t.kind, moLetCursor)
  if not a.admitted: return true
  case a.payload.share
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
