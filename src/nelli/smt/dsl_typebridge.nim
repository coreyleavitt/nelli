## Layer 2 of the predicate DSL (ADR-0002): typedesc → `IRType`.
##
## Phase 2 recognises the fixed-width Nim integer family plus the
## type-derived range subtypes:
##
##   * `bool`                         → `tBool()`
##   * `int`/`uint`                   → `tInt(64, signed=…)`
##   * `int{8,16,32,64}`              → `tInt(W, signed=true)`
##   * `uint{8,16,32,64}`             → `tInt(W, signed=false)`
##   * `range[lo..hi]`                → `tInt(W, signed=…)` + range, where
##                                      `W`/signedness come from the BASE
##                                      type the bounds are written in
##                                      (issue #162; plain `int` bounds give
##                                      the historical `tInt(64, true)`)
##   * `Natural`                      → `tInt(64, signed=true)` + range
##   * `Positive`                     → `tInt(64, signed=true)` + range
##
## `classifyType` returns a `ClassifiedType` carrying the `IRType`
## and an optional type-derived range. The parser plumbs the range
## into the `IRParam`/`IRStmt(isLet)` for downstream consumption by
## the runtime (path-condition tightening) and by the abstraction
## layer (promotion proof obligations).

import std/macros
import std/strutils
import std/strformat
import std/sequtils
import std/tables     ## RFC-0005 S8e: the witness type-symbol registry
import std/compilesettings   ## RFC-0005 S8c: `libPath` for `isStdlibDecl`
import ./types

# ---- RFC-0005 S8c: callee resolution by SYMBOL, not by name ------------------
#
# The parser recognises its builtin vocabulary (`+ < == ... contains len inc
# items ...`) by the callee's NAME. A user overload of one of those names -- a
# `+` on a `distinct int`, a `==` on an object, a non-generic `contains`/`len`
# that beats the stdlib generic, a `converter` -- was modelled as the builtin:
# a silent substitution (§2.2's class) with nothing recorded. The typed AST the
# parser receives carries the RESOLVED symbol at every call head (`nnkSym`,
# probe-confirmed for `nnkCall`/`nnkInfix`/`nnkPrefix`/`nnkHiddenCallConv`,
# including `>`/`!=`/`notin`, which the compiler rewrites through the user's
# `<`/`==`/`contains`), so the question "is this the builtin?" is answerable
# exactly: where was the resolved routine DECLARED?

const nimLibDirForCmp = block:
  ## The compiler's own `lib/` tree, normalised for a prefix compare (both
  ## separators, and case, which a Windows toolchain path may vary in).
  var d = querySetting(libPath).replace('\\', '/').toLowerAscii
  if not d.endsWith("/"): d.add '/'
  d

proc isStdlibDecl*(sym: NimNode): bool =
  ## RFC-0005 S8c. True iff `sym` is a symbol whose declaration lives in the
  ## compiler's own `lib/` tree (`system` and its includes, `std/*`,
  ## `pure/*`, ...). Decided from the declaration's file, not its module
  ## NAME: a user module may be called `sequtils` or `tables`, and a nimble
  ## package is user code, not stdlib.
  if sym.kind != nnkSym: return false
  let impl = sym.getImpl
  if impl.kind == nnkNilLit: return false
  impl.lineInfoObj.filename.replace('\\', '/').toLowerAscii.startsWith(
    nimLibDirForCmp)

const userRoutineSymKinds = {nskProc, nskFunc, nskMethod, nskConverter,
                             nskIterator}

const procValueSymKinds* = {nskProc, nskFunc}
  ## RFC-0005 S8bn (item 6). The routines a proc-typed value (a proc field's
  ## assignment, `dsl_parser.pfProcSym`) can name directly.

proc isUserRoutine*(sym: NimNode): bool =
  ## RFC-0005 S8c. True iff `sym` resolves to a routine declared OUTSIDE the
  ## stdlib -- the SUT's own procs, a nimble package's, nelli's. Such a call
  ## is never a builtin model, whatever its name: the parser walks it like
  ## any other user call (the precise answer). A proc-valued VARIABLE
  ## (`nskLet`/`nskParam`/...) is not a routine symbol and is left to the
  ## closure-call arms; an unresolved `nnkIdent` (the untyped isolation entry
  ## point, ADR-0002) is not a symbol at all. A routine with no locatable
  ## declaration (`getImpl` nil) is conservatively NOT claimed user here --
  ## no such routine reaches the parser in real compiler output (every
  ## routine symbol in the typed AST carries its impl).
  sym.kind == nnkSym and sym.symKind in userRoutineSymKinds and
    sym.getImpl.kind != nnkNilLit and not isStdlibDecl(sym)

# ---- RFC-0005 S8d: type heads resolved by SYMBOL, not by name ----------------
#
# The same substitution one level down. `classifyType` and the parser's
# type-dependent arms recognised `seq`/`Table`/`HashSet`/`range`/`array`/
# `sink`/`lent`/`owned`, the scalar spellings (`int8`, `bool`, `Natural`,
# `byte`, ...) and `unicode.Rune` by the type's NAME. A user type spelled the
# same way -- a user generic `Table[K, V]`, an alias `Natural = int`, a
# `Rune = distinct RuneImpl` of the user's own -- was modelled as the stdlib
# type, with nothing recorded. The typed AST carries the type's symbol, so the
# question is again answerable exactly.

proc isStdlibTypeSym*(sym: NimNode): bool =
  ## RFC-0005 S8d, the type-symbol analogue of `isStdlibDecl`. True iff `sym`
  ## is a type symbol that is either a compiler builtin or declared under the
  ## compiler's `lib/` tree. The builtins (`int`, `int8`, `char`, `float`,
  ## `string`, and the `seq`/`set`/`array`/`range`/`openArray` heads of an
  ## instance) have NO declaration at all -- `getImpl` is nil, probe-confirmed
  ## on this toolchain -- whereas every user-declared type has its `TypeDef`,
  ## so a nil impl is the builtin's signature, not an unknown. Everything
  ## else (`Natural`, `byte`, `bool`, `Table`, `HashSet`, `Rune`, `sink`, ...)
  ## is decided by the declaring file, as for callees.
  if sym.kind != nnkSym or sym.symKind != nskType: return false
  sym.getImpl.kind == nnkNilLit or isStdlibDecl(sym)

proc isBuiltinTypeHead*(head: NimNode; names: openArray[string]): bool =
  ## RFC-0005 S8d. True iff the type head `head` is spelled as one of `names`
  ## AND is the stdlib type of that name. An `nnkSym` head must resolve to the
  ## stdlib (`isStdlibTypeSym`); a user type of the same name is not the
  ## builtin. An `nnkIdent` head is unresolved -- the untyped isolation entry
  ## point (ADR-0002) -- and carries no symbol to check, so its spelling is
  ## all there is (S8c's rule for an `nnkIdent` callee, `isUserRoutine`). The
  ## typed pipeline never presents a user type that way: every type head in a
  ## typed formal, a `getTypeInst` result or a `getImpl` body is an `nnkSym`
  ## (probe-confirmed, including generic formals' `sink`/`lent`/`array`).
  if head.kind notin {nnkIdent, nnkSym} or head.strVal notin names:
    return false
  head.kind == nnkIdent or isStdlibTypeSym(head)

proc typeSpelling*(t: NimNode): string =
  ## RFC-0005 S8d. The spelling a name-keyed type table (the parser's
  ## `intTyNames`/`fltTyNames`, the `low`/`high` fold, `"bool"`, the
  ## `byte`/`uint8` literal unwrap) may match. A stdlib type symbol (or an
  ## unresolved `nnkIdent`, see `isBuiltinTypeHead`) is its own name; any
  ## other symbol -- a user type, or a VALUE symbol (`low(someArray)`) -- is
  ## tagged `user:` so it can never equal a builtin spelling while still
  ## reading naturally in a decline message.
  case t.kind
  of nnkIdent: t.strVal
  of nnkSym: (if isStdlibTypeSym(t): t.strVal else: "user:" & t.strVal)
  else: t.repr

proc isStdlibRuneSym*(sym: NimNode): bool =
  ## RFC-0005 S8d. True iff `sym` is `std/unicode.Rune` itself. The A7
  ## intercept (a Rune is an int pinned to [0, 0x10FFFF]) matched the name
  ## pair `Rune`/`RuneImpl`, so a user `type RuneImpl = int32; Rune =
  ## distinct RuneImpl` -- any int32, negatives included -- was pinned too.
  ## Shared by `classifyType` and the parser's `isRuneTyped`, so the two
  ## sites cannot disagree.
  sym.kind == nnkSym and sym.strVal == "Rune" and isStdlibTypeSym(sym)

proc nominalId*(n: NimNode): string =
  ## Canonical, symbol-unique nominal type identity for a named object type or
  ## generic instantiation. Stable across call sites (`signatureHash` of the
  ## type symbol), and distinguishes generic instantiations by their type ARGS
  ## (`Box[int]` vs `Box[string]`) — the head symbol's hash is identical, the
  ## args disambiguate. Populated onto `IRType.nominalId` at construction; NOT
  ## yet consumed anywhere (Cluster H Step A is a pure no-op — Step B wires this
  ## into `refPointeeTypeId`). NOTE: `signatureHash` on an `nnkBracketExpr` node
  ## itself is a hard compile error, hence the `.kind` dispatch.
  case n.kind
  of nnkSym: signatureHash(n)
  of nnkBracketExpr:
    var s = signatureHash(n[0])
    for i in 1 ..< n.len: s.add "|" & nominalId(n[i])
    s
  else: n.repr

proc inheritObjectBody(sym: NimNode): tuple[nomSym, obj: NimNode] =
  ## RFC-0005 S8bh (item 3). The `nnkObjectTy` body a type symbol names and
  ## the symbol `classifyType` keys its nominal id on: the symbol itself for
  ## `type T = object ...` / `type T = ref object ...`, the object's own
  ## symbol for `type T = ref Obj`. `(nil, nil)` for anything else (a
  ## generic, a non-object).
  if sym.kind != nnkSym: return (nil, nil)
  let impl = sym.getImpl
  if impl.kind != nnkTypeDef or impl.len < 3: return (nil, nil)
  if impl[1].kind == nnkGenericParams: return (nil, nil)
  let u = impl[2]
  if u.kind == nnkObjectTy: return (sym, u)
  if u.kind in {nnkRefTy, nnkPtrTy} and u.len == 1:
    if u[0].kind == nnkObjectTy: return (sym, u[0])
    if u[0].kind == nnkSym: return inheritObjectBody(u[0])
  (nil, nil)

proc isInheritableRoot(sym: NimNode): bool =
  ## RFC-0005 S8bn (item 8). `sym` names a type declared `{.inheritable.}`
  ## (a hierarchy root without `of`).
  if sym.kind != nnkSym: return false
  let impl = sym.getImpl
  if impl.kind != nnkTypeDef or impl.len < 1 or impl[0].kind != nnkPragmaExpr:
    return false
  for pr in impl[0][1]:
    if pr.kind in {nnkIdent, nnkSym} and pr.strVal == "inheritable": return true
  false

proc inheritInfo*(sym: NimNode): tuple[chain, ownedNames, ownedIds: seq[string];
                                       parent: NimNode] =
  ## RFC-0005 S8bh (item 3). For a type declared `of` another (`RootObj`
  ## included): the nominal ids from the hierarchy's root down to `sym`'s
  ## type (`IRType.inheritChain`), every field of the chain with the id of
  ## the type declaring it (`ownedFieldNames`/`ownedFieldIds`), and the
  ## direct user parent's symbol (nil under `RootObj`). All empty for a type
  ## without `of`, and for a chain this cannot follow (a generic parent, a
  ## `case` object in the chain): those keep their pre-S8bh per-type keying.
  ## Reads names only -- never a field's type -- so a recursion placeholder
  ## (`namedRefPlaceholder`) can call it without recursing.
  ##
  ## RFC-0005 S8bn (item 8): one level of the chain may hold a `case` part
  ## (a case object under `RootObj`, or a type derived from one): its plain
  ## fields are owned as any level's; its discriminator and branch fields
  ## key on the root through the variant's own keys. A chain with two
  ## levels holding one keeps per-type keying.
  var cur = sym
  var levels: seq[tuple[id: string; names: seq[string]]]
  var first = true
  var caseLevels = 0
  while true:
    let (nomSym, obj) = inheritObjectBody(cur)
    if obj == nil or obj.len < 3: return
    var names: seq[string]
    if obj[2].kind == nnkRecList:
      var hasCase = false
      for d in obj[2]:
        if d.kind == nnkRecCase:
          if hasCase: return            # two axes: a multi-variant
          hasCase = true
          inc caseLevels
          if caseLevels > 1: return
          continue
        if d.kind != nnkIdentDefs: return
        for i in 0 ..< d.len - 2:
          var nn = d[i]
          if nn.kind == nnkPostfix: nn = nn[1]
          if nn.kind == nnkPragmaExpr: nn = nn[0]
          if nn.kind notin {nnkIdent, nnkSym}: return
          names.add nn.strVal
    levels.insert((nominalId(nomSym), names), 0)
    let inh = obj[1]
    if inh.kind != nnkOfInherit or inh.len != 1:
      # RFC-0005 S8bn (item 8): a `{.inheritable.}` type is a hierarchy's
      # root, as `RootObj`'s child is.
      if isInheritableRoot(nomSym) or isInheritableRoot(cur): break
      return                    # no `of`: not a hierarchy
    let par = inh[0]
    # RFC-0005 S8bn (item 8): `of RootRef` (`ref RootObj`) roots one too.
    if par.kind == nnkSym and par.strVal in ["RootObj", "RootRef"]: break
    if par.kind != nnkSym: return
    if first: result.parent = par
    first = false
    cur = par
  for lv in levels:
    result.chain.add lv.id
    for nm in lv.names:
      result.ownedNames.add nm
      result.ownedIds.add lv.id

proc withInheritInfo(t: IRType, sym: NimNode): IRType =
  ## RFC-0005 S8bh (item 3). Stamp `inheritInfo(sym)` onto the freshly built
  ## tuple `t` (placeholder or full) and return it.
  if t.kind != itTuple: return t
  let info = inheritInfo(sym)
  if info.chain.len == 0: return t
  t.inheritChain = info.chain
  t.ownedFieldNames = info.ownedNames
  t.ownedFieldIds = info.ownedIds
  t

var witnessTypeSyms {.compileTime.}: Table[string, NimNode]
  ## RFC-0005 S8e. `IRType.typeKey` -> the symbol of the named user type it
  ## was classified from. Never cleared: an entry is a fact about a symbol,
  ## and a cached parse may emit its witness long after the classification.

proc keyedBySym*(ty: IRType, sym: NimNode): IRType =
  ## RFC-0005 S8e. Record `sym` as the symbol that names `ty` in a witness and
  ## return `ty` (freshly built by the caller, so the stamp touches no shared
  ## node). The witness emitter (`symex.emitTyAndReader`) builds its value in
  ## the CALLER's scope, where the type's spelling may be undeclared (the
  ## caller imported only the SUT proc) or bound to a different type (a user
  ## `OrderedTable` object, beside `std/tables.OrderedTable`). A symbol names
  ## its own type in any scope. A node that is not a symbol records nothing:
  ## the emitter then keeps its spelling.
  if sym.kind == nnkSym:
    let key = nominalId(sym)
    witnessTypeSyms[key] = sym
    ty.typeKey = key
  ty

proc witnessTypeSym*(ty: IRType): NimNode =
  ## RFC-0005 S8e. The symbol recorded for `ty` by `keyedBySym`, or nil.
  if ty.typeKey.len == 0: nil
  else: witnessTypeSyms.getOrDefault(ty.typeKey)

type
  ClassifiedType* = object
    ty*:    IRType
    range*: tuple[hasRange: bool, lo, hi: int64]

proc unranged(ty: IRType): ClassifiedType =
  ClassifiedType(ty: ty, range: (false, 0'i64, 0'i64))

proc ranged(ty: IRType, lo, hi: int64): ClassifiedType =
  ## Issue #162: the bounds go onto the TYPE as well as into the
  ## `ClassifiedType.range` tuple. The tuple feeds `IRParam`, which only ever
  ## reaches top-level params; the type travels everywhere a type travels —
  ## into object fields, nested objects, array and seq elements — and that is
  ## the only route by which a range-typed FIELD can be constrained at all.
  ## Both are populated rather than one being removed: the param path also
  ## carries ASSERTION-derived ranges (#134), which are not type-level facts.
  ClassifiedType(ty: (if ty.kind == itInt: ty.withRange(lo, hi) else: ty),
                 range: (true, lo, hi))

proc parseRangeBracket(rangeNode: NimNode): tuple[lo, hi: int64] =
  ## Parse `range[lo .. hi]` (already known to be the right shape).
  ## `rangeNode` is the nnkBracketExpr; index 1 is the `lo .. hi` infix.
  let body = rangeNode[1]
  body.expectKind nnkInfix
  if body[0].strVal != "..":
    error("symex (Phase 2): expected `..` in range bound", body)
  result.lo = body[1].intVal
  result.hi = body[2].intVal

proc rangeBaseType(bound: NimNode): IRType =
  ## Issue #162. A `range[lo .. hi]` is a SUBTYPE — of `int32` in
  ## `range[0'i32 .. 100_000'i32]`, of `int` in `range[0 .. 1000]`. Nim
  ## performs arithmetic on the subtype in its BASE type and checks overflow
  ## against the base type's window, so the base type is what the walker has
  ## to model: `mul32(100_000, 100_000)` raises `OverflowDefect` at runtime
  ## precisely because `typeof(a * b)` is `int32` and 1e10 does not fit.
  ## Classifying every range as 64-bit checked that multiply against a window
  ## where it fits, and a real reachable defect disappeared in BOTH integer
  ## modes (`isExact` too — this sits upstream of any promotion decision).
  ##
  ## The base type is recoverable from a bound literal's own NODE KIND, which
  ## semcheck stamps and which survives on both routes into this module: the
  ## instantiated formal (`getTypeInst`) and the named alias (`getImpl`).
  ## Reading the kind rather than calling `getTypeInst` on the literal matters
  ## for the alias route, where the bound comes from the type DEFINITION's AST
  ## and need not carry a type at all.
  ##
  ## Unmatched kinds — `nnkIntLit`/`nnkInt64Lit` (base `int`/`int64`) and
  ## `nnkCharLit` — keep the historical `tInt(64, signed = true)`. That is the
  ## right answer for the int family and a harmless one for `char`: Nim has no
  ## `+` on chars, so a char range carries no arithmetic obligation to get
  ## wrong.
  ##
  ## Signedness is recovered as well as width. An unsigned base is not merely
  ## a different window — it is different SEMANTICS: Nim wraps unsigned
  ## arithmetic silently instead of raising, so `a + b` over a uint8 base can
  ## be less than `a`. Modelled as signed 64-bit, that path was unreachable.
  ## See `allocateSym`'s `promoteSound` guard for the matching rule on the
  ## representation side.
  case bound.kind
  of nnkInt8Lit:   tInt(8,  signed = true)
  of nnkInt16Lit:  tInt(16, signed = true)
  of nnkInt32Lit:  tInt(32, signed = true)
  of nnkUInt8Lit:  tInt(8,  signed = false)
  of nnkUInt16Lit: tInt(16, signed = false)
  of nnkUInt32Lit: tInt(32, signed = false)
  of nnkUIntLit, nnkUInt64Lit:
                   tInt(64, signed = false)
  else:            tInt(64, signed = true)

proc enumOrdBitsNeeded(minOrd, maxOrd: int64, signed: bool): int =
  ## Issue #163 review R2. Smallest of the four widths `IRType.width` ever
  ## takes (8/16/32/64 — see `bvVar`'s width-exhaustive `case ty.width` in
  ## `runtime.nim`) whose window losslessly holds `[minOrd, maxOrd]` under
  ## the given signedness. Sizing off ordinal MAGNITUDE rather than member
  ## COUNT matters: a 3-member enum with one `= 300` ordinal needs 16 bits,
  ## not 8 — an 8-bit window would force the bound-literal construction
  ## downstream (`mkBitVec[8]`, which truncates mod 2^8 per its own doc)
  ## to silently alias 300 down to 44.
  ##
  ## Ordinal literals are read via `NimNode.intVal` (a `BiggestInt` — a
  ## 64-bit host int), so `[minOrd, maxOrd]` is always representable at
  ## width 64; this never needs to signal an unrepresentable range.
  if signed:
    if minOrd >= -128'i64 and maxOrd <= 127'i64: 8
    elif minOrd >= -32768'i64 and maxOrd <= 32767'i64: 16
    elif minOrd >= -2147483648'i64 and maxOrd <= 2147483647'i64: 32
    else: 64
  else:
    if maxOrd <= 0xFF'i64: 8
    elif maxOrd <= 0xFFFF'i64: 16
    elif maxOrd <= 0xFFFFFFFF'i64: 32
    else: 64

proc enumFieldOrdinals*(enumBody: NimNode): seq[(string, int64)] =
  ## Issue #163 review round 2 (R18/R23), structural fix approved ahead of
  ## the per-finding patches: SINGLE source of truth for walking an
  ## `nnkEnumTy` body and computing each field's true ordinal. Before this,
  ## `classifyType`'s enum arm (below) and `dsl_parser.parseExpr`'s `nnkSym`
  ## arm each carried their OWN copy of this loop, kept in sync only by
  ## review discipline -- exactly the shape review finding R15 already had
  ## to fix once (the two loops disagreed on what a field's ordinal was).
  ## Routing both consumers through one function removes the divergence
  ## class outright rather than re-auditing two call sites every time this
  ## logic changes.
  ##
  ## `enumBody` is the `nnkEnumTy` node itself (`impl[2]` of the enum's
  ## `nnkTypeDef`/`nnkEnumTy` impl) -- child 0 is the empty/base-type slot,
  ## children `1 ..< len` are the fields, in declaration order.
  ##
  ## Per-field value shapes (confirmed against this exact toolchain via
  ## `scratchpad/probe_r18_enum_valueshapes.nim` and
  ## `scratchpad/probe_r18_stringonly.nim` -- not guessed):
  ##   * bare `nnkSym` (no explicit value)               -> implicit,
  ##     previous ordinal + 1 (0 for the first field).
  ##   * `nnkEnumFieldDef` with an int-literal value      -> that literal IS
  ##     the explicit ordinal (`nnkIntLit..nnkUInt64Lit`).
  ##   * `nnkEnumFieldDef` with a tuple-constructor value (R18: Nim's
  ##     `a = (1, "alpha")` form, e.g. for a custom `$`) -> `nnkTupleConstr`,
  ##     NOT an int literal, so the old int-literal-only guard silently fell
  ##     through to the implicit counter (wrong ordinal, no degrade signal).
  ##     The tuple's first element is the explicit ordinal; its second is
  ##     the display name and plays no role here.
  ##   * `nnkEnumFieldDef` with a BARE string-literal value (`a = "alpha"`,
  ##     no tuple) -> confirmed by probe: this assigns ONLY the `$`-name,
  ##     never an explicit ordinal (`ord()` of such a field is still its
  ##     positional auto-increment value) -- implicit, same as bare `nnkSym`.
  ##   * anything else (R23): Nim's own enum grammar admits no other
  ##     field-value shape. The prior parser loop's `else: continue` on an
  ##     unrecognised child advanced its OWN caller's `i` but not
  ##     `nextOrdinal`, silently desyncing it from the classifier's loop
  ##     (which had no such guard and always advanced) for every subsequent
  ##     field -- precisely the classifier/parser divergence class R15 was
  ##     written to close, just relocated to a different trigger. Since a
  ##     conforming child can never actually take this arm, "advance and
  ##     hope" and "silently keep the old ordinal" are both guesses about an
  ##     AST shape that, per Nim's own grammar, does not mean what this
  ##     proc assumes it means -- fail loudly at macro-expansion time
  ##     instead, matching this codebase's own precedent for a structurally
  ##     impossible node kind (`dsl_parser.parseExpr`'s case-arm-kind arm:
  ##     `else: error(&"...unexpected case-arm kind {arm.kind}", arm)`).
  var nextOrdinal = 0'i64
  for i in 1 ..< enumBody.len:
    let c = enumBody[i]
    if c.kind != nnkSym and c.kind != nnkEnumFieldDef:
      error("issue #163 review R23: unexpected enum-body child kind " &
            $c.kind & " (neither nnkSym nor nnkEnumFieldDef) -- Nim's own " &
            "enum grammar admits no other field shape, so enumFieldOrdinals " &
            "declines rather than risk silently desyncing from another " &
            "caller's ordinal tracking", c)
      # `error` is `{.noReturn.}` -- aborts compilation, never falls through.
    let fieldSym = if c.kind == nnkSym: c else: c[0]
    var ord = nextOrdinal
    if c.kind == nnkEnumFieldDef:
      let val = c[1]
      if val.kind in nnkIntLit..nnkUInt64Lit:
        ord = val.intVal
      elif val.kind == nnkTupleConstr and val.len >= 1 and
           val[0].kind in nnkIntLit..nnkUInt64Lit:
        ord = val[0].intVal
      # else (bare string-literal name, or any other Nim-legal literal):
      # no explicit ordinal -- `ord` already holds the implicit value.
    result.add (fieldSym.strVal, ord)
    nextOrdinal = ord + 1

proc classifyFieldType*(ty: NimNode): ClassifiedType   ## fwd decl (R9)
proc classifyType*(ty: NimNode): ClassifiedType   ## fwd decl (Cluster H Step C:
  ## `classifyObjectRecordFields` needs it for a variant discriminator's type)

proc unwrapFieldNameNode(n: NimNode): NimNode =
  ## v64 §0 clause (b) precedent (chapulin round-3), generalized: a raw
  ## `getImpl` record can carry an EXPORTED/pragma'd/quoted field name as
  ## `nnkPostfix("*", name)` / `nnkPragmaExpr(name, pragmas)` /
  ## `nnkAccQuoted(name)` instead of a bare `nnkIdent`/`nnkSym` — unwrap the
  ## known wrapper shapes so `.strVal` is safe to call on the result. A bare
  ## `.strVal` read on the wrapped node crashes macro expansion ("node lacks
  ## field: strVal"), aborting the whole file — originally fixed only for
  ## the plain-record path (below); A6 (RFC-chapulin-hardening) hit the
  ## SAME crash via a real exported case-object's discriminator/arm field
  ## names (every synthetic symex test SUT to date used unexported local
  ## types, so the variant path's three raw `.strVal` sites went
  ## unexercised against this shape until now) — extracted here so all
  ## three variant-path sites share the one fix.
  result = n
  if result.kind == nnkPragmaExpr and result.len >= 1:
    result = result[0]
  if result.kind == nnkPostfix and result.len == 2:
    result = result[1]
  if result.kind == nnkAccQuoted and result.len >= 1:
    result = result[0]

proc fieldNameStr(n: NimNode, fallbackIx: int): string =
  ## `unwrapFieldNameNode` + the same "unresolved generic param" positional
  ## fallback the plain-record path already uses (the name is never
  ## load-bearing for soundness there; an unresolved generic degrades via
  ## CR-2b's `__unsupported:` marker at allocation time regardless).
  let nameNode = unwrapFieldNameNode(n)
  if nameNode.kind in {nnkIdent, nnkSym}: nameNode.strVal
  else: "__field" & $fallbackIx

proc fieldDeclineMsg(n: NimNode, note: string): string =
  ## Round-6 Bug #2 (scoped decline). Mirrors `dsl_parser.siteMsg`'s EXACT
  ## format (`<file>:<line>:<col>: {note} in \`{n.repr}\``) — duplicated
  ## rather than imported: `dsl_typebridge` is Layer 2, a dependency OF
  ## `dsl_parser` (Layer 3, which imports this module), so importing
  ## `dsl_parser` here to reuse `siteMsg` directly would create an import
  ## cycle. Captured at PARSE time, where a `NimNode` (and therefore a real
  ## source location) still exists for the DECLARED field — the eventual
  ## READ-site decline (`dsl_parser.nim`'s `nnkDotExpr` arm) renders this
  ## string VERBATIM (the same walk-time discipline `siteLoc` established for
  ## `isVariantConstructSym`'s budget-cap message), so the read decline is
  ## honest about WHERE the unsupported field was declared, not merely that
  ## some read touched it.
  let li = n.lineInfoObj
  &"{li.filename}:{li.line}:{li.column}: {note} in `" & n.repr & "`"

const maxRecursiveValueDepth* = 2
  ## RFC-0005 S8bc (item 3). How many levels of a recursive value object
  ## (`type T = object; kids: seq[T]`) below the outermost are modelled:
  ## `p.kids[i].kids[j]` is, `p.kids[i].kids[j].kids` is the depth
  ## placeholder (`seRecursiveValueDepth`).
const recursiveDepthPrefix = "__unsupported:recursive value object depth bound "
  ## RFC-0005 S8bc. The `uninterpName` prefix of the element type past the
  ## depth bound (`scopedDeclineFieldTy` keys its decline kind on it).

proc unsupportedFieldTy(fieldName: string, elemTy: IRType, n: NimNode): IRType =
  ## Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution 2026-08-15) —
  ## build the per-field UNSUPPORTED PLACEHOLDER `IRType` (see the
  ## `isUnsupportedFieldPlaceholder`/`isBackedSeqElemTy` doc block in
  ## `types.nim` for the full mechanism). Called by
  ## `classifyObjectRecordFields` in place of a real `itSeq` field type
  ## whenever `isBackedSeqElemTy` declines `elemTy`. `elemTy` (not just its
  ## `.kind`) is threaded through so `tUnsupportedFieldSeq` can still build a
  ## real, correctly-typed (if content-empty) `seq[T]` witness reader later.
  ## Round-6 N12 (message-formatting boundary): this reaches the user
  ## through `SymexResult.errors` (`declineUnsupportedFieldRead`,
  ## `dsl_parser.nim`, renders `fieldTy.seqUnsupportedFieldReason` — this
  ## string — verbatim into a `SymexErrorInfo.msg`) — route the element
  ## kind through `plainEnglishTypeKind` instead of the bare `$elemTy.kind`
  ## so internal IR vocabulary ("itTuple") does not leak into it. `.kind`
  ## (the structured `SymexErrorKind` field) is unchanged.
  tUnsupportedFieldSeq(elemTy, fieldDeclineMsg(n,
    "field `" & fieldName & "` of type seq[" & plainEnglishTypeKind(elemTy.kind) &
    "] not modeled (nested seq element type is not supported)"))

proc scopedDeclineFieldTy(rawFty: IRType, fieldNameNode: NimNode,
                          declNode: NimNode): IRType =
  ## Round-6 Bug #2. Applied to EVERY field type `classifyObjectRecordFields`
  ## derives (plain-record fields, variant plain fields, variant arm fields):
  ## if `rawFty` is a `seq[T]` with an unbacked element kind, replace it with
  ## the scoped-decline placeholder instead of the real (eagerly
  ## unallocatable) `itSeq`. Every other field type passes through
  ## unchanged. `fieldNameNode` supplies the field's own name for the decline
  ## message (falls back positionally like `fieldNameStr` does); `declNode`
  ## is the `nnkIdentDefs` group the field was declared in, for `lineInfo`.
  if rawFty.kind == itSeq and rawFty.seqElemTy.kind == itUninterp and
     rawFty.seqElemTy.uninterpName.startsWith(recursiveDepthPrefix):
    # RFC-0005 S8bc: the seq at a recursive value object's depth bound.
    tUnsupportedFieldSeq(rawFty.seqElemTy, fieldDeclineMsg(declNode,
      "field `" & fieldNameStr(fieldNameNode, 0) & "` is a recursive value " &
      "object's seq past the modelled depth (" & $maxRecursiveValueDepth &
      " levels below the outermost value)"), kind = seRecursiveValueDepth)
  elif rawFty.kind == itSeq and not isBackedSeqElemTy(rawFty.seqElemTy):
    unsupportedFieldTy(fieldNameStr(fieldNameNode, 0), rawFty.seqElemTy, declNode)
  else:
    rawFty

proc tagOrdOf(tagNode: NimNode;
              enumOrdinals: seq[tuple[name: string, ordinal: int]]):
              tuple[name: string, ord: int] =
  ## RFC-0005 S8z. The (name, ordinal) of one variant tag label: an enum
  ## member or an integer literal (a `range` discriminator's `of 0:`). A
  ## top-level proc taking `enumOrdinals`, not a closure over it: a nested
  ## proc capturing the per-`case` `var enumOrdinals` moved it into a
  ## closure environment the macro VM did not re-zero per `case`, so a
  ## second axis's tags doubled (a witness `case` with duplicate labels).
  let tagName =
    case tagNode.kind
    of nnkSym, nnkIdent: tagNode.strVal
    of nnkIntLit..nnkInt64Lit: ""  # unusual but legal
    else: ""
  # Resolve ordinal from enumOrdinals or, if missing, from the literal.
  var tagOrd = -1
  for eo in enumOrdinals:
    if eo.name == tagName: tagOrd = eo.ordinal; break
  if tagOrd < 0 and tagNode.kind in nnkIntLit..nnkInt64Lit:
    tagOrd = int(tagNode.intVal)
  if tagOrd < 0:
    error("symex Phase 11: could not resolve ordinal " &
          "for tag `" & tagName & "`", tagNode)
  (tagName, tagOrd)

proc classifyObjectRecordFields*(nameSym: NimNode, recList: NimNode,
                                  isRefWrapped: bool = false): IRType =
  ## Cluster H Step C (ADR-0022 Round-2): shared core that builds the FULL
  ## record-field `IRType` for a named object's `nnkRecList`, keyed nominally
  ## on `nameSym`. Owns the `hasRecCase` VARIANT gate (Phase 11/14 lowering) —
  ## a `case`-having object returns `itVariant`/`itMultiVariant` exactly as
  ## before; a plain object returns `itTuple(fields, names, objectName,
  ## nominalId, nameIsRefAlias)`. Used by `classifyType`'s plain (non-ref)
  ## named-object path (`isRefWrapped = false`) AND its DIRECT named-ref/ptr
  ## path (`type Node = ref object` — `isRefWrapped = true`, since `nameSym`
  ## IS the ref alias itself: `Node(...)` construction syntax already yields a
  ## `ref Node`, so the resulting `itTuple`'s `nameIsRefAlias` flag must say
  ## so for witness rendering, `symex.nim`'s `emitTyAndReader`). NOT called
  ## for sym-indirection (`type NodeRef = ref Obj`) — that delegates to a
  ## RECURSIVE `classifyType(Obj)` call instead, where `Obj` is a genuinely
  ## separate, non-ref-aliased object name (`isRefWrapped` stays false there
  ## too, correctly). The caller wraps the result in `tRef`/`tPtr` -- a
  ## variant result too since RFC-0005 S8l (it was never wrapped under
  ## ADR-0022 sub-decision #1) — `isRefWrapped` only affects the
  ## witness-rendering flag, never the routing decision itself.
  # A genuinely ZERO-FIELD object (`type Token = object` / `type Token = ref
  # object`, no members at all) has an `nnkEmpty` body, NOT `nnkRecList` — Nim
  # omits the record-list node entirely rather than emitting an empty one.
  # Cluster H Step C surfaces this: a zero-field NAMED REF-OBJECT alias
  # (`type Token = ref object`) now reaches this shared helper via the
  # ref-wrap arm (previously only zero-field VALUE objects could reach here).
  # Treat `nnkEmpty` as "zero fields, non-variant" — the plain-record path
  # below already handles an empty `fields`/`names` seq correctly.
  if recList.kind == nnkEmpty:
    return tTuple(@[], @[], objectName =
      (if nameSym.kind in {nnkSym, nnkIdent}: nameSym.strVal else: nameSym.repr),
      nominalId = nominalId(nameSym), nameIsRefAlias = isRefWrapped).keyedBySym(nameSym)
  recList.expectKind nnkRecList
  let s = if nameSym.kind in {nnkSym, nnkIdent}: nameSym.strVal else: nameSym.repr
  # First pass: detect whether this object has any `nnkRecCase`
  # member. If it does, we build an `itVariant` (Phase 11);
  # otherwise the plain-tuple path stays.
  var hasRecCase = false
  for member in recList:
    if member.kind == nnkRecCase:
      hasRecCase = true
      break
  if hasRecCase:
    # ---- Phase 11 single-axis + Phase 14 multi-axis lowering --
    # Each `nnkRecCase` in `recList` becomes one VariantAxis.
    # Plain (non-recCase) fields are shared across all axes.
    # After the loop: 1 axis → `tVariant` (Phase 11 path);
    # 2+ axes → `mkMultiVariant` (Phase 14, ADR-0003 D1).
    var axes: seq[VariantAxis]
    var plainFieldNames: seq[string]
    var plainFieldTypes: seq[IRType]
    for member in recList:
      case member.kind
      of nnkIdentDefs:
        # Plain field group `name1, name2, ..., type, default`.
        let rawFty = classifyFieldType(member[member.len - 2]).ty  ## R9: ref field → heap ref
        let fty = scopedDeclineFieldTy(rawFty, member[0], member)  ## Bug #2
        for j in 0 ..< member.len - 2:
          plainFieldNames.add fieldNameStr(member[j], j)
          plainFieldTypes.add fty
      of nnkRecCase:
        # Parse one recCase into a VariantAxis. The walker reads
        # each axis independently and conjoins per-axis
        # constraints on the same `pcOut` (ADR-0003 D1).
        var discName = ""
        var discTy: IRType = nil
        var arms: seq[VariantArm]
        let discDef = member[0]
        discName = fieldNameStr(discDef[0], 0)
        discTy = classifyType(discDef[discDef.len - 2]).ty
        # discDef[1] is the discriminator's typedesc; its sym
        # carries the enum impl from which we read ordinal +
        # name for each tag.
        let discTypeSym = discDef[discDef.len - 2]
        # Build a name → ordinal map for the discriminator's
        # enum. The enum impl is the type-def's nnkEnumTy node.
        var enumOrdinals: seq[tuple[name: string, ordinal: int]]
        # RFC-0005 S8z: an inline anonymous `range[lo..hi]` discriminator
        # (`case d: range[0..2]`) is an `nnkBracketExpr`, not a symbol, and
        # `getImpl` on it failed the whole file's compile ("node is not a
        # symbol"). It has no enum to read; it takes the non-enum arm below,
        # exactly as a named `range` alias does.
        let dImpl = if discTypeSym.kind == nnkSym: discTypeSym.getImpl
                    else: newEmptyNode()
        if dImpl.kind == nnkTypeDef and dImpl.len >= 3 and
           dImpl[2].kind == nnkEnumTy:
          # nnkEnumTy children: first is nnkEmpty, rest are
          # enum constants. Each is an nnkSym or nnkEnumFieldDef.
          var nextOrdinal = 0
          for i in 1 ..< dImpl[2].len:
            let c = dImpl[2][i]
            var nm = ""
            var ord = nextOrdinal
            case c.kind
            of nnkSym, nnkIdent:
              nm = c.strVal
            of nnkEnumFieldDef:
              # `kind = value` form: c[0] is name, c[1] is ordinal
              nm = c[0].strVal
              if c[1].kind in nnkIntLit..nnkInt64Lit:
                ord = int(c[1].intVal)
            else:
              error("symex Phase 11: unsupported enum constant " &
                    "shape " & $c.kind, c)
            enumOrdinals.add (nm, ord)
            nextOrdinal = ord + 1
        else:
          # Phase 14 cycle A3. Non-enum disc (e.g. `range[lo..hi]`):
          # tagOrdinals come from explicit `of N:` literals; no
          # enumOrdinals to enumerate. `else:` arms use the same
          # conjunction-of-negations the enum path uses.
          discard
        # Process arms: member[1..^1] are nnkOfBranch (or nnkElse).
        for k in 1 ..< member.len:
          let branch = member[k]
          if branch.kind notin {nnkOfBranch, nnkElse}:
            error("symex Phase 14: unsupported recCase branch kind " &
                  $branch.kind, branch)
          # nnkElse has a single child (the body); nnkOfBranch has
          # 0..^2 tag values + a body at the last child.
          let lastIx = branch.len - 1
          let body = branch[lastIx]
          # Collect this arm's plain-field group.
          var armFieldNames: seq[string]
          var armFieldTypes: seq[IRType]
          let bodyMembers = if body.kind == nnkRecList: toSeq(body.children)
                            elif body.kind == nnkIdentDefs: @[body]
                            else: @[]
          for armMember in bodyMembers:
            if armMember.kind != nnkIdentDefs: continue
            let rawFty = classifyFieldType(armMember[armMember.len - 2]).ty  ## R9: ref field → heap ref
            let fty = scopedDeclineFieldTy(rawFty, armMember[0], armMember)  ## Bug #2
            for j in 0 ..< armMember.len - 2:
              armFieldNames.add fieldNameStr(armMember[j], j)
              armFieldTypes.add fty
          # `else:` arm — single VariantArm with isElse=true and
          # tagOrdinal=-1 sentinel. Walker computes the membership
          # constraint lazily as AND_over_non_else(disc != tagOrd).
          if branch.kind == nnkElse:
            arms.add VariantArm(
              tagOrdinal: -1, tagName: "else",
              fieldNames: armFieldNames,
              fieldTypes: armFieldTypes,
              branchIx: k,   # RFC-0005 S8f
              isElse: true)
            continue
          # Emit one arm per tag literal listed in this branch.
          var tags: seq[tuple[name: string, ord: int]]
          for tagIx in 0 ..< lastIx:
            let tagNode = branch[tagIx]
            # RFC-0005 S8z: a range label (`of 0..1:`, `of kA..kC:`) is
            # every ordinal between its bounds -- one arm per ordinal, as if
            # each were listed. It was a compile error ("could not resolve
            # ordinal for tag ``"). `getImpl` gives it as `Infix(.., lo, hi)`
            # (`nnkRange` once semchecked).
            let bounds =
              if tagNode.kind == nnkRange and tagNode.len == 2:
                @[tagNode[0], tagNode[1]]
              elif tagNode.kind == nnkInfix and tagNode.len == 3 and
                   tagNode[0].kind in {nnkIdent, nnkSym} and
                   tagNode[0].strVal == "..":
                @[tagNode[1], tagNode[2]]
              else: @[]
            if bounds.len == 2:
              let lo = tagOrdOf(bounds[0], enumOrdinals).ord
              let hi = tagOrdOf(bounds[1], enumOrdinals).ord
              for o in lo .. hi:
                var nm = ""
                for eo in enumOrdinals:
                  if eo.ordinal == o: nm = eo.name; break
                if enumOrdinals.len == 0 or nm.len > 0: tags.add (nm, o)
            else:
              tags.add tagOrdOf(tagNode, enumOrdinals)
          for (tagName, tagOrd) in tags:
            arms.add VariantArm(
              tagOrdinal: tagOrd, tagName: tagName,
              fieldNames: armFieldNames,
              fieldTypes: armFieldTypes,
              branchIx: k)   # RFC-0005 S8f: tags of one `of` share it
        # Phase 14 cycle A2. Snapshot the disc enum's full (name,
        # ordinal) domain — walker uses ords to bound the disc
        # range when an `else:` arm is present; witness emitter
        # uses names to render `of <tagName>:` branches for
        # else-covered ordinals.
        var discTags: seq[tuple[name: string, ord: int]]
        for eo in enumOrdinals:
          discTags.add (name: eo.name, ord: eo.ordinal)
        axes.add VariantAxis(discName: discName,
                             discTy: discTy, arms: arms,
                             discTags: discTags)
      else:
        error("symex Phase 11: unsupported object member shape " &
              $member.kind, member)
    # Plain fields stay separate from arm-specific ones — the
    # walker allocates them once (shared across all arms) so
    # they survive discriminator reassignment, matching Nim's
    # runtime memory layout.
    # ADR-0003 D1 invariant: single-axis objects use itVariant;
    # multi-axis objects use itMultiVariant. The two IR kinds
    # are intentionally disjoint.
    if axes.len == 1:
      return tVariant(objectName = s,
        discName = axes[0].discName, discTy = axes[0].discTy,
        arms = axes[0].arms,
        plainFieldNames = plainFieldNames,
        plainFieldTypes = plainFieldTypes,
        discTags = axes[0].discTags,
        nominalId = nominalId(nameSym)).keyedBySym(nameSym)   # RFC-0005 S8j
    else:
      return mkMultiVariant(objectName = s,
        axes = axes,
        plainFieldNames = plainFieldNames,
        plainFieldTypes = plainFieldTypes,
        nominalId = nominalId(nameSym)).keyedBySym(nameSym)   # RFC-0005 S8l
  # ---- Phase-4 plain-record path: only plain fields --------------
  var fields: seq[IRType]
  var names: seq[string]
  for member in recList:
    member.expectKind nnkIdentDefs
    # Phase 15 R9: a ref/ptr-to-object field (e.g. recursive `next: Node`)
    # is classified as a heap REF (`tRef`/`tPtr` of a finite named
    # placeholder), NOT unwrapped to the object value — see
    # `classifyFieldType`. This breaks the self-referential compile-time
    # recursion and matches the R6 field-split heap's `Ref_T`-valued field.
    let rawFty = classifyFieldType(member[member.len - 2]).ty
    let fty = scopedDeclineFieldTy(rawFty, member[0], member)  ## Bug #2
    for j in 0 ..< member.len - 2:
      fields.add fty
      # v64 (§0 clause (b), chapulin round-3): a RAW generic `getImpl`
      # record (e.g. system's `HSlice[T, U]` reached through a slice-valued
      # expression) carries EXPORTED/pragma'd field names as
      # `nnkPostfix("*", name)` / `nnkPragmaExpr(name, pragmas)` /
      # `nnkAccQuoted(name)` — the bare `.strVal` read here crashed macro
      # expansion ("node lacks field: strVal"), aborting the whole file. See
      # `fieldNameStr`/`unwrapFieldNameNode` above (A6, RFC-chapulin-
      # hardening: the SAME fix, generalized and shared with the variant
      # path's three analogous sites).
      names.add fieldNameStr(member[j], j)
  return tTuple(fields, names, objectName = s, nominalId = nominalId(nameSym),
                nameIsRefAlias = isRefWrapped).keyedBySym(nameSym)

const maxArrayIndexSpan = 4096
  ## RFC-0005 S8z. The widest index type an array is modelled over. The
  ## walker allocates one symbol per element, so an `array[int16, T]`
  ## (65536 elements) declines scoped instead of exhausting the budget.

proc arrayIndexBounds*(idx: NimNode): tuple[ok: bool, lo, hi: int64] =
  ## RFC-0005 S8z. The index range `[lo, hi]` of an array type's index node
  ## (`array[<idx>, T]`): an integer size `N` (`0 .. N-1`), a literal range
  ## `lo .. hi` (int or char bounds), a `range[lo .. hi]`, or an ordinal
  ## TYPE -- an enum, `char`/`uint8`/`int8`, a `range` alias. The
  ## walker's array is positional: Nim's index `i` is position `i - lo`.
  ## Before S8z only `N` and `lo .. hi` were read, the low bound was dropped
  ## (an `array[1..3, T]` read `a[1]` at position 1: a false `sxUnsat`), and
  ## any other index type was a macro-time `error`. `ok` is false for an
  ## index type the walker does not model, and the caller declines it
  ## scoped: one wider than `maxArrayIndexSpan`. (`bool` -- its index lowers
  ## to a Z3 Bool, which the walker's integer bounds check and element
  ## select did not take -- was in this list through RFC-0005 S8z; S8am
  ## closed it by coercing the `svBool` index to `svInt` at the two walker
  ## sites that read one, below this proc's own call sites.)
  const litKinds = {nnkCharLit} + {nnkIntLit..nnkUInt64Lit}
  var lo, hi: int64
  if idx.kind in litKinds and idx.kind != nnkCharLit:
    lo = 0; hi = idx.intVal - 1
  elif idx.kind in {nnkInfix, nnkRange} and idx.len >= 2:
    let (a, b) = if idx.kind == nnkInfix and idx.len == 3: (idx[1], idx[2])
                 else: (idx[0], idx[1])
    if idx.kind == nnkInfix and
       (idx[0].kind notin {nnkIdent, nnkSym} or idx[0].strVal != ".."):
      return (false, 0'i64, 0'i64)
    if a.kind notin litKinds or b.kind notin litKinds:
      return (false, 0'i64, 0'i64)
    lo = a.intVal; hi = b.intVal
  elif idx.kind == nnkBracketExpr and idx.len == 2 and
       isBuiltinTypeHead(idx[0], ["range"]):
    let (a, b) = parseRangeBracket(idx)
    lo = a; hi = b
  elif idx.kind == nnkSym:
    let cls = classifyType(idx)
    case cls.ty.kind
    of itInt:
      if cls.ty.hasRange:
        lo = cls.ty.rangeLo; hi = cls.ty.rangeHi
      elif cls.ty.width == 8:
        if cls.ty.signed: (lo = -128; hi = 127)
        else: (lo = 0; hi = 255)
      else:
        return (false, 0'i64, 0'i64)
    of itBool:
      # RFC-0005 S8am (S8z's remainder, item 6): `array[bool, T]` -- Nim's
      # ordinal `false`/`true`, positions 0/1. S8z's own doc comment above
      # (on this proc) listed `bool` among the index types that decline;
      # S8am closes it, now that the walker's array index lowering (below,
      # `isIndex`/`isIndexAssign`) coerces an `svBool` index to `svInt`
      # before calling `arrayIndexConds`/`arraySelect`/`arrayStore`, which
      # only ever took an int-family `SymVal`.
      lo = 0; hi = 1
    else:
      return (false, 0'i64, 0'i64)
  else:
    return (false, 0'i64, 0'i64)
  if hi < lo or hi - lo + 1 > maxArrayIndexSpan:
    return (false, 0'i64, 0'i64)
  (true, lo, hi)

proc classifyArrayBracket(arr: NimNode): ClassifiedType =
  ## RFC-0005 S8z. `array[<idx>, T]`, resolved: an `itArray` of the index
  ## type's size, or the scoped `__unsupported:` decline for an index type
  ## `arrayIndexBounds` does not model.
  let b = arrayIndexBounds(arr[1])
  if not b.ok:
    return unranged(tUninterp("__unsupported:" & arr.repr.strip))
  # RFC-0005 S8am (S8z's remainder, item 5): carry the declared low bound
  # onto the TYPE (`IRType.lo`), not just this call's own `b.lo` local --
  # the witness renderer (`emitTyAndReader`) only ever sees the `IRType`,
  # never this proc's NimNode-derived bounds.
  unranged(tArray(classifyType(arr[2]).ty, int(b.hi - b.lo + 1), lo = b.lo))

proc arrayTypeImpl(n: NimNode): NimNode =
  ## RFC-0005 S8z. `n`'s type resolved to `array[<idx>, T]` (through `var`
  ## and aliases), or nil when it is not an array.
  var ty = n.getTypeImpl
  if ty.kind == nnkVarTy and ty.len == 1: ty = ty[0].getTypeImpl
  if ty.kind == nnkBracketExpr and ty.len == 3 and
     isBuiltinTypeHead(ty[0], ["array"]):
    ty
  else: nil

proc arrayIndexLow*(n: NimNode): int64 =
  ## RFC-0005 S8z. The first index of the array `n` (0 for `array[N, T]`, 1
  ## for `array[1..3, T]`, an enum's first ordinal for `array[E, T]`). Every
  ## index site subtracts it: the walker's element `k` is Nim's `lo + k`.
  let ty = arrayTypeImpl(n)
  if ty == nil: return 0
  let b = arrayIndexBounds(ty[1])
  if b.ok: b.lo else: 0

proc namedRefPlaceholder(objSym: NimNode): IRType   ## fwd decl (RFC-0005 S8ar)

var objectsInClassification {.compileTime.}: seq[string]
  ## RFC-0005 S8ar. The `nominalId`s of the named object types whose record
  ## fields `classifyType` is classifying right now, innermost last. A Nim
  ## type graph is cyclic wherever a container breaks the value nesting:
  ## `type N = ref object; kids: seq[N]` reaches `N` again through
  ## `classifyFieldType(seq[N])` -> `classifyType(N)`. R9's
  ## `namedRefPlaceholder` cut the cycle only for a DIRECT ref field
  ## (`next: N`); a ref reached through a seq/Table/HashSet/tuple/array
  ## element expanded `N` again, without end ("maximum call depth for the
  ## VM exceeded"). A named type met again while its own fields are being
  ## classified is a REFERENCE to that type, not a second expansion of it.

var borrowBaseViews* {.compileTime.}: seq[tuple[node, baseTy: NimNode]]
  ## RFC-0005 S8bc (item 2). The argument nodes of a `{.borrow.}` routine
  ## call the parser is lowering as its BASE routine right now, each with the
  ## base type it is viewed at (`parseBorrowRoutineCall`). Nim gives a
  ## borrowed routine no body: `proc len(d: DSq): int {.borrow.}` is
  ## `len(seq[int](d))`, and the base routine's arms classify their
  ## argument nodes. A macro cannot make a TYPED `seq[int](d)` node (a
  ## synthesized node has no type, and `getTypeInst` on one fails the whole
  ## compile), so the original, typed argument node is kept and classified
  ## at its base type while the rewritten call is parsed. The value side
  ## needs nothing: a conversion between a distinct and its base is a
  ## pass-through in this engine (the walker ejects an `svDistinct` where a
  ## base value is used, `ejectBase`), exactly as for a written `T(d)`.
  ## Pushed and popped by the parser around that one call; empty otherwise.

type GenericArg = tuple[name: string; ty: IRType; id, spelling: string;
                        node: NimNode]
  ## RFC-0005 S8bn (item 8). One type argument of a generic object instance:
  ## the parameter's name, the argument's classified type, and its nominal id
  ## and spelling (the instance's identity and its name in a witness).

var genericFrames {.compileTime.}: seq[seq[GenericArg]]
  ## RFC-0005 S8bn (item 8). The arguments of the generic instances being
  ## classified, innermost last: a parameter named in a body resolves in
  ## the innermost frame (`classifyType`'s first arm).
var genericInProgress {.compileTime.}: seq[string]
  ## RFC-0005 S8bn (item 8). The instance ids being classified: a field
  ## that re-enters one (`next: GNode[T]`) takes its named placeholder.

proc genericParamArg(n: NimNode): int =
  ## RFC-0005 S8bn (item 8). The innermost frame's index of the parameter
  ## `n` names, or -1.
  if genericFrames.len == 0 or n.kind notin {nnkSym, nnkIdent}: return -1
  let nm = n.strVal
  for i, a in genericFrames[^1]:
    if a.name == nm: return i
  -1

proc userGenericObjectImpl(head: NimNode): NimNode =
  ## RFC-0005 S8bn (item 8). The `TypeDef` of a user generic object type
  ## (`type G[T] = object ...` / `ref object ...` / `ptr object ...`), or
  ## nil. RFC-0005 S8bw (item 3): one with a `case` part too.
  if head.kind != nnkSym or head.symKind != nskType or isStdlibDecl(head):
    return nil
  let impl = head.getImpl
  if impl.kind != nnkTypeDef or impl.len < 3 or
     impl[1].kind != nnkGenericParams: return nil
  var u = impl[2]
  if u.kind in {nnkRefTy, nnkPtrTy} and u.len == 1: u = u[0]
  if u.kind != nnkObjectTy or u.len < 3: return nil
  if u[2].kind == nnkRecList:
    for d in u[2]:
      if d.kind notin {nnkIdentDefs, nnkRecCase}: return nil
  impl

proc genericParamNames(impl: NimNode): seq[string] =
  for g in impl[1]:
    if g.kind in {nnkSym, nnkIdent}: result.add g.strVal
    elif g.kind == nnkIdentDefs:
      for j in 0 ..< g.len - 2: result.add g[j].strVal

proc genericArgOf(name: string; arg: NimNode): GenericArg =
  ## RFC-0005 S8bn (item 8). `arg` (a type argument as written in a typed
  ## instance, or in a body under the current frame) for the parameter
  ## `name`.
  let k = genericParamArg(arg)
  if k >= 0:
    var a = genericFrames[^1][k]
    a.name = name
    return a
  (name: name, ty: classifyType(arg).ty, id: nominalId(arg), spelling: arg.repr,
   node: arg)

proc genericInstanceId(head: NimNode; args: seq[GenericArg]): tuple[id, spelling: string] =
  var ids, sps: seq[string]
  for a in args:
    ids.add a.id
    sps.add a.spelling
  (nominalId(head) & "[" & ids.join(",") & "]",
   head.strVal & "[" & sps.join(", ") & "]")

proc classifyGenericInstance(head, impl: NimNode;
                             args: seq[GenericArg]): ClassifiedType

proc genericArgsOfInst(inst: NimNode; impl: NimNode): seq[GenericArg] =
  ## RFC-0005 S8bn (item 8). The arguments of the instance `inst`
  ## (`G[A, B]`), one per parameter of `impl`.
  let names = genericParamNames(impl)
  for i in 1 ..< inst.len:
    if i - 1 < names.len: result.add genericArgOf(names[i - 1], inst[i])

proc classifyGenericInstance(head, impl: NimNode;
                             args: seq[GenericArg]): ClassifiedType =
  ## RFC-0005 S8bn (item 8). A user generic object instance (`G[int]`):
  ## its body classified with each parameter resolved to its argument
  ## (`genericFrames`), keyed on the instance (`genericInstanceId`) and
  ## spelled as written (a witness names `G[int]`). A parent that is a
  ## generic instance (`of GBase[T]`) is classified the same way, with the
  ## arguments the derived type passes it, and joins the hierarchy as a
  ## non-generic parent does (`inheritChain`, `ownedFieldIds`): S8bh's
  ## shared address space. Before S8bn a generic object type was
  ## `feUnsupportedParamType`.
  let (id, spelling) = genericInstanceId(head, args)
  var u = impl[2]
  let wrap = if u.kind in {nnkRefTy, nnkPtrTy}: u.kind else: nnkEmpty
  if u.kind in {nnkRefTy, nnkPtrTy}: u = u[0]
  if id in genericInProgress:
    let ph = tTuple(@[], @[], objectName = spelling, nominalId = id,
                    isPlaceholder = true)
    var inst = nnkBracketExpr.newTree(head)
    for a in args: inst.add a.node
    witnessTypeSyms[id] = inst
    ph.typeKey = id
    return unranged(case wrap
      of nnkRefTy: tRef(ph)
      of nnkPtrTy: tPtr(ph)
      else: ph)
  genericInProgress.add id
  genericFrames.add args
  var fields: seq[IRType]
  var names: seq[string]
  # RFC-0005 S8bw (item 3): a generic case object is classified as a
  # non-generic one is (`classifyObjectRecordFields`), its fields' types
  # resolved in this instance's frame -- its monomorphization. It was
  # `feUnsupportedParamType` (`userGenericObjectImpl` refused a `case`).
  var variant: IRType = nil
  if u[2].kind == nnkRecList:
    for d in u[2]:
      if d.kind == nnkRecCase:
        variant = classifyObjectRecordFields(head, u[2],
                                             isRefWrapped = wrap != nnkEmpty)
        break
  if variant == nil and u[2].kind == nnkRecList:
    for d in u[2]:
      let tn = d[d.len - 2]
      let k = genericParamArg(tn)
      let fty = if k >= 0: genericFrames[^1][k].ty
                else: classifyFieldType(tn).ty
      for j in 0 ..< d.len - 2:
        names.add fieldNameStr(d[j], j)
        fields.add fty
  # The parent: a generic instance, a plain object, or a root.
  var chain: seq[string]
  var ownedNames, ownedIds: seq[string]
  var parentOk = true
  let inh = u[1]
  if inh.kind == nnkOfInherit and inh.len == 1:
    let par = inh[0]
    var parTy: IRType = nil
    if par.kind == nnkBracketExpr and par.len >= 2:
      let pimpl = userGenericObjectImpl(par[0])
      if pimpl == nil: parentOk = false
      else:
        let pargs = genericArgsOfInst(par, pimpl)
        parTy = classifyGenericInstance(par[0], pimpl, pargs).ty
    elif par.kind == nnkSym and par.strVal notin ["RootObj", "RootRef"]:
      parTy = classifyType(par).ty
    if parTy != nil:
      if parTy.kind == itRef: parTy = parTy.refPointeeTy
      elif parTy.kind == itPtr: parTy = parTy.ptrPointeeTy
      if variant != nil:
        # RFC-0005 S8bw (item 3): a generic case object below a plain
        # parent holds the parent's fields first, among its plain ones (as
        # S8bn's non-generic join does). A case part at two levels keeps
        # the decline.
        if parTy.kind != itTuple or parTy.inheritChain.len == 0 or
           variant.kind != itVariant:
          parentOk = false
        else:
          variant.vPlainFieldNames = parTy.fieldNames & variant.vPlainFieldNames
          variant.vPlainFieldTypes = parTy.fields & variant.vPlainFieldTypes
          chain = parTy.inheritChain
          ownedNames = parTy.ownedFieldNames
          ownedIds = parTy.ownedFieldIds
      elif parTy.kind == itVariant and parTy.vInheritChain.len > 0:
        # RFC-0005 S8bw (item 3): a generic object below a generic case
        # object is a variant: the parent's discriminator and branches,
        # its own fields added to the plain ones.
        variant = tVariant(objectName = spelling,
          discName = parTy.vDiscName, discTy = parTy.vDiscTy,
          arms = parTy.vArms,
          plainFieldNames = parTy.vPlainFieldNames & names,
          plainFieldTypes = parTy.vPlainFieldTypes & fields,
          discTags = parTy.vDiscTags, nominalId = id)
        chain = parTy.vInheritChain
        ownedNames = parTy.vOwnedFieldNames
        ownedIds = parTy.vOwnedFieldIds
        names = parTy.vPlainFieldNames & names
      elif parTy.kind != itTuple or parTy.inheritChain.len == 0:
        parentOk = false
      else:
        fields = parTy.fields & fields
        names = parTy.fieldNames & names
        chain = parTy.inheritChain
        ownedNames = parTy.ownedFieldNames
        ownedIds = parTy.ownedFieldIds
    if parentOk:
      chain.add id
      let own = if variant != nil and variant.kind == itVariant:
                  variant.vPlainFieldNames
                else: names
      for nm in own[min(ownedNames.len, own.len) .. ^1]:
        ownedNames.add nm
        ownedIds.add id
  discard genericFrames.pop()
  discard genericInProgress.pop()
  if not parentOk:
    return unranged(tUninterp("__unsupported:" & spelling))
  if variant != nil:
    # RFC-0005 S8bw (item 3): keyed on the instance and named as written.
    var inst = nnkBracketExpr.newTree(head)
    for a in args: inst.add a.node
    witnessTypeSyms[id] = inst
    variant.typeKey = id
    if variant.kind == itVariant:
      variant.vObjectName = spelling
      variant.vNominalId = id
      if chain.len > 0:
        variant.vInheritChain = chain
        variant.vOwnedFieldNames = ownedNames
        variant.vOwnedFieldIds = ownedIds
    else:
      variant.mvObjectName = spelling
      variant.mvNominalId = id
    return unranged(case wrap
      of nnkRefTy: tRef(variant)
      of nnkPtrTy: tPtr(variant)
      else: variant)
  var t = tTuple(fields, names, objectName = spelling, nominalId = id,
                 nameIsRefAlias = wrap != nnkEmpty)
  # The witness names the instance by its head symbol applied to the
  # arguments' own nodes (`userTypeName`), as a symbol names a plain type.
  var inst = nnkBracketExpr.newTree(head)
  for a in args: inst.add a.node
  witnessTypeSyms[id] = inst
  t.typeKey = id
  if chain.len > 0:
    t.inheritChain = chain
    t.ownedFieldNames = ownedNames
    t.ownedFieldIds = ownedIds
  unranged(case wrap
    of nnkRefTy: tRef(t)
    of nnkPtrTy: tPtr(t)
    else: t)

proc borrowViewBase(n: NimNode): NimNode =
  ## RFC-0005 S8bl (item 4). The base type node `n` is viewed at while a
  ## borrowed routine's rewrite parses (`borrowBaseViews`), or nil.
  for i in countdown(borrowBaseViews.high, 0):
    if borrowBaseViews[i].node == n: return borrowBaseViews[i].baseTy
  nil

proc viewTypeKind*(n: NimNode): NimTypeKind =
  ## RFC-0005 S8bl (item 4). `std/macros.typeKind`, through the borrow
  ## views: an argument of a borrowed routine is of its distinct's base
  ## type while the base routine's arms parse it. S8bc consulted the views
  ## in `classifyType` and `valueTypeName` only, so an arm that read
  ## `typeKind` / `getTypeInst` / `getTypeImpl` saw the distinct
  ## (`dsl_parser` reads all three through these).
  let b = borrowViewBase(n)
  if b != nil: macros.typeKind(b) else: macros.typeKind(n)

proc viewTypeInst*(n: NimNode): NimNode =
  ## RFC-0005 S8bl (item 4). `std/macros.getTypeInst`, through the borrow
  ## views (`viewTypeKind`).
  let b = borrowViewBase(n)
  if b != nil: macros.getTypeInst(b) else: macros.getTypeInst(n)

proc viewTypeImpl*(n: NimNode): NimNode =
  ## RFC-0005 S8bl (item 4). `std/macros.getTypeImpl`, through the borrow
  ## views (`viewTypeKind`).
  let b = borrowViewBase(n)
  if b != nil: macros.getTypeImpl(b) else: macros.getTypeImpl(n)

proc classifyType*(ty: NimNode): ClassifiedType =
  ## Map a typed-AST type node to a `ClassifiedType`.
  # RFC-0005 S8bc: an argument of a borrowed routine, viewed at its base.
  for i in countdown(borrowBaseViews.high, 0):
    if borrowBaseViews[i].node == ty:
      return classifyType(borrowBaseViews[i].baseTy)
  # RFC-0005 S8bn (item 8): a generic object's parameter, in its body, is
  # the argument of the instance being classified.
  block:
    let k = genericParamArg(ty)
    if k >= 0: return unranged(genericFrames[^1][k].ty)
  # RFC-0005 S8bn (item 8): an instance written in a generic body (`seq[T]`
  # is typed there; `GBase8[T]` is not) of a user generic object.
  if ty.kind == nnkBracketExpr and ty.len >= 2 and genericFrames.len > 0:
    let gimpl = userGenericObjectImpl(ty[0])
    if gimpl != nil:
      return classifyGenericInstance(ty[0], gimpl, genericArgsOfInst(ty, gimpl))
  # `var T` strip (lvalue parameter).
  if ty.kind == nnkVarTy and ty.len == 1:
    return classifyType(ty[0])
  # Phase 15 G3: a monomorphised `sink T` / `lent T` formal arrives as an
  # nnkCommand `[sink|lent, concreteType]` which carries NO type, so
  # `getTypeInst` below would raise "node has no type". Strip the ownership
  # wrapper on the RAW node first and classify the concrete inner type.
  if ty.kind == nnkCommand and ty.len == 2 and
     isBuiltinTypeHead(ty[0], ["sink", "lent"]):   ## RFC-0005 S8d: by symbol
    return classifyType(ty[1])
  # Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). `owned T` is an
  # ownership annotation out of scope for the ref cluster — map to the
  # `__ownership:owned` placeholder so `allocateSym` raises the classified
  # `heUnsupportedOwnership` (sxUnknown, Invariant 3) at walk time. `owned T`
  # presents as an nnkCommand `[owned, T]` on the RAW node (no type), so match it
  # before `getTypeInst`.
  if ty.kind == nnkCommand and ty.len == 2 and
     isBuiltinTypeHead(ty[0], ["owned"]):   ## RFC-0005 S8d: by symbol
    return unranged(tUninterp("__ownership:owned"))
  # Phase 15 G7: a `static[N]`-dimensioned array formal `array[N, T]` is
  # monomorphized (by `monomorphize`, with `N → nnkIntLit`) into a SYNTHESIZED
  # `nnkBracketExpr[Ident "array", IntLit n, T]` that carries NO type — so
  # `getTypeInst` below would raise "node has no type". Match it structurally on
  # the RAW node first (size is the literal dimension directly; the element type
  # recurses through the normal path).
  if ty.kind == nnkBracketExpr and ty.len == 3 and
     isBuiltinTypeHead(ty[0], ["array"]) and   ## RFC-0005 S8d: by symbol
     ty[1].kind in nnkIntLit..nnkInt64Lit:
    let elemCls = classifyType(ty[2])
    return unranged(tArray(elemCls.ty, int(ty[1].intVal)))
  # Phase 15 Cluster C (C2b): a proc-typed formal (`f: proc(x: T): T`) of a
  # monomorphized generic (e.g. `applyTwice[T]`) arrives as a SYNTHESIZED
  # `nnkProcTy` on the RAW node that carries NO type — `getTypeInst` below would
  # raise "node has no type". Match it structurally first and map to the
  # "__closure" placeholder (the same target as the resolved-node arm below); a
  # proc-valued PARAM is resolved at the call site as an svClosure, never read
  # back as a top-level witness (Invariant 3).
  if ty.kind == nnkProcTy:
    return unranged(tUninterp("__closure"))
  var resolved = ty.getTypeInst
  if resolved.kind == nnkVarTy and resolved.len == 1:
    resolved = resolved[0]
  # RFC-0005 S8bn (item 8): a user generic object instance (`G[int]`).
  if resolved.kind == nnkBracketExpr and resolved.len >= 2:
    let gimpl = userGenericObjectImpl(resolved[0])
    if gimpl != nil:
      return classifyGenericInstance(resolved[0], gimpl,
                                     genericArgsOfInst(resolved, gimpl))
  # Phase 15 Z3c / G3: `sink T` / `lent T` are ownership annotations; symex is
  # by-value, so strip the wrapper and classify T. The node shape varies:
  # `sink[T]` / `lent[T]` is an nnkBracketExpr, but a GENERIC `sink T` formal
  # (Cluster G) presents as an nnkCommand `[sink|lent, T]` — handle both (there
  # is no nnkSinkTy/nnkLentTy node). After monomorphization the inner `T` is the
  # concrete type, so this recurses to the right IRType (e.g. `sink int`→itInt).
  if resolved.kind in {nnkBracketExpr, nnkCommand} and resolved.len == 2 and
     isBuiltinTypeHead(resolved[0], ["sink", "lent"]):   ## RFC-0005 S8d
    return classifyType(resolved[1])
  # ---- structural match: range[lo .. hi] ----
  if resolved.kind == nnkBracketExpr and
     resolved.len == 2 and
     isBuiltinTypeHead(resolved[0], ["range"]):   ## RFC-0005 S8d
    let (lo, hi) = parseRangeBracket(resolved)
    return ranged(rangeBaseType(resolved[1][1]), lo, hi)
  # ---- structural match: array[N, T] ----
  if resolved.kind == nnkBracketExpr and
     resolved.len == 3 and
     isBuiltinTypeHead(resolved[0], ["array"]):   ## RFC-0005 S8d
    # resolved[1] is the index range (typically `0..N-1` from Nim's
    # array literal sugar); we want its size. RFC-0005 S8z: any ordinal
    # index type (`arrayIndexBounds`); its low bound is read back at each
    # index site (`arrayIndexLow`). One the walker does not model declines
    # scoped (it was a macro-time `error`, failing the whole file).
    return classifyArrayBracket(resolved)
  # ---- structural match: anonymous tuples ----
  # `(int, int)` parses to nnkTupleConstr; `tuple[a, b: int]` parses
  # to nnkTupleTy after semcheck.
  if resolved.kind == nnkTupleConstr:
    var fields: seq[IRType]
    var names: seq[string]
    for child in resolved:
      fields.add classifyType(child).ty
      names.add ""
    return unranged(tTuple(fields, names))
  if resolved.kind == nnkTupleTy:
    # Each child is an nnkIdentDefs `[name1, name2, ..., type, default]`.
    var fields: seq[IRType]
    var names: seq[string]
    for id in resolved:
      let fty = classifyType(id[id.len - 2]).ty
      for j in 0 ..< id.len - 2:
        fields.add fty
        names.add id[j].strVal
    return unranged(tTuple(fields, names))
  # ---- nominal object / enum: nnkSym → getImpl yields nnkTypeDef ----
  if resolved.kind == nnkSym:
    let s = resolved.strVal
    let impl = resolved.getImpl
    # Phase 15 G4 (ADR-0008 D4). `type Foo = distinct Bar` → the typed AST's
    # `getImpl` yields `nnkTypeDef[name, genericParams, nnkDistinctTy[Bar]]`.
    # Map to `itDistinct(name = Foo, base = classify(Bar))` — a fresh
    # uninterpreted Z3 sort allocated at walk time. The base recurses, so a
    # nested `type KiloMeters = distinct Meters` classifies to an itDistinct
    # whose base is itself an itDistinct ("Meters"). Checked BEFORE the
    # object/enum/alias paths because a distinct over an object/enum base must
    # be walled off (the wall is the whole point), not unwrapped to the base.
    # RFC-0005 S8z: an array type alias (`type Arr3 = array[3, int]`) is
    # the array. It reached the text-match catch-all below and classified
    # `__unsupported:Arr3`, so a value of the alias was opaque.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkBracketExpr and impl[2].len == 3 and
       isBuiltinTypeHead(impl[2][0], ["array"]):
      let arr = arrayTypeImpl(resolved)
      if arr != nil: return classifyArrayBracket(arr)
    # RFC-0005 S8bc: a named tuple type (`type P = tuple[x, y: int]`) is the
    # tuple. It reached the text-match catch-all below and classified
    # `__unsupported:P`, and a literal of it (`s.add((a, b))` into a
    # `seq[P]`) aborted the compile (`mkTupleLit`'s itTuple assertion). A
    # tuple is structural, so the witness spells it `tuple[x: int, ...]`,
    # the same type.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkTupleTy:
      var fields: seq[IRType]
      var names: seq[string]
      for id in impl[2]:
        let fty = classifyType(id[id.len - 2]).ty
        for j in 0 ..< id.len - 2:
          fields.add fty
          names.add id[j].strVal
      return unranged(tTuple(fields, names))
    # RFC-0005 S8bq: a set type alias (`type CharSet = set[char]`) is the
    # set, as an array alias is the array.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkBracketExpr and impl[2].len == 2 and
       isBuiltinTypeHead(impl[2][0], ["set"]):
      let ety = classifyType(impl[2][1]).ty
      if bitSetDomain(ety).ok:
        return unranged(tBitSet(ety))
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkDistinctTy and impl[2].len == 1:
      # A7 (ADR-0017 Path B): `Rune` from std/unicode → svInt pinned [0, 0x10FFFF].
      # Rune = distinct RuneImpl = distinct int32. RFC-0005 S8d: intercepted
      # by SYMBOL (`isStdlibRuneSym`); the old `Rune`/`RuneImpl` name pair
      # also matched a user's own pair, pinning any-int32 values into
      # [0, 0x10FFFF] (a false `sxUnsat` for a negative). A user `Rune` falls
      # through to the ordinary distinct arm below.
      # Path B is ADDITIVE: the byte-faithful string model (ADR-0006 S-cluster) is untouched.
      if isStdlibRuneSym(resolved):
        return ranged(tInt(64, signed = true), 0'i64, 0x10FFFF'i64)
      let baseCls = classifyType(impl[2][0])
      return unranged(tDistinct(s, baseCls.ty).keyedBySym(resolved))
    # Phase 14 cycle A3. Named-alias for `range[lo..hi]` with int
    # literal bounds — used as a variant discriminator since Nim
    # rejects plain `int` discs (low(T) must be 0). Aliases with
    # symbolic bounds (e.g. `Natural = range[0..high(int)]`) fall
    # through to the dedicated Natural/Positive handlers below.
    #
    # Issue #162: this is the SECOND route into a range — a named alias
    # resolves through `getImpl`, the inline formal through `getTypeInst` —
    # and it carried its own copy of the "every range is 64-bit signed"
    # answer, so fixing only the formal left the identical defect one `type`
    # declaration away. The literal-kind guard widens to the UNSIGNED kinds
    # at the same time: it admitted only `nnkIntLit..nnkInt64Lit`, so a
    # `type Weight = range[0'u16..60_000'u16]` param did not merely classify
    # wrongly, it fell through to the unsupported-type path and degraded the
    # whole run to `sxUnknown`.
    #
    # Issue #163 (audit finding W3): `nnkCharLit` is NOT in
    # `nnkIntLit..nnkUInt64Lit` (it sorts before `nnkIntLit` in the
    # `NimNodeKind` enum), so a char-bounded alias — `type Letter =
    # range['a'..'z']` — fell through this guard the same way the unsigned
    # kinds used to: not to a wrong classification, but off the cliff into
    # the `__unsupported:` catch-all, degrading the WHOLE run to `sxUnknown`.
    # The inline spelling (`proc f(c: range['a'..'z'])`) reaches the
    # structural arm above, which has no kind guard at all, so only the
    # alias route was broken. Admit `nnkCharLit` explicitly (as a set union
    # rather than widening the range literal, since it is not adjacent to
    # the int-literal kinds) so both spellings take the same route.
    # `rangeBaseType` already maps `nnkCharLit` to the historical 64-bit
    # signed answer deliberately — Nim has no `+` on chars, so a char range
    # carries no arithmetic obligation to get wrong — this widening only
    # stops the alias route from declining before it reaches that mapping.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkBracketExpr and
       impl[2].len == 2 and
       isBuiltinTypeHead(impl[2][0], ["range"]) and   ## RFC-0005 S8d
       impl[2][1].kind == nnkInfix and
       impl[2][1][1].kind in ({nnkCharLit} + {nnkIntLit..nnkUInt64Lit}) and
       impl[2][1][2].kind in ({nnkCharLit} + {nnkIntLit..nnkUInt64Lit}):
      let (lo, hi) = parseRangeBracket(impl[2])
      return ranged(rangeBaseType(impl[2][1][1]), lo, hi)
    # Enum: lift to BV[w] integer with type-derived range `[minOrd, maxOrd]`.
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind == nnkEnumTy and
       not (s == "bool" and isStdlibTypeSym(resolved)):
      # Enum lifts to BV[w]. Skip `bool` — it has an enum-shaped impl
      # but is handled below as itBool. RFC-0005 S8d: only SYSTEM's `bool`;
      # a user enum named `bool` is the enum it declares.
      #
      # Issue #163 (audit finding W7). This USED to return `unranged(...)`,
      # with the comment "don't attach hasRange to avoid promotion routing
      # unsigned readers to intVals".
      #
      # CAUTION, corrected by /code-review round 2 (finding R20). The
      # original justification said `promoteSound` "requires `p.ty.signed`
      # and closes that door on its own regardless". That was true only
      # while every enum was `signed = false`. Review finding R2 now derives
      # `signed := minOrd < 0`, so a NEGATIVE-ORDINAL enum param satisfies
      # all three of `promoteSound`'s conditions (`hasRange`, `signed`,
      # `fitsBVWindow`) and IS promoted to a Z3Int — under `isOptimised`,
      # which is the DEFAULT (`types.nim`'s SymexSettings). The door is
      # open, not closed. No wrong verdict has been found through it (the
      # promoted-Int route is exercised by ordinary signed ranged params,
      # and the same sparse-domain imprecision applies identically to the
      # BV route), but it is an untested path in the default mode: see
      # ledger row R20 in `docs/issue-0163-opaque-call-taint.handoff.md`.
      #
      # Left unranged, a plain (non-discriminator) enum param/field was an
      # unconstrained BV, so out-of-domain ordinals were model-reachable —
      # variant DISCRIMINATORS get an ordinal disjunction (see the
      # `promotedDisc`/`ordSet` construction above), plain enum values got
      # nothing. `allocateSym`'s `itInt` arm already asserts `bvRangeConds`
      # off `ty.hasRange` for every int allocation (fields, nested fields,
      # array/seq elements included) — attaching the range here is
      # sufficient; no new plumbing needed.
      #
      # `[minOrd, maxOrd]` — computed from the actual ordinals rather than
      # `0 .. (nValues - 1)` — is a sound REFINEMENT, not exact, for a
      # sparse/holed enum (explicit `= N` values): it excludes nothing legal
      # but admits ordinals that fall in the holes. Exact modelling would
      # need a discTags-style disjunction (as the variant-discriminator path
      # has) and is out of scope here.
      #
      # Issue #163 review finding R2 (three defects, one root cause — all in
      # this arm):
      #   (a) `minOrd` was never tracked; the floor was the literal `0'i64`,
      #       so a NEGATIVE-ordinal enum (`enum roLess = -1, ...`) excluded
      #       its own legal member -1 from the domain the solver enforces.
      #   (b) `bits` was sized from member COUNT (`nValues`), not from the
      #       ordinal MAGNITUDE in play. A 3-member enum with an explicit
      #       `= 300` ordinal got `bits = 8`; the literal construction that
      #       asserts that bound (`mkBitVec[8]`) truncates mod 2^8 (its own
      #       doc: `mkBitVec[8](-1'i8) # = 0xFF`), silently aliasing the
      #       declared bound to 44 and excluding every legal value 45..255.
      #   (c) The literal-kind guard (`nnkIntLit..nnkInt64Lit`) excluded
      #       unsigned-suffixed literals (`nnkUIntLit..nnkUInt64Lit`, the
      #       adjacent range in `NimNodeKind`) the same way the range-alias
      #       guard above once did — widened here to match, defensively;
      #       `getImpl` in practice always normalizes an enum field's value
      #       node to `nnkIntLit` regardless of source suffix, so this has
      #       no live repro through this arm today, but the guard should not
      #       silently disagree with the alias route's.
      #
      # Fix: track both `minOrd` and `maxOrd`; derive `signed` from whether
      # any real ordinal is negative; size `bits` from the magnitude
      # `[minOrd, maxOrd]` actually needs under that signedness (never from
      # arity). `ranged`'s own `withRange` call puts the (possibly negative)
      # bounds on the type, and `bvRangeConds` (`runtime.nim`) already
      # dispatches signed vs. unsigned comparisons off `ty.signed` — the same
      # split a `range[-5..5]`-shaped alias has used since #162, so a
      # negative-ordinal enum joins an already-proven mechanism rather than
      # opening a new one.
      # Issue #163 review round 2 (R18): this loop used to carry its own
      # copy of the ordinal-tracking logic, with an int-literal-only guard
      # that silently fell through to the implicit counter for a
      # tuple-valued field (`a = (1, "alpha")`) -- wrong ordinal, no
      # degrade. Route through `enumFieldOrdinals` (above), the single
      # source of truth both this arm and `dsl_parser.parseExpr`'s
      # `nnkSym` arm now share.
      let fields = enumFieldOrdinals(impl[2])
      var minOrd = fields[0][1]
      var maxOrd = fields[0][1]
      for (_, ord) in fields:
        if ord < minOrd: minOrd = ord
        if ord > maxOrd: maxOrd = ord
      let enumSigned = minOrd < 0
      let bits = enumOrdBitsNeeded(minOrd, maxOrd, enumSigned)
      var cls = ranged(tInt(bits, signed = enumSigned), minOrd, maxOrd)
      # Issue #163 (rev item 1): stamp the enum's own name onto the lifted
      # `itInt` so witness reconstruction (`symex.emitTyAndReader`) can emit
      # `s(readUInt8(...))` instead of a raw reader Nim will not implicitly
      # convert back into an enum-typed slot -- see `IRType.enumName`'s field
      # doc for the full mechanism this unblocks (an enum-typed OBJECT FIELD
      # could not even reach `symexFind`: the generated witness constructor
      # failed to COMPILE).
      cls.ty = cls.ty.withEnumName(s).keyedBySym(resolved)
      return cls
    # #136 FLIPPED (Cluster H Step C, ADR-0022): a NAMED `ref T`/`ptr T` alias
    # whose pointee is a plain (non-variant) object now classifies as
    # `itRef`/`itPtr(FULL pointee)` — true heap identity — instead of
    # unwrapping to the pointee's value shape. RFC-0005 S8l: a VARIANT pointee
    # (case fields, one axis or several) is no longer exempted. ADR-0022
    # sub-decision #1 exempted it because the field-split heap then declined
    # variant reads; ADR-0013 Slices 1-3 (single axis) and S8l (multi-axis,
    # `runtime_heap.mvAxisView`) model them, while the exemption erased the
    # `ref`: a value-modelled `VB = ref object case ...` param faulted on
    # `p != nil` (weInternalWalkerFault), had no aliasing, and declined its
    # constructor (`ctorIsRefAliasedVariant`).
    var underObj: NimNode = nil
    var refWrapNode: NimNode = nil   # non-nil (the nnkRefTy/nnkPtrTy node) iff
                                      # this alias directly wraps `ref object`/
                                      # `ptr object`.
    if impl.kind == nnkTypeDef and impl.len >= 3:
      underObj = impl[2]
      if underObj.kind in {nnkRefTy, nnkPtrTy} and underObj.len == 1:
        let inner = underObj[0]
        if inner.kind == nnkObjectTy:
          refWrapNode = underObj
          underObj = inner
        elif inner.kind == nnkSym:
          # Sym-indirection (`type NodeRef = ref Obj`) — ADR-0022 Round-2
          # CRITICAL fix. Delegate to Obj's OWN classify (dispatches
          # enum/distinct/variant/plain-object exactly as classifyType always
          # has for a named sym), then wrap a plain (non-variant) OBJECT
          # result in `itRef`/`itPtr` so `NodeRef` gets the same heap
          # treatment a direct `type Node = ref object` gets — keyed on OBJ's
          # OWN nominal id (`classifyObjectRecordFields` already stamped it,
          # via this same recursive `classifyType(inner)` call, since `Obj`'s
          # own dispatch reaches the plain-record arm with `nameSym = inner`).
          # A non-object result is returned UNCHANGED — identical to the
          # pre-H1 `return classifyType(inner)`. RFC-0005 S8l: a variant
          # (`VRef = ref VObj`) is wrapped too; it used to be returned
          # unchanged, value-modelling the ref (see the flip note below).
          # RFC-0005 S8ar: `inner` met again inside its own fields (a
          # `seq[NodeRef]` field of `Obj`) is a reference to `Obj`, keyed as
          # `classifyFieldType` keys a direct `NodeRef` field (S8l).
          if nominalId(inner) in objectsInClassification:
            let ph = namedRefPlaceholder(inner)
            return unranged(if underObj.kind == nnkPtrTy: tPtr(ph) else: tRef(ph))
          let objCls = classifyType(inner)
          if objCls.ty.kind in {itTuple, itVariant, itMultiVariant}:   # RFC-0005 S8l: + variants
            return unranged(if underObj.kind == nnkPtrTy: tPtr(objCls.ty)
                             else: tRef(objCls.ty))
          else:
            return objCls
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       underObj != nil and underObj.kind == nnkObjectTy:
      let recList = underObj[2]
      # RFC-0005 S8ar: a type met again while its own fields are classified.
      # A ref/ptr type is a heap reference to itself (the R9 placeholder,
      # sharing its `Ref_` sort through `nominalId`). A VALUE object can only
      # recur through a container (`type O = object; kids: seq[O]`), so its
      # value is unbounded in depth: it declines scoped, as any type the
      # walker does not model (`__unsupported:`, `feUnsupportedParamType`),
      # and `scopedDeclineFieldTy` turns the enclosing seq field into its
      # per-field read decline.
      let oid = nominalId(resolved)
      if oid in objectsInClassification and refWrapNode != nil:
        let ph = namedRefPlaceholder(resolved)
        return unranged(if refWrapNode.kind == nnkPtrTy: tPtr(ph) else: tRef(ph))
      # RFC-0005 S8bc (item 3): a value object met again is UNROLLED, to
      # `maxRecursiveValueDepth` levels below the outermost (a seq of a tree
      # element is leaf-split now, so each level is a real seq of the next).
      # Was the placeholder at the first recurrence (S8ar), so no element
      # of the seq was ever read. Past the bound the element type is the
      # depth placeholder (`recursiveDepthPrefix`), and
      # `scopedDeclineFieldTy` turns the enclosing seq field into a
      # placeholder declining with `seRecursiveValueDepth`. Each level is
      # its own IR type (the next level's `seqElemTy` differs), so a value
      # built at one level and stored at another is conformed or declined by
      # the walker (`conformSV`).
      if objectsInClassification.count(oid) > maxRecursiveValueDepth:
        # Keyed on the type's symbol, so the witness still spells the
        # field's element type (an empty `seq[O]`, never read).
        return unranged(tUninterp(recursiveDepthPrefix &
                                  s).keyedBySym(resolved))
      objectsInClassification.add oid
      var pointee = classifyObjectRecordFields(resolved, recList,
                                               isRefWrapped = refWrapNode != nil)
      objectsInClassification.setLen(objectsInClassification.len - 1)
      if pointee.kind in {itTuple, itVariant}:
        # RFC-0005 S8bh (item 3). A type declared `of` a user type holds its
        # ancestors' fields first, as Nim lays them out: they were missing
        # (`new Derived` never zeroed an inherited field -- a false `sxSat`
        # -- and a witness could not set one). The chain and owners key the
        # sort and field heaps (`refPointeeTypeId`, `fieldHeapKey`).
        # RFC-0005 S8bn (item 8): a case object of the chain makes every type
        # at and below it a variant: the case object's own fields, or its
        # discriminator and branches with the derived type's fields added to
        # the plain ones.
        let info = inheritInfo(resolved)
        if info.chain.len > 0:
          var parTy: IRType = nil
          if info.parent != nil:
            parTy = classifyType(info.parent).ty
            if parTy.kind in {itRef, itPtr}:
              parTy = if parTy.kind == itRef: parTy.refPointeeTy
                      else: parTy.ptrPointeeTy
          if pointee.kind == itTuple and parTy != nil and
             parTy.kind == itVariant:
            var v = tVariant(objectName = pointee.objectName,
              discName = parTy.vDiscName, discTy = parTy.vDiscTy,
              arms = parTy.vArms,
              plainFieldNames = parTy.vPlainFieldNames & pointee.fieldNames,
              plainFieldTypes = parTy.vPlainFieldTypes & pointee.fields,
              discTags = parTy.vDiscTags,
              nominalId = pointee.nominalId).keyedBySym(resolved)
            pointee = v
          elif pointee.kind == itVariant and parTy != nil and
               parTy.kind == itTuple:
            pointee.vPlainFieldNames = parTy.fieldNames & pointee.vPlainFieldNames
            pointee.vPlainFieldTypes = parTy.fields & pointee.vPlainFieldTypes
          elif pointee.kind == itTuple and parTy != nil and
               parTy.kind == itTuple:
            pointee.fields = parTy.fields & pointee.fields
            pointee.fieldNames = parTy.fieldNames & pointee.fieldNames
          if pointee.kind == itTuple:
            pointee.inheritChain = info.chain
            pointee.ownedFieldNames = info.ownedNames
            pointee.ownedFieldIds = info.ownedIds
          else:
            pointee.vInheritChain = info.chain
            pointee.vOwnedFieldNames = info.ownedNames
            pointee.vOwnedFieldIds = info.ownedIds
      if refWrapNode != nil:   # RFC-0005 S8l: variants too
        return unranged(if refWrapNode.kind == nnkPtrTy: tPtr(pointee)
                         else: tRef(pointee))
      # A non-ref object (plain or variant).
      return unranged(pointee)
  # ---- structural match: Nim's builtin set[T] ----
  # RFC-0005 S8bq (item 2). `set[T]` over a base type with at most 2^16
  # values (`bitSetDomain`: `bool`, `char`, an enum, an 8- or 16-bit int, a
  # range) is one bit-vector. It reached the `__unsupported:` catch-all
  # below, so every set-typed parameter or value declined. Nim rejects any
  # other base type, so the fall-through is a defensive one.
  if resolved.kind == nnkBracketExpr and resolved.len == 2 and
     isBuiltinTypeHead(resolved[0], ["set"]):
    let ety = classifyType(resolved[1]).ty
    if bitSetDomain(ety).ok:
      return unranged(tBitSet(ety))
  # ---- structural match: seq[T] / Table[K, V] / HashSet[T] ----
  # RFC-0005 S8d: the container models apply only to the STDLIB head
  # (`system.seq`, `tables.Table`, `sets.HashSet`, ...). A user generic of the
  # same name -- `type Table[K, V] = array[3, V]` -- is a user generic
  # instance like any other and reaches the `__unsupported:` catch-all below
  # (a recorded `feUnsupportedParamType`), never the hash-table model.
  if resolved.kind == nnkBracketExpr and
     isBuiltinTypeHead(resolved[0],
                       ["seq", "Table", "HashSet", "Atomic"]):
    let head = resolved[0].strVal
    case head
    of "seq":
      if resolved.len != 2:
        error("symex (Phase 5): seq type must be `seq[T]`", resolved)
      let elem = classifyType(resolved[1]).ty
      return unranged(tSeq(elem))
    of "Table":
      if resolved.len != 3:
        error("symex (Phase 5): Table type must be `Table[K, V]`", resolved)
      let kty = classifyType(resolved[1]).ty
      let vty = classifyType(resolved[2]).ty
      return unranged(tTable(kty, vty))
    of "HashSet":
      if resolved.len != 2:
        error("symex (Phase 5): HashSet type must be `HashSet[T]`", resolved)
      let ety = classifyType(resolved[1]).ty
      return unranged(tSet(ety))
    of "Atomic":
      # Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). `Atomic[T]`
      # (`std/atomics`) is out of scope for the ref cluster — map to an
      # `__ownership:*` placeholder so `allocateSym` raises the classified
      # `heUnsupportedOwnership` (sxUnknown, Invariant 3) at walk time rather
      # than a compile error. RFC-0005 S8d: the `WeakRef` spelling this arm
      # also matched is removed -- Nim's lib has no `WeakRef` type, so under
      # the by-symbol rule it could only ever match a USER type of that name
      # (a name-only model, as S8c's `replaceAll`/`bytes`). A user `WeakRef`
      # is a user generic: the `__unsupported:` catch-all below.
      return unranged(tUninterp("__ownership:" & head))
    else: discard
  # Phase 15 Cluster R (R1a, ADR-0010). Inline `ref T` / `ptr T` — classify to
  # `tRef`/`tPtr` of the pointee (REPLACING the pre-R unwrap-to-pointee
  # behaviour, reconciliation §A:128). The walker STUBS these via
  # `allocateSym(itRef/itPtr)` → `heUnresolvedRef` (sxUnknown) until R1+ land the
  # logical-heap semantics.
  if resolved.kind == nnkRefTy and resolved.len == 1:
    return unranged(tRef(classifyType(resolved[0]).ty))
  if resolved.kind == nnkPtrTy and resolved.len == 1:
    return unranged(tPtr(classifyType(resolved[0]).ty))
  # Phase 15 Cluster C (C2a): a proc/closure type (`proc(...): T`) — a closure
  # as a top-level SUT param/result type is UNSUPPORTED (Invariant 3). Map it to
  # an `itUninterp` placeholder with the recognisable "__closure" marker name;
  # `emitTyAndReader` renders a proc placeholder + `{.warning.}` for it rather
  # than crashing (closures are constructed in-body — C2a — but never
  # reconstructed as a top-level witness).
  if resolved.kind == nnkProcTy:
    return unranged(tUninterp("__closure"))
  # ---- otherwise: text match on the resolved type name ----
  let s = resolved.repr.strip
  # RFC-0005 S8d: the spellings below are the BUILTIN types. A user type of
  # the same name -- `type Natural = int` (no lower bound), `type int8 = int`
  # (64 bits), `type string = seq[char]` -- is not one of them, and a user
  # alias or generic instance has no structural arm above, so it takes the
  # catch-all's recorded `feUnsupportedParamType`, exactly as a user alias
  # of any other name always has. `typeSpelling` tags a non-stdlib symbol
  # `user:`, which no arm matches.
  case (if resolved.kind in {nnkIdent, nnkSym}: typeSpelling(resolved) else: s)
  of "bool":     unranged(tBool())
  of "string":   unranged(tString())
  of "char":     unranged(tInt(8,  signed = false, isChar = true))  ## Phase 15
                                                     ## Z3c: char = uint8;
                                                     ## RFC-0005 S8am: `isChar`
                                                     ## distinguishes it from
                                                     ## `byte`/`uint8` at
                                                     ## witness-render time.
  of "byte":     unranged(tInt(8,  signed = false))  ## Phase 15 S7a: byte = uint8
                                                     ## (bytes(s) element type)
  of "float", "float64": unranged(tFloat64())        ## Phase 15 F1
  of "float32":  unranged(tFloat32())                ## Phase 15 F1
  of "int":      unranged(tInt(64, signed = true))
  of "int8":     unranged(tInt(8,  signed = true))
  of "int16":    unranged(tInt(16, signed = true))
  of "int32":    unranged(tInt(32, signed = true))
  of "int64":    unranged(tInt(64, signed = true))
  of "uint":     unranged(tInt(64, signed = false))
  of "uint8":    unranged(tInt(8,  signed = false))
  of "uint16":   unranged(tInt(16, signed = false))
  of "uint32":   unranged(tInt(32, signed = false))
  of "uint64":   unranged(tInt(64, signed = false))
  of "Natural":  ranged(tInt(64, signed = true), 0'i64, high(int64))
  of "Positive": ranged(tInt(64, signed = true), 1'i64, high(int64))
  else:
    # RFC-0005 S8bl (item 4). A plain alias -- `type Hash* = int`
    # (std/hashes), `type IntSeq = seq[int]`, a user `Natural = int` -- IS
    # the type it names: Nim gives the two one identity. It reached this
    # catch-all and declined (`feUnsupportedParamType`), so a `Hash` local
    # held a placeholder and every value of a user alias was opaque. The
    # aliased type node is classified, by its own symbol (S8d's rule: a
    # user `Natural = int` is a plain `int`, not `system.Natural`).
    if resolved.kind == nnkSym:
      let aliasImpl = resolved.getImpl
      if aliasImpl.kind == nnkTypeDef and aliasImpl.len >= 3 and
         aliasImpl[2].kind in {nnkSym, nnkBracketExpr} and
         aliasImpl[2] != resolved:
        return classifyType(aliasImpl[2])
    # RFC-chapulin-hardening CR-2b (Cluster 2 — Crash-totality, round-2
    # Option 2). This text-match catch-all used to `error()` at MACRO-
    # EXPANSION time, aborting compilation of the whole test file before any
    # proc body was walkable — strictly worse than `sxUnknown`, and unlike
    # CR-2a's expression-position catch-all there is no `ctx`/`preamble` to
    # taint here (`classifyType` takes neither), so no sound dummy value is
    # possible. Instead, map to an `itUninterp` placeholder carrying the
    # recognisable `"__unsupported:" & s` marker name, mirroring the
    # `WeakRef`/`Atomic` -> `__ownership:*` precedent above (~404-410) and
    # the `nnkProcTy` -> `__closure` precedent (~427-428). `allocateSym`'s
    # `itUninterp` arm special-cases this prefix and raises the classified
    # `SymexClassifiedDegradeError` (kind `feUnsupportedParamType`) at
    # PARAMETER-ALLOCATION time — before the body is walked — so the whole
    # run degrades to `sxUnknown` rather than crashing or aborting the build.
    unranged(tUninterp("__unsupported:" & s))

proc namedRefPlaceholder(objSym: NimNode): IRType =
  ## Phase 15 R9 (ADR-0010). Build the `tRef`/`tPtr` POINTEE for a ref/ptr-typed
  ## OBJECT FIELD (e.g. the recursive `next: Node` of a linked list). The pointee
  ## is an EMPTY-fielded named `itTuple` placeholder carrying ONLY the object's
  ## name — NOT the object's full field structure. This is deliberate: a
  ## self-referential type (`Node` whose `next: Node`) would make the IR cyclic,
  ## and `$`/`==` over `IRType` recurse STRUCTURALLY into every field — a cyclic
  ## IR would infinite-loop both at compile time (this classifier) and at runtime
  ## (`refPointeeTypeId` = `$pointee`). The walker never needs the pointee's
  ## fields for a ref-typed field: the `Ref_<name>` SORT keys on this stable name
  ## (`refPointeeTypeId`), the field VALUE sort comes from `dElemTy` (the field's
  ## own type, resolved from the TYPED AST at the access site), and the field
  ## type at a deeper `.field` comes from `classifyType(wholeDotExpr)` (again the
  ## typed AST), so an empty-fielded named placeholder is sufficient and FINITE.
  let nm = if objSym.kind in {nnkSym, nnkIdent}: objSym.strVal else: objSym.repr
  tTuple(@[], @[], objectName = nm, nominalId = nominalId(objSym),
         isPlaceholder = true).keyedBySym(objSym).withInheritInfo(objSym)

proc isObjectTypeSym(sym: NimNode): bool =
  ## CR-19: Returns true iff `sym` (a nnkSym/nnkIdent) refers to a user-defined
  ## OBJECT type (nnkTypeDef over nnkObjectTy). Primitive built-in types (`int`,
  ## `float`, `bool`, etc.) have `getImpl` returning nnkEmpty or a non-TypeDef
  ## node, so they return false. This guards the placeholder arm in
  ## `classifyFieldType` — only object pointees should use the named placeholder
  ## (to break self-referential cycles); primitive pointees (`ref int`, `ref float`)
  ## should fall through to `classifyType(ty)` which produces `tRef(tInt(64,true))`
  ## etc. via the inline-nnkRefTy arm at lines 411-414 — the same IR as the
  ## deref site's `dElemTy`, keeping the Z3 sort names byte-identical.
  if sym.kind notin {nnkSym, nnkIdent}: return false
  let impl = try: sym.getImpl except: return false
  if impl.kind != nnkTypeDef or impl.len < 3: return false
  impl[2].kind == nnkObjectTy

proc classifyFieldType*(ty: NimNode): ClassifiedType =
  ## Phase 15 R9 (ADR-0010). Classify an OBJECT FIELD's type. A field whose type
  ## is a `ref`/`ptr` to an object (named `type N = ref object` OR an inline
  ## `ref Obj`) is classified as `tRef`/`tPtr` of a finite NAMED PLACEHOLDER
  ## (`namedRefPlaceholder`) rather than UNWRAPPED to the object value. This is
  ## the R9 ref-typed-field extension: a ref-typed field is a ref (a heap address
  ## modelled as `Ref_<name>`), stored/loaded through the R6 field-split heap as
  ## a `Ref_T` value — and crucially it BREAKS the compile-time infinite recursion
  ## a self-referential field (`next: Node`) would otherwise cause in
  ## `classifyType`'s named-`ref object` unwrap. Non-ref/ptr fields delegate to
  ## the ordinary `classifyType` (a plain value field is modelled by value, as
  ## before — no behaviour change for Phase-4 record fields).
  ##
  ## CR-19: for `ref PRIMITIVE` fields (e.g. `p: ref int`), the pointee sym was
  ## previously matched by the `inner.kind in {nnkSym, nnkIdent}` guard and
  ## received the named-tuple placeholder — producing sort `Ref_int__` — while
  ## the deref site's `dElemTy` produced `tInt(64,true)` → sort `Ref_i64_s`,
  ## causing a Z3SortMismatchError → sxUnknown. Fix: gate the placeholder on
  ## `isObjectTypeSym` — only actual object types get the placeholder; primitives
  ## fall through to `classifyType(ty)` which produces `tRef(tInt(64,true))` etc.
  # A NAMED ref/ptr object type, reached either as the field-type node directly
  # (`next: Node`) OR as the resolved TYPE of a derived ref-valued expression
  # (`getTypeInst` of `n.next` yields the `Node` sym). In both cases the sym's
  # `getImpl` is `nnkTypeDef[name, _, nnkRefTy|nnkPtrTy]`.
  var nameSym: NimNode = nil
  if ty.kind == nnkSym:
    nameSym = ty
  else:
    let inst = ty.getTypeInst
    if inst.kind == nnkSym:
      nameSym = inst
  if nameSym != nil:
    let impl = nameSym.getImpl
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind in {nnkRefTy, nnkPtrTy} and impl[2].len == 1:
      let inner = impl[2][0]
      # Only OBJECT pointees route to the heap-ref model here; a `ref int`-style
      # named alias still has a primitive pointee and the existing `classifyType`
      # ref arms (R1a) handle it. We detect the object case structurally.
      # CR-19: `inner.kind in {nnkSym, nnkIdent}` previously matched primitive
      # syms too (e.g. `int`). Now gate on `isObjectTypeSym` to match only real
      # object types and let primitive pointees fall to `classifyType(ty)`.
      if inner.kind == nnkObjectTy or isObjectTypeSym(inner):
        # RFC-0005 S8l: a sym-indirection alias (`NodeRef = ref Obj`) keys
        # the placeholder on `Obj`, as `classifyType` keys the pointee of a
        # `NodeRef` param (`tRef(classifyType(Obj))`). Keyed on the alias,
        # a `NodeRef` field and every other `NodeRef` position named two
        # `Ref_` sorts for one Nim type -- a Z3 sort error on the first
        # cross-use (`h.p != nil and h.p.x == 5`), for a plain object as for
        # the case object S8l now heap-models.
        let placeholder = namedRefPlaceholder(
          if inner.kind == nnkSym: inner else: nameSym)
        return if impl[2].kind == nnkRefTy: unranged(tRef(placeholder))
               else: unranged(tPtr(placeholder))
  # An INLINE `ref Obj` / `ptr Obj` field (the type node is itself nnkRefTy/PtrTy
  # over an object sym).
  # CR-19: gate inner-sym case on `isObjectTypeSym` (not just `nnkSym/nnkIdent`)
  # so inline `ref int` / `ref float` etc. fall through to `classifyType(ty)`.
  let resolved = ty.getTypeInst
  if resolved.kind in {nnkRefTy, nnkPtrTy} and resolved.len == 1:
    let inner = resolved[0]
    if inner.kind == nnkObjectTy or isObjectTypeSym(inner):
      let nm = if inner.kind in {nnkSym, nnkIdent}: inner.strVal else: ""
      let placeholder = tTuple(@[], @[], objectName = nm,
                               nominalId = (if inner.kind in {nnkSym, nnkIdent}: nominalId(inner) else: ""),
                               isPlaceholder = true).keyedBySym(inner).withInheritInfo(inner)
      return if resolved.kind == nnkRefTy: unranged(tRef(placeholder))
             else: unranged(tPtr(placeholder))
  classifyType(ty)
