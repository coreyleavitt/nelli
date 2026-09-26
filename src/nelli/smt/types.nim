## Symex IR + public result/target/settings types.
##
## NB: imports of std/tables / std/sequtils / std/strutils live near
## the bottom of the file (right above the rendering helpers); the
## rest of this module is type definitions only.

import std/tables
import std/options   ## Phase 15 R12: Option[string] for HeapSnapshotEntry.aliasRef/pointsTo
export tables, options
##
## The architecture (per [docs/SYMEX_PLAN.md](../../../docs/SYMEX_PLAN.md))
## is a classic front-end / back-end split:
##
##   typed Nim AST  ─[dsl_parser]→  SymexProgram (this file)
##                                       │
##                                       └─[runtime]→  SymexResult
##
## The IR is intentionally small. Each phase widens it; this file
## carries only the Phase-1 fragment (int/bool, arithmetic +
## comparison, `if` / `block` / target labels). Later phases extend
## with `let`, `assign`, `return`, composite types, function calls,
## loops, etc.
##
## `ref object` is used for the variant nodes so the parser can
## construct them with ordinary heap allocation; the runtime walks
## them without ever needing to mutate the structure (it's an
## immutable view).

type
  IRBinop* = enum
    bAdd, bSub, bMul, bDiv, bMod
    bAnd, bOr, bXor              ## bool×bool→bool, or bitwise on integers —
                                 ## the runtime dispatches by operand type
    bShl, bShr                   ## bit-shifts on integers; sign-aware shr
                                 ## maps to ashr (signed) / lshr (unsigned)
    bEq, bNe                     ## polymorphic equality
    bLt, bLe, bGt, bGe           ## comparison; signed vs unsigned by IRType

  IRUnop* = enum
    uNot                         ## boolean negation
    uNeg                         ## arithmetic negation

  IRTypeKind* = enum
    itInt    ## Any fixed-width Nim integer
    itBool
    itString ## Phase 5: Nim `string`, encoded as Z3String.
    itTuple  ## Records: tuples (anonymous or named) and objects.
             ## Both lower to `svTuple` with per-field SymVals.
    itArray  ## Static `array[N, T]` — Phase 4 supports primitive `T`
             ## and tuples-of-primitive `T`; nested arrays defer to #142.
    itSeq    ## Phase 5: dynamic `seq[T]` via Z3 array theory.
    itTable  ## Phase 5: `Table[K, V]` via two Z3 arrays (data + present).
    itSet    ## Phase 5: `HashSet[T]` via `Z3Array[T, Z3Bool]`.
    itVariant ## Phase 11: Nim variant object — a tagged sum type.
              ## Discriminator + per-arm field records, modelled
              ## structurally rather than flattened. See PHASE11_PLAN.md.
    itMultiVariant ## Phase 14 (ADR-0003 D1): Nim variant object with
              ## MULTIPLE `nnkRecCase` blocks — a product of tagged sum
              ## axes. Single-recCase objects keep using `itVariant`;
              ## `itMultiVariant` requires `mvAxes.len >= 2` (asserted by
              ## `mkMultiVariant`). The two kinds are intentionally
              ## structurally disjoint: canonical encodings differ
              ## (`Vr:` vs `MVr:`), cache partitions are disjoint by
              ## design.
    itUninterp ## Phase 15 Z3b: uninterpreted reference sort (the IR type of
              ## an `svUninterpRef`). Produced by cluster E; carries the
              ## sort name only.
    itFloat32  ## Phase 15 F1: IEEE float32 (Z3Fp[8,24]).
    itFloat64  ## Phase 15 F1: IEEE float64 (Z3Fp[11,53]); Nim `float`.
    itRef      ## Phase 15 Cluster R (R1a, ADR-0010): a `ref T` type — a
               ## phantom-typed reference. Carries `refPointeeTy: IRType`. The
               ## logical-heap model (per-type `Z3Array[Ref_T, T]`) lands R1+;
               ## R1a is structural and the walker STUBS any `itRef` it reaches
               ## with a classified `heUnresolvedRef` → `sxUnknown` (Invariant 3).
    itPtr      ## Phase 15 Cluster R (R1a, ADR-0010): a `ptr T` type — same heap
               ## model as `itRef`. Carries `ptrPointeeTy: IRType`. Pointer
               ## arithmetic is classified `hePtrArith` in R8; R1a STUBS it as
               ## `heUnresolvedRef`.
    itDistinct ## Phase 15 G4 (ADR-0008 D4): a `distinct T` type. Maps to a
               ## FRESH uninterpreted Z3 sort named `distinctName` (a type wall
               ## between the distinct type and its base). Carries the base
               ## `IRType` so the walker can allocate/eject through to it. The
               ## sort is allocated once per distinct name per run on
               ## `WalkerStatics.distinctSorts`; inject/eject uninterpreted
               ## functions + (decidable-base-only) bijectivity axioms model the
               ## round-trip. Nesting (`distinct (distinct U)`) recurses through
               ## `distinctBase`.

  VariantArm* = object
    ## One arm of an `itVariant`. The tag ordinal is the
    ## discriminator value that selects this arm; the field
    ## names + types describe the record valid under that tag.
    tagOrdinal*: int
    tagName*:    string
    fieldNames*: seq[string]
    fieldTypes*: seq[IRType]
    isElse*:     bool
      ## Phase 14 cycle A2 (forward-compat): true iff this arm is the
      ## `else:` branch of an `nnkRecCase`. Walker-time arm membership
      ## constraint for an else-arm is `AND(disc != other.tagOrdinal)`
      ## over the non-else arms on the same axis — computed lazily,
      ## never materialized as a tag-set seq (catastrophic for non-
      ## enum discriminator types per A3). Default false preserves
      ## Phase 11 behavior for every existing `VariantArm` literal.

  VariantAxis* = object
    ## Phase 14 (ADR-0003 D1). One discriminator axis of an
    ## `itMultiVariant`. Each `nnkRecCase` block in a multi-recCase
    ## object becomes one `VariantAxis`.
    discName*:     string
    discTy*:       IRType
    arms*:         seq[VariantArm]
    discTags*: seq[tuple[name: string, ord: int]]
      ## Phase 14 cycle A2. Full (name, ordinal) domain of `discTy`'s
      ## enum, populated by typebridge. The walker uses ordinals to
      ## bound the disc range when an `else:` arm is present on this
      ## axis; the witness emitter uses names to render `of <tagName>:`
      ## branches for else-covered ordinals.

  IRType* = ref object  ## ref because itTuple/itArray/itVariant recurse.
    case kind*: IRTypeKind
    of itInt:
      width*: int
      signed*: bool
      hasRange*: bool          ## Issue #162. A `range[lo..hi]` IS a type in
      rangeLo*: int64          ## Nim, so its bounds belong here rather than
      rangeHi*: int64          ## only on `IRParam`. Carrying them on the
                               ## TYPE is what makes them survive into an
                               ## object field, a nested object, an array
                               ## element and a seq element for free:
                               ## `allocateSym` already recurses over types,
                               ## and asserts the bounds wherever it lands.
                               ##
                               ## Before this, `ClassifiedType.range` was
                               ## plumbed ONLY into `IRParam`, so a
                               ## range-typed FIELD kept its bounds nowhere.
                               ## Z3 was free to pick a value outside the
                               ## declared range and witness construction
                               ## then raised `RangeDefect` out of the
                               ## caller's own test process — a crash, not a
                               ## wrong verdict.
                               ##
                               ## NOT part of `IRType.==`: equality here is
                               ## structural (shape/sort), and a refinement
                               ## of the value set is not a different shape.
                               ## The same reasoning `isPlaceholder` and
                               ## `nominalId` are excluded under. It IS part
                               ## of `canonicalize`, because two programs
                               ## that differ only in a field's declared
                               ## bounds have genuinely different verdicts
                               ## and must not share a cache entry.
      enumName*: string        ## Issue #163 (rev item 1). "" for an ordinary
                               ## int/range; the enum type's OWN name (e.g.
                               ## "Ordering") when this `itInt` is the lifted
                               ## representation of a Nim `enum` (see
                               ## `dsl_typebridge.classifyType`'s enum arm).
                               ## Witness reconstruction
                               ## (`symex.emitTyAndReader`) needs the name to
                               ## emit a reader Nim will actually accept for
                               ## an enum-typed slot -- `readUInt8`/
                               ## `readUInt16` alone produce a raw unsigned
                               ## value, and Nim will not implicitly convert
                               ## that back into an enum-typed FIELD inside a
                               ## generated `nnkObjConstr`, so the whole
                               ## witness-rebuilding proc fails to COMPILE
                               ## (`symexFind` could not even be called on a
                               ## proc taking an object with a plain enum
                               ## field). Wrapping the reader in
                               ## `EnumName(...)` fixes the call-site type;
                               ## this field is what tells the reader which
                               ## name to wrap with.
                               ##
                               ## Analogous to `itTuple.nominalId` — nominal
                               ## identity carried for WITNESS/CODEGEN
                               ## purposes, not a structural/verdict property
                               ## — same reasoning `isPlaceholder` and
                               ## `nominalId` are excluded under: NOT part of
                               ## `IRType.==` (two enums with the same
                               ## width/signedness/declared range behave
                               ## byte-identically to every walker arm that
                               ## consumes an `itInt` — the walker never
                               ## reads a name). IS rendered by
                               ## `canonicalize` anyway (the conservative
                               ## default the field's own review round
                               ## specifies for a new `IRType` field, mirrors
                               ## `itTuple.objectName`'s own canonicalize
                               ## treatment) — cheap, and it forecloses any
                               ## future doubt about a generic/overload
                               ## dispatch keying on the enum's name.
    of itBool:
      discard
    of itTuple:
      fields*: seq[IRType]
      fieldNames*: seq[string]   ## "" for positional / anonymous; nominal
                                 ## name for named-tuples and objects.
      objectName*: string        ## "" for tuple types; the nominal name
                                 ## (e.g., "Point") for object types — the
                                 ## witness constructor uses it.
      nominalId*: string         ## canonical symbol-unique nominal identity
                                 ## of a named object / generic instantiation;
                                 ## "" for anonymous tuples. Populated at
                                 ## Cluster H Step A; consumed at Step B.
      nameIsRefAlias*: bool      ## Cluster H Step C (ADR-0022 Round-2): true
                                 ## iff `objectName` NAMES A REF/PTR ALIAS
                                 ## ITSELF (`type Node = ref object` — the
                                 ## object body has no separate nameable
                                 ## symbol; `Node` denotes the `ref` type, and
                                 ## Nim's `Node(field: val, ...)` constructor
                                 ## sugar ALREADY allocates and returns a
                                 ## `ref Node`). Witness rendering
                                 ## (`emitTyAndReader`'s `itRef`/`itPtr` arm,
                                 ## `symex.nim`) MUST NOT additionally wrap
                                 ## such a pointee in `new(objectName)` +
                                 ## `cell[] = objectName(...)` — that double-
                                 ## allocates (`new(Node)` tries to build `ref
                                 ## Node` = `ref ref Body`, a genuine Nim type
                                 ## mismatch). False for a plain (non-ref)
                                 ## named object (`type Point = object`) and
                                 ## for a sym-indirected pointee (`type
                                 ## NodeRef = ref Obj` — `Obj` IS a separately
                                 ## nameable plain object; `Obj(...)` is an
                                 ## ordinary value constructor, needs the
                                 ## `new`+wrap).
      isPlaceholder*: bool       ## Cluster H Step C (ADR-0022 Round-2):
                                 ## explicit PROVENANCE flag — `true` ONLY for
                                 ## a recursion-truncated placeholder pointee
                                 ## (`namedRefPlaceholder`, empty-fielded by
                                 ## construction, built to break a
                                 ## self-referential field's compile-time
                                 ## recursion), `false` for every REAL object
                                 ## shape (including a legitimately zero-field
                                 ## `type Token = ref object`). Replaces the
                                 ## old `fields.len == 0` witness heuristic
                                 ## (`isRecursionPlaceholder`, symex.nim /
                                 ## types.nim), which was AMBIGUOUS for a
                                 ## genuine zero-field object — a proven
                                 ## non-nil `p: Token` would have mis-rendered
                                 ## as `nil`. `IRType.==` stays STRUCTURAL and
                                 ## does NOT compare this field (a full
                                 ## pointee and its own placeholder are
                                 ## `==`-unequal but share a Z3 sort via
                                 ## `nominalId` — see `refPointeeTypeId`); this
                                 ## flag is a WITNESS-RENDERING concern only.
    of itArray:
      elemTy*: IRType
      size*: int
    of itString:
      discard
    of itSeq:
      seqElemTy*: IRType
      seqUnsupportedFieldReason*: string
        ## Round-6 Bug #2 (scoped decline). "" (the default) for an ordinary
        ## `itSeq` — set by `dsl_typebridge.tUnsupportedFieldSeq` for a
        ## declared object/variant field whose element kind
        ## `isBackedSeqElemTy` declines. See the doc block beside
        ## `isUnsupportedFieldPlaceholder` (below) for the full mechanism.
        ## `seqElemTy` stays the REAL element type even when this is set —
        ## needed so the witness reader can still build a correctly-typed
        ## (if content-empty) `seq[T]`.
      seqUnsupportedFieldKind*: SymexErrorKind
        ## N47-followup (walker v110): the classified `SymexErrorKind` a
        ## downstream READ of this placeholder should surface, meaningful
        ## only when `seqUnsupportedFieldReason.len > 0`. Defaults (via
        ## `tUnsupportedFieldSeq`'s `kind` param) to `seNestedSeqUnsupported`
        ## — the ORIGINAL, still-correct classification for a declared
        ## field/local whose element TYPE is structurally unbacked. An
        ## OPERATION-level degrade (e.g. `iekSeqAdd`'s width/elem-support
        ## gap on an otherwise-backed element type, runtime.nim) passes
        ## `weInternalWalkerFault` instead — that receiver's element type IS
        ## backed in general (`isBackedSeqElemTy` would say so); only THIS
        ## specific mutation's implementation is incomplete, so a downstream
        ## read of the rebound receiver must not claim "nested seq element
        ## type is not supported" (false) via `seNestedSeqUnsupported`.
        ## Mirrored onto the runtime `SymVal` alongside
        ## `seqUnsupportedFieldReason` (runtime.nim) so the read-side
        ## chokepoint (`placeholderReadDeclineMsg`/`declinePlaceholderInLower`)
        ## can report the correct kind without re-deriving it.
    of itTable:
      tabKeyTy*: IRType
      tabValTy*: IRType
    of itSet:
      setElemTy*: IRType
    of itVariant:
      vDiscName*:        string    # discriminator field name (any name, not just "kind")
      vDiscTy*:          IRType    # must be itInt (the enum's int representation)
      vArms*:            seq[VariantArm]   # arm-specific fields ONLY
      vDiscTags*:        seq[tuple[name: string, ord: int]]
        ## Phase 14 cycle A2. The disc enum's full (name, ordinal)
        ## domain, populated by typebridge. The walker uses the
        ## ordinals to bound the disc range when an `else:` arm is
        ## present (the non-else arms' equalities don't cover the
        ## full legal enum range). The witness emitter uses the
        ## names to render `of <tagName>:` branches for else-covered
        ## ordinals — variant construction needs static enum literals,
        ## which the of-arm tagNames alone don't supply.
      vObjectName*:      string
      vPlainFieldNames*: seq[string]
                                    # Phase 11 post-cycle-12: plain
                                    # (non-recCase) fields shared
                                    # across arms. Excluded from
                                    # arm.fieldNames so they're
                                    # allocated once and survive
                                    # discriminator reassignment.
      vPlainFieldTypes*: seq[IRType]
    of itUninterp:
      uninterpName*: string   ## Phase 15 Z3b: Z3 uninterpreted-sort name.
    of itFloat32, itFloat64:
      # Phase 15 F1: sort fully determined by the kind; no payload fields.
      discard
    of itDistinct:
      distinctName*: string   ## Phase 15 G4: the Nim distinct type name; the
                              ## Z3 uninterpreted-sort name (e.g. "Meters").
      distinctBase*: IRType   ## the base type (`float64` for `distinct float64`;
                              ## may itself be `itDistinct` for nested chains).
    of itRef:
      refPointeeTy*: IRType   ## Phase 15 R1a (ADR-0010): the `ref T` pointee
                              ## type `T`. Drives the per-type `Ref_T` sort and
                              ## the `Z3Array[Ref_T, T]` heap in R1+.
    of itPtr:
      ptrPointeeTy*: IRType   ## Phase 15 R1a (ADR-0010): the `ptr T` pointee
                              ## type. Same heap model as `itRef`.
    of itMultiVariant:
      mvObjectName*:      string
      mvPlainFieldNames*: seq[string]
        ## Same role as `vPlainFieldNames` in `itVariant`: plain
        ## (non-recCase) prefix fields shared across all axes.
      mvPlainFieldTypes*: seq[IRType]
      mvAxes*:            seq[VariantAxis]
        ## One entry per `nnkRecCase` block. Invariant: `mvAxes.len
        ## >= 2`; enforced by `mkMultiVariant`. The parser emits
        ## `itVariant` (not `itMultiVariant`) for single-recCase
        ## objects.

  ## IRExprKind prefix convention (M2):
  ##   iek* — value-producing expressions (may appear in rvalue position)
  ##   is*  — statements (sequenced; may not produce a value), see IRStmtKind
  ##   it*  — type-level IR nodes, see IRTypeKind
  IRExprKind* = enum
    iekIntLit, iekBoolLit, iekVar, iekBinop, iekUnop
    iekField     ## Phase 4: positional field access into a tuple/object.
    iekIndex     ## Phase 4: array index access; `arr[idx]`.
    iekArrayLit  ## Phase 4: static array literal `[a, b, c]`.
    iekTupleLit  ## RFC-chapulin-hardening P1 (walker v51->52): a general
                 ## N-ary tuple constructor `(a, b, c)` / named `(x: a, y: b)`
                 ## used as an EXPRESSION (e.g. `let t = (a, b)`, `return (a,
                 ## b, c)`). Builds an `itTuple`/`svTuple` SymVal from the
                 ## element expressions — the same witness machinery already
                 ## used for variant/object values, just reached from a new
                 ## construction site. Distinct from the narrow `yield
                 ## (e1,e2)` A3-S2a special-case (`parseIterBodyStmt`), which
                 ## destructures a tuple constructor directly into per-var
                 ## `let`s without ever building a tuple SymVal.
    iekVariantLit ## Round-6 A1 (ADR-0029): literal-discriminant variant
                 ## object construction `T(kind: tagLit, f1: e1, ...)` used
                 ## as an EXPRESSION. Mirrors `iekTupleLit`'s payload shape —
                 ## a pure per-env value production, no path forking (a
                 ## SYMBOLIC discriminant is NOT this kind; it is A3's
                 ## `isVariantConstructSym` STATEMENT, which needs
                 ## `paths`/`WalkCtx` to fork one path per feasible tag).
                 ## Builds an `itVariant`/`svVariant` SymVal whose
                 ## discriminator is PINNED to the literal tag (a Z3 CONST)
                 ## and whose active arm's fields come from the parsed
                 ## constructor exprs; every OTHER arm allocates
                 ## FRESH-UNCONSTRAINED fields (never zero — reading one is a
                 ## `FieldDefect` FINDING via the existing `isVariantField`
                 ## fork, not a modeling gap).
    iekSeqLen    ## Phase 5: `s.len` on a `seq[T]`. Returns Z3Int.
    iekStrLit    ## Phase 5: string literal (Z3String constant).
    iekFloatLit  ## Phase 15 F2: float32/float64 literal (incl. Inf/NaN/-0.0).
    iekConvIntToFloat  ## Phase 15 F5: `float(intExpr)` (rmRNE).
    iekConvFloatToInt  ## Phase 15 F5: `int(floatExpr)` (rmRTZ, truncation).
    iekConvIntWidth    ## Round-6 B2 (RFC-chapulin-hardening, ADR-0028 Leg 2):
                       ## int-family WIDTH-CONVERSION, WIDENING ONLY
                       ## (`uint16(b)` call syntax / `b.uint16` method syntax —
                       ## both desugar to the identical nnkConv shape). Zero-
                       ## vs sign-extend is keyed on the SOURCE value's OWN
                       ## signedness (`ciwSrcSigned`); the resulting SymVal's
                       ## `signed` flag takes the TARGET type's signedness
                       ## (`ciwTgtSigned`), so downstream arithmetic/compares
                       ## on the converted value are correct. Narrowing is OUT
                       ## of scope (recorded decline — no truncate primitive
                       ## is modeled; the pre-B2 identity pass-through was
                       ## silently unsound: it left the value's bit pattern
                       ## un-truncated).
    iekConvIntReinterpret  ## A1 adjudication (walker v116): SAME-WIDTH
                       ## signedness reinterpret (e.g. `uint(x)` from an
                       ## `int`, `uint32(y)` from an `int32`) — B2 originally
                       ## recorded this as a decline ("no reinterpret
                       ## primitive is modeled"), but every fixed-width Nim
                       ## int already allocates as an svBV* whose raw Z3 BV
                       ## bit pattern is signedness-agnostic (only `signed`
                       ## steers which comparison/shift-right variant a
                       ## downstream op picks — arithmetic/bitwise ops don't
                       ## care). A reinterpret is therefore NOT a missing
                       ## primitive; it's a same-width no-op at the Z3 level
                       ## plus a `signed`-tag correction the pre-B2 identity
                       ## pass-through used to skip (that omission, not the
                       ## conversion itself, was B2's actual unsoundness
                       ## finding). `cirOperand`/`cirTgtSigned` below.
    iekMathCall  ## Phase 15 F6: std/math float op or FP predicate
                 ## (`abs`/`sqrt`/`min`/`max`/`floor`/`ceil`/`round`/`trunc`/
                 ## `signbit`/`isNaN`/`isInf`/`isFinite`/`isNormal`), plus the
                 ## deferred ops (`classify`/`copySign`/`nextafter`/...) which
                 ## lower to a classified `feUnsupportedOp` error.
    iekContains  ## Phase 5: `x in s` / `t.contains(k)`. Returns Z3Bool.
    iekSeqAdd    ## #145: `s.add(v)` — returns new svSeq.
    iekSeqDel    ## #145: `s.del(i)` — Nim swap-with-last semantics.
    iekSeqInsert ## #145: `s.insert(v, i)` — shift later elements.
    iekSeqPop    ## #143: `s.pop()` — returns the popped value;
                 ## a separate isAssign updates the seq.
    iekTableSet  ## #145: returns new svTable with `[k]=v`.
    iekTableDel  ## #145: returns new svTable with k absent.
    iekSetIncl   ## #145: returns new svSet with elem included.
    iekSetExcl   ## #145: returns new svSet with elem excluded.
    # ---- Phase 15 Cluster S: full Z3 String op surface (ADR-0006,
    # byte-faithful). S1 adds these as STUBS — each carries its operands in
    # `strArgs` (and `strOp` for the unsupported-op diagnostic). S2–S11 fill in
    # the real lowering one op per cycle. Until then any S* op that reaches the
    # walker lowers to a classified `seUnsupportedStringOp` (sxUnknown), never a
    # crash or silent UNSAT (Invariant 3).
    iekStrLen        ## `s.len`            → Z3 `(str.len s)`            (S3)
    iekStrAt         ## `s[i]` read        → Z3 `(seq.at s i)`          (S3)
    iekStrSubstr     ## `s[a..b]`          → Z3 `(seq.extract …)`       (S3)
    iekStrFind       ## `s.find(sub[,start])` → Z3 `indexOf[, start]`, −1 absent
                     ## strArgs = [recv,sub] or [recv,sub,start] (S4; RFC Q1 ADR-0025)
    iekStrRfind      ## `s.rfind(sub)`     → Z3 `lastIndexOf`, −1 absent (RFC M3)
    iekStrContains   ## `sub in s`         → Z3 `(seq.contains s sub)`  (S4)
    iekStrStartsWith ## `s.startsWith(p)`  → Z3 `(seq.prefixof p s)`    (S4)
    iekStrEndsWith   ## `s.endsWith(q)`    → Z3 `(seq.suffixof q s)`    (S4)
    iekStrReplace    ## `s.replace(o,n)`   → Z3 `replace` first-occ     (S5)
    iekStrReplaceAll ## `s.replace(o,n)` all-occ (z3WithSeqReplaceAll)  (S5)
    iekStrSplit      ## `s.split(sep)`     → bounded split             (S5)
    iekStrJoin       ## `xs.join(sep)`     → bounded concat            (S5)
    iekStrMatch      ## `s.match(re"…")`   → Z3 `(seq.in.re s r)`      (S6b)
                     ## byte-faithful regex membership. The raw `re"…"` pattern
                     ## string rides in `strOp` (parsed at walk time by S6a's
                     ## `parseNimRegexToZ3Regex`); `strArgs == [recv]`.
    iekStrFindRe     ## `s.find(re"…")`    → DEFERRED (no Z3 indexOf/regex) (S6b)
                     ## pattern in `strOp`; classified `seUnsupportedRegex`.
    iekStrReplaceRe  ## `s.replace(re"…",x)` → Z3 `(seq.replace_re …)`  (S6b)
                     ## VERSION-GATED `-d:z3WithSeqReplaceRe`; pattern in `strOp`,
                     ## `strArgs == [recv, replacement]`.
    iekStrBytes      ## `bytes(s)[i]`      → identity byte view        (S7a)
    iekStrConcat     ## `a & b`            → Z3 `(seq.++ a b)`          (S3)
    iekIntToStr      ## `$i`               → Z3 `(int.to.str i)`       (S10a)
    iekStrToInt      ## `parseInt(s)`      → Z3 `(str.to.int s)`       (S10a)
    iekRadixFmt      ## Phase 16 A8: `toHex`/`toBin` on a fixed-width BV int.
                     ## `strOp` encodes `"<name>:<base>:<numDigits>"` e.g.
                     ## `"toHex:16:2"` (uint8 full-width hex) or `"toBin:2:8"`.
                     ## `strArgs[0]` is the integer operand (must lower to a BV).
                     ## Result is an svString (ITE-chain digit table, no hang).
    iekStrUnsupported ## genuinely-unsupported string op (immutability /
                      ## missing-Z3-op, e.g. `s[i]=c`, `toLower`) → S1 routing
                      ## target; lowers to a classified `seUnsupportedStringOp`.
    iekStrToLower    ## Phase 16 A9: `toLowerAscii(s)` → seq.map with BV18-ITE
                     ## fold body (ADR-0015). `strArgs[0]` is the string operand.
                     ## Result is svString (seqMapBody, quantifier-free, no hang).
                     ## Non-svString operand degrades to sxUnknown (Invariant 3).
    iekStrToUpper    ## Phase 16 A9: `toUpperAscii(s)` → seq.map with BV18-ITE
                     ## fold body (ADR-0015). `strArgs[0]` is the string operand.
                     ## Same invariants as `iekStrToLower`; ITE range 97..122 → -32.
    iekRuneToStr     ## Phase 16 A7-S2: `$r` where r: Rune → UTF-8 byte string
                     ## via `runeToUtf8Sym` (4-branch ITE, byte-level encoding).
                     ## `strArgs[0]` is the Rune's svInt term (a Z3Int operand).
                     ## Output chars ≤0xFF → byte-faithful svString (ADR-0006).
                     ## ADR-0017 Path B: additive, byte model untouched.
    iekSeqSlice      ## Round-4 (dev item 1, walker v67): `data[a..b]` /
                     ## `data[a ..< b]` slice VALUE over a seq — an
                     ## ARRAY-LAMBDA VIEW: the lowered svSeq has
                     ## `seqLen = hi - lo + 1` and
                     ## `seqData = (lambda (i) (select base (+ i lo)))`
                     ## (`Z3_mk_lambda_const` + raw `Z3_mk_select` —
                     ## element-sort-generic, quantifier-free; Z3
                     ## beta-reduces selects over the lambda natively).
                     ## Copy semantics come free: the lambda captures the
                     ## base's array AST AT SLICE TIME, so later mutation of
                     ## the base (a new store chain) cannot leak in. Bounds
                     ## follow ADR-0027: svInt proto, BV-sorted bound
                     ## declines classified. Fields: `ssBase`/`ssLo`/`ssHi`
                     ## (hi already ..<-adjusted by the parser).
    iekStrStrip      ## Round-4 Slice B (ADR-0026): `strutils.strip(s,
                     ## leading, trailing, chars)` with COMPILE-TIME-literal
                     ## flags and char set → quantifier-free DECOMPOSITION
                     ## constraints (`s = pre ++ core ++ suf`; `pre`/`suf` ∈
                     ## `(union chars)*` via Z3 regex; `core`'s boundary
                     ## chars ∉ chars), asserted through the
                     ## `stripDecompConds` global sink; the expression's
                     ## VALUE is the fresh `core` string. `strArgs[0]` is
                     ## the receiver; `strOp` carries `"<L|T|LT|->:" & chars`
                     ## (the literal stripped-char set; "-" = both flags
                     ## false, identity). Non-literal flags/chars degrade at
                     ## parse time (`iekStrUnsupported`) — this kind is only
                     ## emitted for fully-literal specs.
    iekStrInOptionRegion ## Round-6 B6 (ADR-0028, option-region membership):
                     ## boolean predicate `s[start .. bound-1] ∈
                     ## ((nonzero)* "\0")*` — STAR inner segments (round-2
                     ## depth: empty keys/values and the double-NUL
                     ## terminator are themselves empty segments; `+` would
                     ## reject exactly the well-formed inputs a property
                     ## search generates). `strArgs = [recv, start, bound]`;
                     ## `strOp` unused ("" — no literal spec, unlike
                     ## `iekStrStrip`). The Z3 regex term
                     ## (`range`/`star`/`concat`/`matches`) is built entirely
                     ## at WALK time (`runtime_strings.nim`) from these three
                     ## operands — never from a user-facing pattern string,
                     ## unlike `iekStrMatch`/`iekStrFindRe`. Emitted ONLY by
                     ## `tryRecognizePairLoopIdiom`'s closed-form replacement
                     ## of the `readOptions` pair-loop shape; never reachable
                     ## from ordinary Nim surface syntax.
    iekGetCurrentExn    ## Phase 15 E8: `getCurrentException()`. No-arg magic
                        ## intrinsic; the walker reads `w.frame.inFlightExn` at
                        ## lower time. Returns an opaque `svUninterpRef` keyed by
                        ## the in-flight type, or `eeNotInHandler` out of a handler.
    iekGetCurrentExnMsg ## Phase 15 E8: `getCurrentExceptionMsg()`. No-arg magic
                        ## intrinsic; returns the in-flight exn's message string
                        ## (or "" if none), or `eeNotInHandler` out of a handler.
    iekBorrowOp         ## Phase 15 G5: a `{.borrow.}`-proc operator on a
                        ## `distinct T`. Carries the BASE operator + the two
                        ## (distinct-typed) operands. The runtime ejects both
                        ## operands to their base SymVals, applies the base op,
                        ## and — for arithmetic — RE-BOXES the result as a fresh
                        ## `svDistinct` (same `borrowDistinctName`); for a
                        ## comparison returns the raw bool. This operates on the
                        ## G4 boxed-base value, NOT a Z3 `inject` function
                        ## application (which HANGS — see the G4 finding).
    iekLambda           ## Phase 15 Cluster C (C1, ADR-0009 D1/D8): a
                        ## value-producing lambda expression (`proc(...) = ...`
                        ## in rvalue position) with an explicit free-variable
                        ## capture list. Emitted POST-monomorphization, so
                        ## `lambdaParams`/`lambdaRetTy` carry concrete IRTypes.
                        ## The walker STUBS it (`ceNotImplemented`) in C1;
                        ## C2a builds the `(funcSym, envRecord)` `svClosure`.
    iekClosureCall      ## Phase 15 Cluster C (C1, ADR-0009 D6): a call THROUGH a
                        ## proc-valued variable (`f(args)` where `f` is a
                        ## proc-typed local/param, not a top-level proc def).
                        ## A-normalised like `isCall`. The walker STUBS it
                        ## (`ceNotImplemented`) in C1; C2b descends into the
                        ## lambda body with a GROUND per-call-site axiom.
    iekSeqLit           ## Phase 15 C4: a concrete seq literal `@[a, b, c]`
                        ## (incl. the empty `@[]`). Lowers to a CONCRETE-length
                        ## `svSeq` (seqLen pinned to the literal element count),
                        ## so a downstream HOF can take the bounded inline path.
    iekHofCall          ## Phase 15 C4 (ADR-0009): a std/sequtils higher-order
                        ## call — `filter`/`map` over `seq[T]` with a closure
                        ## argument (the closure is an `iekLambda`). Dispatched
                        ## by the walker to the inline (concrete length ≤
                        ## seqInlineThreshold) or axiom (symbolic length) path,
                        ## NOT the generic isCall descent. `fold` reaches this
                        ## node only via a hypothetical closure-taking fold;
                        ## std/sequtils `foldl`/`foldr` are TEMPLATES that the
                        ## typed macro expands to a loop before the parser runs.
    iekNil              ## Phase 15 R5 (Cluster R): the `nil` ref/ptr literal in a
                        ## comparison (`p == nil` / `nil == p`). Lowers to an
                        ## `svRef`/`svPtr` carrying the per-sort `nilConst`
                        ## (`nil_<typeId>`); `nilPointee` is the pointee type of
                        ## the ref/ptr it is compared against (resolved at parse
                        ## time from the OTHER operand). `refEq` then decides
                        ## `p == nil` as a ground equality on `Ref_T` consts.

  IRExpr* = ref object
    case kind*: IRExprKind
    of iekIntLit:
      ival*: int64
    of iekFloatLit:
      fval*:   float64   ## Phase 15 F2: literal value (narrowed to float32 when fwidth==32)
      fwidth*: int       ## 32 or 64
    of iekConvIntToFloat, iekConvFloatToInt:
      convOperand*: IRExpr   ## Phase 15 F5: the value being converted
      convWidth*:   int      ## target width: 32 or 64
    of iekConvIntWidth:
      ciwOperand*:   IRExpr  ## Round-6 B2: the value being widened
      ciwSrcWidth*:  int     ## source width: 8, 16, or 32
      ciwSrcSigned*: bool    ## source signedness — drives zero-/sign-extend
      ciwTgtWidth*:  int     ## target width: 16, 32, or 64 (> ciwSrcWidth)
      ciwTgtSigned*: bool    ## target signedness — the result SymVal's `signed`
    of iekConvIntReinterpret:
      cirOperand*:   IRExpr  ## A1 adjudication: the value being reinterpreted
      cirWidth*:     int     ## shared src==tgt width: 8, 16, 32, or 64
      cirTgtSigned*: bool    ## target signedness — the result SymVal's `signed`
    of iekMathCall:
      mathOp*:   string        ## Phase 15 F6: the std/math op name (e.g. "sqrt")
      mathArgs*: seq[IRExpr]    ## Phase 15 F6: the call arguments (1 or 2)
    of iekBoolLit:
      bval*: bool
    of iekVar:
      vname*: string
    of iekBinop:
      bop*: IRBinop
      lhs*, rhs*: IRExpr
    of iekUnop:
      uop*: IRUnop
      operand*: IRExpr
    of iekField:
      obj*:        IRExpr
      fieldIx*:    int
      fieldName*:  string   ## for diagnostics; runtime dispatches by index
    of iekIndex:
      arr*:  IRExpr
      idx*:  IRExpr
    of iekArrayLit:
      lelems*: seq[IRExpr]
      lelemTy*: IRType
    of iekTupleLit:
      telems*:   seq[IRExpr]  ## the element expressions, in field order
      ttupleTy*: IRType       ## the full itTuple IRType (fields+fieldNames);
                               ## carried whole (not just one elemTy, unlike
                               ## iekArrayLit) because tuple fields may be
                               ## heterogeneous.
    of iekVariantLit:
      vlVariantTy*:   IRType      ## the full itVariant IRType (vArms,
                                   ## vDiscName, vPlainFieldNames, ...) — as
                                   ## returned by `classifyType` on the
                                   ## object-constructor node.
      vlTagOrd*:      int         ## the literal discriminant's ordinal
      vlTagName*:     string      ## diagnostic arm/tag name
      vlArmFields*:   seq[IRExpr] ## the ACTIVE arm's field exprs, in that
                                   ## arm's `VariantArm.fieldNames` order
      vlPlainFields*: seq[IRExpr] ## the shared (always-present) plain-field
                                   ## exprs, in `vlVariantTy.vPlainFieldNames`
                                   ## order
    of iekSeqLen:
      lenObj*: IRExpr
      lenLoc*: string            ## Round-6 B1 (siteLoc precedent, A3):
                                   ## parse-time file:line:col + `n.repr`
                                   ## for the walk-time classified-decline
                                   ## fallback arm (a receiver kind the
                                   ## svString/container backstop doesn't
                                   ## cover); "" when not populated by a
                                   ## B1-aware call site.
    of iekSeqSlice:
      ssBase*: IRExpr
      ssLo*:   IRExpr
      ssHi*:   IRExpr
    of iekStrLit:
      sval*: string
    of iekContains:
      container*: IRExpr
      key*: IRExpr
    of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
      mutRecv*: IRExpr
      mutArg*:  IRExpr
    of iekSeqDel:
      delSeq*: IRExpr
      delIdx*: IRExpr
    of iekSeqInsert:
      insSeq*: IRExpr
      insVal*: IRExpr
      insIdx*: IRExpr
    of iekSeqPop:
      popSeq*: IRExpr
    of iekTableSet:
      tabRecv*: IRExpr
      tabKey*:  IRExpr
      tabVal*:  IRExpr
    of iekStrLen, iekStrAt, iekStrSubstr, iekStrFind, iekStrRfind, iekStrContains,
       iekStrStartsWith, iekStrEndsWith, iekStrReplace, iekStrReplaceAll,
       iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe, iekStrReplaceRe,
       iekStrBytes, iekStrConcat,
       iekIntToStr, iekStrToInt, iekRadixFmt, iekStrUnsupported,
       iekStrToLower, iekStrToUpper, iekRuneToStr, iekStrStrip,
       iekStrInOptionRegion:
      ## Phase 15 Cluster S (S1 scaffolding). Uniform payload: operands in
      ## `strArgs`; `strOp` names the surface op (for the unsupported
      ## diagnostic). S2–S11 read these; they are otherwise inert in S1.
      ## S6b reuses `strOp` to carry the raw `re"…"` PATTERN string for
      ## `iekStrMatch`/`iekStrFindRe`/`iekStrReplaceRe` (no recursive IRRegex
      ## type, no new field): the pattern is parsed at walk time by S6a's
      ## `parseNimRegexToZ3Regex`, and canonicalize already folds `strOp` into
      ## the cache key, so distinct patterns content-address distinctly.
      strArgs*: seq[IRExpr]
      strOp*:   string
      strRetTy*: IRType  ## Fix-slice item 5: the CALL EXPRESSION's static
                          ## Nim return type, threaded from the parser's own
                          ## `classifyType(n)` at construction. Defaults to
                          ## the `itString` sentinel (`mkStrOp`'s own
                          ## default), which is also the CORRECT answer for
                          ## every StrOpKinds member whose result type is
                          ## already implied by its `kind` alone
                          ## (`iekStrLen` -> int, `iekStrContains` -> bool,
                          ## …) — those call sites never override it. Only
                          ## `iekStrUnsupported`'s NAME-KEYED fallback arm
                          ## (an unrecognized stdlib string-method call,
                          ## `getStdlibModelFor` returns `smkUnregistered`)
                          ## is genuinely ambiguous — its real return type
                          ## could be int/bool/seq/anything — so that ONE
                          ## site passes the classified type explicitly.
                          ## `degradeStrArm` (runtime.nim) reads this to
                          ## manufacture a type-correct placeholder instead
                          ## of assuming string.
    of iekGetCurrentExn, iekGetCurrentExnMsg:
      ## Phase 15 E8: no-arg magic intrinsics; no payload. Resolved at lower
      ## time against `w.frame.inFlightExn`.
      discard
    of iekBorrowOp:
      ## Phase 15 G5: `{.borrow.}` operator on a `distinct T`.
      borrowOp*:           IRBinop   ## the BASE operator (e.g. bAdd / bLt)
      borrowLhs*:          IRExpr
      borrowRhs*:          IRExpr
      borrowReturnsDistinct*: bool   ## true → re-box the base result as a fresh
                                     ## `svDistinct` (arithmetic); false →
                                     ## comparison, return the raw bool.
      borrowDistinctName*: string    ## the distinct type to re-box into
                                     ## (only meaningful when returnsDistinct).
    of iekLambda:
      ## Phase 15 Cluster C (C1, ADR-0009). A lambda expression.
      lambdaSite*:     tuple[siteHash: int64, declOrder: int]
                                     ## body-hash + intra-scope order index (D3)
      lambdaParams*:   seq[IRParam]  ## concrete types post-monomorphization (D8)
      lambdaBody*:     IRStmt        ## the lambda's body (descended at C2b apply)
      lambdaCaptures*: seq[string]   ## names of captured locals (free vars, D2)
      lambdaRetTy*:    IRType        ## concrete return type
    of iekClosureCall:               ## A-normalised like isCall (D6)
      ccCallee*:  string             ## name of the proc-valued variable
      ccArgs*:    seq[IRExpr]
    of iekSeqLit:                    ## Phase 15 C4: `@[a, b, c]`
      seqLitElems*:  seq[IRExpr]     ## the literal elements (concrete length)
      seqLitElemTy*: IRType          ## the element IRType
      seqLitDeclinedPlaceholder*: bool ## Round-6 N15: parse-time twin of
        ## `SymVal.isUnsupportedFieldPlaceholder` (runtime.nim). Set ONLY by
        ## `declineUnsupportedFieldRead`'s fake empty-seq stand-in, so a
        ## caller that just parsed a receiver expression can tell it declined
        ## by inspecting what `parseExpr` RETURNED — no side-channel
        ## `ctx.parseErrors.len` diff-and-inspect required. False for every
        ## ordinary seq literal (`@[..]`) and every other `zeroValueForType`
        ## stand-in.
    of iekHofCall:                   ## Phase 15 C4: filter/map/fold HOF
      hofOp*:      string            ## "filter" | "map" | "fold"
      hofSeq*:     IRExpr            ## the receiver seq expression
      hofClosure*: IRExpr            ## the closure arg (an iekLambda)
      hofInit*:    IRExpr            ## fold initial accumulator (nil otherwise)
      hofRetElemTy*: IRType          ## element type of the result seq
                                     ## (map: mapper return; filter: input elem)
    of iekNil:                       ## Phase 15 R5: the `nil` ref/ptr literal
      nilPointee*: IRType            ## the pointee type of the ref/ptr it is
                                     ## compared against (an `itRef`/`itPtr` full
                                     ## type when the other operand is `ptr T`)

  IRStmtKind* = enum
    isBlock
    isIf
    isLet
    isAssign          ## #145: env reassignment for mutations
                      ## (s = newSeq, t = newTable, etc.)
    isWhile           ## Phase 6: bounded loop k-unrolled per
                      ## `SymexSettings.maxLoopUnwind`.
    isBreak           ## Phase 6: terminate enclosing loop body.
    isContinue        ## Phase 6: skip to next iteration's guard.
    isReturn          ## `return [expr]` — terminate this path; in callees
                      ## the optional value binds the call's return symbol
    isAssert          ## `symexAssert(cond)` — under a label target,
                      ## tighten path condition with cond; under
                      ## `tAssertionViolation`, fork to search for
                      ## `not cond` reachability
    isAssume          ## Phase 16 SND-2 (ADR-0019): `symexAssume(cond)` —
                      ## FILTER/PRUNE semantics, distinct from `isAssert`.
                      ## Conjoins `cond` into the path condition like
                      ## `isAssert`, but NEVER forks an `AssertionDefect` —
                      ## `symexAssume` cannot itself be "violated" in the
                      ## sense that opens a defect-search fork. Raises
                      ## arising from EVALUATING `cond` (e.g. a div-by-zero
                      ## inside the assumed expression) still surface — only
                      ## the assert-specific defect fork is omitted. A
                      ## distinct IR kind (not a bool flag on isAssert) so
                      ## Nim's `case`-exhaustiveness compiler-forces every
                      ## switch site to decide how isAssume behaves.
    isCall            ## A-normalised call to a user-defined proc; lookup
                      ## via `SymexProgram.procs[callee]`, walk the body
                      ## under arg bindings, bind retval to the named
                      ## fresh symbol if non-void
    isVariantField    ## Phase 11 cycle 5: A-normalised variant
                      ## arm-field access `let r = obj.field`. The
                      ## walker forks: in-arm path adds `disc IN
                      ## matchingTags` to pc and binds `r`; out-of-
                      ## arm path adds the negation and (under
                      ## stkFieldDefect target) is solved for a
                      ## witness.
    isVariantReassign ## Phase 11 cycle 6: `obj.kind = tagLiteral` —
                      ## reassigns the discriminator of a variant
                      ## variable in env. The walker updates vDisc
                      ## to the literal tag's BV constant and zero-
                      ## initialises the new arm's primitive fields
                      ## (Nim's runtime semantics).
    isVariantReassignSymbolic ## Phase 14 cycle A4 (ADR-0003 D4).
                      ## `obj.kind = symbolicRhs` — walker forks one
                      ## path per arm-ordinal of the discriminator's
                      ## enum domain; each path is constrained
                      ## `rhsExpr == k_ord`. Existing arm-field
                      ## SymVals are PRESERVED across the fork
                      ## (no zero-init — that's the static-tag
                      ## path's job per ADR-0003 D4).
    isVariantConstructSym ## Round-6 A3 (ADR-0029). `T(disc: symbolicExpr,
                      ## plainField: e, ...)` — a SYMBOLIC-discriminant
                      ## variant object CONSTRUCTOR, A-normalised (M5 idiom):
                      ## the parser hoists a fresh result temp and emits this
                      ## STATEMENT into the preamble rather than lowering the
                      ## constructor as an `iek*` expression (fork-per-tag
                      ## needs `paths`/`WalkCtx`, unavailable inside `lower()`
                      ## — see `iekVariantLit`'s doc comment). Clones
                      ## `isVariantReassignSymbolic`'s fork-per-tag shape
                      ## (one path per feasible tag, each constrained
                      ## `discExpr == tag_ord`) with the deliberate
                      ## divergence the ADR calls out: reassignment PRESERVES
                      ## arm fields; construction has no "active arm" data to
                      ## carry (Nim itself accepts a non-constant discriminant
                      ## in constructor syntax only when NO arm-specific field
                      ## is set — only `vcsPlainFields` ever carries parsed
                      ## constructor exprs), so EVERY declared arm's fields
                      ## allocate FRESH-UNCONSTRAINED, independently, in EACH
                      ## fork. `vcsTagSet` is the parse-time (possibly
                      ## `case`-branch-NARROWED, lexical/per-proc-body only —
                      ## never crossing a proc boundary) feasible-tag set;
                      ## the walker's own `maxVariantConstructorForks`
                      ## STRUCTURAL budget check (against `vcsTagSet.len`,
                      ## before any solver work) classifies a decline
                      ## (`beBudgetExhaustedUnmodelled`, RFC-0005 S6a) when
                      ## exceeded — a WALK-TIME
                      ## site with no `NimNode` to build a `siteMsg` from, so
                      ## `vcsLoc` carries the file:line:col + `n.repr`
                      ## components captured at PARSE time and rendered
                      ## VERBATIM into that decline's message.
    isIndex           ## A-normalised array index `let r = arr[idx]`.
                      ## Symbolic indexes fork the path: in-bounds path
                      ## adds `0 <= idx < N` to pc and binds r to the
                      ## ite-chain over elements; OOB path adds the
                      ## negation and (if target = stkIndexError) records
                      ## a witness.
    isIndexAssign     ## N14 (RFC-chapulin-hardening bucket-2): A-normalised
                      ## seq element ASSIGNMENT `xs[idx] = v`. Mirrors `isIndex`'s
                      ## own OOB fork (same `0 <= idx < len` predicate, same
                      ## `IndexDefect` target) but rebinds `iaRecvName` in the
                      ## surviving env to a NEW `svSeq` whose backing array is
                      ## `store(old.data, idx, v)` (`storeSeqElem`, the same
                      ## helper `lowerSeqLit`/HOF map already use for
                      ## construction) instead of binding a fresh read result.
    isSeqPop          ## N14 (RFC-chapulin-hardening bucket-2): A-normalised
                      ## `let r = mySeq.pop()`. Unlike `isIndexAssign` (single
                      ## env rebind) or `del`'s `isAssign`+`iekSeqDel` route
                      ## (single rebind, no return value), `.pop()` needs BOTH
                      ## a fresh return-value bind (`spRetName` = the popped
                      ## element, matching real Nim semantics) AND a receiver
                      ## rebind (`spRecvName`, length-1) in the SAME statement
                      ## — the shape no existing statement/expression kind
                      ## carries, hence its own kind rather than reuse. Forks
                      ## `IndexDefect` on an empty seq (Nim's own `pop()`
                      ## semantics), mirroring `isIndex`'s unconditional
                      ## Phase 16 D1a fork.
    isTargetLabel     ## `symexTarget("name")`
    isRaise           ## Phase 15 E1: `raise newException(T, msg)` or bare
                      ## `raise` (re-raise). Structural in E1 — the walker
                      ## stubs a classified `eeRaiseUnimplemented` error;
                      ## real raise-flow semantics land E2b+.
    isTry             ## Phase 15 E1: `try: … except T: … finally: …`.
                      ## Structural in E1 — walker stubs
                      ## `eeTryUnimplemented`; handler dispatch lands E3+.
    isDeref           ## Phase 15 R1a (ADR-0010): A-normalised `p[]` read,
                      ## binding a fresh let-name to the dereferenced value.
                      ## Structural in R1a — the walker STUBS it with a
                      ## classified `heUnresolvedRef`; the real `select` on
                      ## `path.heaps[T]` lands R3. `dPtrFamily` distinguishes a
                      ## `ptr T` deref (R8) from a `ref T` deref.
    isNew             ## Phase 15 R1a (ADR-0010): `new(T)` allocation, binding a
                      ## fresh ref let-name. Structural in R1a — the walker STUBS
                      ## it with `heUnresolvedRef`; the freshness counter
                      ## (`path.allocCounters`) lands R2.
    isDerefWrite      ## Phase 15 R3 (ADR-0010): `p[] = v` — a heap WRITE through
                      ## a ref/ptr deref. STRUCTURAL at R3: the walker STUBS it
                      ## with a no-op (`discard`) so a write-then-read SUT type-
                      ## checks and the read resolves through the FREE heap array.
                      ## The real `store(path.heaps[T], p, v)` semantics (and the
                      ## read-after-write / per-path isolation it enables) land R4.
    isUnsupported     ## any AST kind the Phase-1 parser doesn't model
    isUnsafeCast      ## Phase 15 R11 (ADR-0010, RFC §R11): an unsafe POINTER
                      ## MATERIALISATION (`cast[ptr T](...)`, `addr x`,
                      ## `unsafeAddr x`) whose raw machine address is unmodelable
                      ## in the logical-heap model. The walker HALTS the path
                      ## with a classified `heUnsafeCast` (sevError) → sxUnknown
                      ## (Invariant 3 — no silent fallback). `ucReason` records
                      ## which pattern was routed (`"cast[ptr T]"`/`"addr"`).

  IRBranch* = object
    cond*: IRExpr     ## guard for this arm (already negation-folded for elif)
    body*: IRStmt

  ExceptHandler* = object
    ## Phase 15 E1. One `except [T, …]: body` (or bare `except: body`) arm
    ## of an `isTry`. `typeIds` empty ⇒ bare catch-all `except:`.
    typeIds*: seq[string]  ## qualified Nim exception type names
    body*:    IRStmt

  IRStmt* = ref object
    case kind*: IRStmtKind
    of isBlock:
      stmts*: seq[IRStmt]
    of isIf:
      branches*: seq[IRBranch]
      elseBody*: IRStmt          ## nil if no `else:` clause
    of isLet:
      lname*: string
      lty*: IRType
      lvalue*: IRExpr
      lIsIntOffsetLocal*: bool
        ## RFC-chapulin-hardening B7r2 (walker v88). Parse-time-captured
        ## companion to `IRParam.isIntOffset`, for the case that flag
        ## cannot cover: a scan/pair-loop counter seeded directly from an
        ## INT LITERAL (`var pos = 2`), not a formal param or a bare-
        ## symbol rebind of one — `collectIntOffsetParams`'s own
        ## `findRootParam` correctly declines to trace THROUGH a literal
        ## (there is no param to promote), leaving the local BV-allocated
        ## by the type-driven `intLitProto` default, which fails
        ## `iekStrSubstr`/`iekStrInOptionRegion`'s CR-17 Int-sortedness
        ## check. Set by `collectIntOffsetLiteralLocals` (`dsl_parser.nim`)
        ## via `ctx.intOffsetLiteralLocals`; consumed by the `isLet`
        ## walker arm (`runtime.nim`) to select an `svInt` proto instead
        ## of `intLitProto(lty)`'s BV default — sound unconditionally (a
        ## literal's value is already known at parse time; no def-use
        ## tracing risk, unlike a param whose caller-supplied value is
        ## only symbolically known). A no-op for a non-literal `lvalue`
        ## (the proto is ignored by `lower`'s `iekVar` arm either way).
    of isAssign:
      aname*: string
      avalue*: IRExpr
      aty*: IRType
        ## #163 review R27 (fixes R22's own regression). `isAssign` used to
        ## carry no declared type for its target at all -- R22 patched
        ## around that with a WalkCtx-wide `Table[string, IRType]` keyed by
        ## the BARE printed name, populated/cleared by `isLet` with no
        ## scope check. That table collided both ways a shadowed/inlined
        ## name can collide (see dsl_parser.nim's N28 fix for the identical
        ## class of bug in a different collector): a sibling branch's
        ## same-named local silently deleted a live entry, and an inlined
        ## callee's local left a stale entry for the caller's own unrelated
        ## variable to inherit after `popFrame` (which restores only
        ## `w.frame`).
        ##
        ## The real fix: `isAssign`'s target identity IS a Nim symbol at
        ## PARSE TIME (the LHS of `n[0] = n[1]` is an `nnkSym`, not a bare
        ## name) -- so ask the compiler what THAT symbol's declared type is
        ## (`classifyType`, which resolves via `getTypeInst` against true
        ## symbol identity, never a name table) and attach it directly to
        ## this statement. No table, no scope-tracking, no collision
        ## surface: nil when the target has no declared range (the common
        ## case, or a non-`itInt` receiver), else the `itInt` type with its
        ## `hasRange`/`rangeLo`/`rangeHi` populated. Set at every call site
        ## that constructs a scalar-target `isAssign` from a real `nnkSym`
        ## LHS (plain assignment, `inc`/`dec`, and `+=`/`-=`/`*=`); every
        ## other `mkAssign` call site (seq/table/string receiver rebinds,
        ## synthesized loop counters, ...) passes the default `nil`, which
        ## is exactly the "no range check" behavior those sites always had.
    of isWhile:
      wcond*: IRExpr
      wbody*: IRStmt
      wHasAssumedBound*: bool  ## N20 (RFC-chapulin-hardening bucket-2):
                         ## parse-time signal (`collectAssumedLoopBound`,
                         ## dsl_parser.nim) — the guard references a variable
                         ## ALSO constrained by a preceding `symexAssume` in
                         ## the same proc body. Lets the k-unroll-exhaustion
                         ## classification (`beBudgetExhaustedAssumedBound`
                         ## vs. `beBudgetExhausted`) distinguish "an assumed
                         ## bound exists but the structural k-unroll can't use
                         ## it" from "genuinely unbounded" — see that error
                         ## kind's own doc comment for the full mechanism.
                         ## Default `false` for every non-generic-while
                         ## construction site (the closed-form scan
                         ## recognizers never build a plain `isWhile`).
    of isBreak, isContinue:
      discard
    of isReturn:
      retExpr*: IRExpr   ## nil for void returns; callees use this to
                         ## carry the value back to the caller
    of isCall:
      callee*: string
      cargs*: seq[IRExpr]
      retName*: string   ## "" for void; else the fresh let-name the
                         ## return value binds to
      retTy*: IRType     ## return type; tBool() sentinel when void
      opaque*: bool      ## #137: when true, the walker doesn't
                         ## resolve the body — fresh retSym + path
                         ## uncertainty. Used for IO / effectful
                         ## stdlib procs.
      opaqueInert*: bool ## #163 slice 4: parse-time proof that this
                         ## opaque call cannot affect the SUT's symbolic
                         ## state — statement position (no bound result)
                         ## AND every actual argument is plainly
                         ## value-typed (`isInertOpaqueCall`,
                         ## dsl_parser.nim). Meaningless unless `opaque`
                         ## is also true. When set, the walker's
                         ## `#137` arm (runtime.nim) is a no-op: no
                         ## taint, no `w.sawUnknown`. Default `false`
                         ## for every non-opaque call and for any opaque
                         ## call the predicate did not clear.
      retIntOffsetPositions*: seq[int]  ## Round-6 B5 (ADR-0028 Leg 1,
                         ## chained composition): 0-based `retTy` tuple
                         ## positions (or `@[0]` for a bare, non-tuple
                         ## `itInt` return) that `calleeIntOffsetReturnPositions`
                         ## (dsl_parser.nim) proved are the CALLEE's own
                         ## recognized scan closed form's index symbol —
                         ## i.e. a genuine Sequence-theory Int (`iekStrFind`'s
                         ## own result), not a BV. The call's fresh retSym
                         ## placeholder (`freshRetSym`, runtime.nim) allocates
                         ## those positions as `svInt` directly instead of the
                         ## type-driven BV default, so a caller that
                         ## destructures the position into a local and passes
                         ## it on as ANOTHER scan's offset satisfies
                         ## `iekStrSubstr`/`iekStrFind`'s CR-17 Int-sortedness
                         ## requirement without a bv2int bridge. Empty ("no
                         ## positions traced") for every ordinary call —
                         ## purely an ADDITIVE precision gain, never a
                         ## soundness lever (an untraced position just keeps
                         ## the pre-existing BV default).
    of isIndex:
      ixRetName*: string
      ixArr*:     IRExpr
      ixIdx*:     IRExpr
      ixElemTy*:  IRType
      ixLoc*:     string   ## Round-6 B1 (siteLoc precedent, A3): parse-time
                            ## file:line:col + `n.repr` for the walk-time
                            ## classified-decline fallback arm; "" when not
                            ## populated by a B1-aware call site.
    of isIndexAssign:
      iaRecvName*: string  ## the seq-typed local/param NAME being rebound —
                            ## the parse site (dsl_parser.nim's `nnkAsgn` arm)
                            ## only ever recognizes a bare `nnkSym` receiver
                            ## (matching the pre-existing `itTable`/`itString`
                            ## sibling arms one case up), so there is no
                            ## general receiver-expr to carry, unlike `isIndex`'s
                            ## `ixArr` (which also handles the `bytes(lit)[i]`
                            ## CR-20 exception — assignment has no literal-base
                            ## analogue).
      iaIdx*:      IRExpr
      iaVal*:      IRExpr
      iaLoc*:      string  ## siteLoc-captured `file:line:col: <repr>`, same
                            ## idiom as `ixLoc`, for the walk-time decline
                            ## fallback (non-svSeq receiver / placeholder).
    of isSeqPop:
      spRecvName*: string  ## the seq-typed local/param NAME being shrunk —
                            ## same bare-`nnkSym`-only scope as `iaRecvName`.
      spRetName*:  string  ## fresh let-name bound to the popped element.
      spLoc*:      string  ## siteLoc idiom, same purpose as `iaLoc`.
    of isVariantField:
      vfRetName*:       string
      vfRecv*:          IRExpr
      vfFieldName*:     string
      vfFieldTy*:       IRType
      vfMatchingTags*:  seq[int]  ## tag ordinals of arms containing
                                  ## `vfFieldName`
    of isVariantReassign:
      vrObjName*:       string    ## the variant variable in env
      vrNewTag*:        int       ## the new tag ordinal
      vrTagName*:       string    ## diagnostic, e.g. "skSquare"
    of isVariantReassignSymbolic:
      vrsObjName*:      string    ## the variant variable in env
      vrsDiscName*:     string    ## which axis (itMultiVariant); ""
                                    ## for single-axis itVariant
      vrsRhs*:          IRExpr    ## the symbolic RHS expression
    of isVariantConstructSym:
      vcsResultVar*:    string    ## fresh temp the constructed value binds to
      vcsVariantTy*:    IRType    ## the full itVariant IRType (vArms,
                                    ## vDiscName, vPlainFieldNames, ...)
      vcsDiscExpr*:     IRExpr    ## the symbolic discriminant expression
      vcsTagSet*:       seq[int]  ## feasible tag ordinals to fork over —
                                    ## parse-time `case`-branch-narrowed, or
                                    ## every declared (non-else) arm's ordinal
                                    ## when no narrowing applied
      vcsPlainFields*:  seq[IRExpr] ## shared plain-field constructor exprs,
                                    ## in `vcsVariantTy.vPlainFieldNames` order
                                    ## (Nim itself accepts a symbolic-disc
                                    ## constructor only when no arm-specific
                                    ## field is set — see the parser's `of
                                    ## itVariant:` arm)
      vcsLoc*:          string    ## PARSE-TIME `siteMsg`-style components
                                    ## (file:line:col + `n.repr`), rendered
                                    ## VERBATIM (never reformatted) into the
                                    ## WALK-TIME budget-exceeded decline
    of isAssert, isAssume:
      acond*: IRExpr
    of isTargetLabel:
      tname*: string
    of isRaise:
      raiseTypeId*: string   ## qualified Nim type name, e.g. "ValueError"
      raiseMsg*:    IRExpr    ## nil for bare `raise` (re-raise)
      raiseIsReraise*: bool   ## true for no-argument `raise`
    of isTry:
      tryBody*:     IRStmt
      tryHandlers*: seq[ExceptHandler]
      tryFinally*:  IRStmt   ## nil if no `finally`
    of isDeref:
      dRetName*:   string    ## Phase 15 R1a: fresh let-name the deref binds.
      dPtr*:       IRExpr    ## the ref/ptr expression being dereferenced.
      dElemTy*:    IRType    ## the pointee type (the deref result type). For a
                             ## FIELD deref (`dField != ""`) this is the FIELD's
                             ## type (the heap-array value sort); for a bare `p[]`
                             ## it is the whole pointee.
      dPtrFamily*: bool      ## true ⇒ a `ptr T` deref (R8); false ⇒ `ref T`.
      dField*:     string    ## Phase 15 R6: when non-empty, `p.field` field
                             ## deref — the per-(type,field) heap array is keyed
                             ## by `refPointeeTypeId(dObjTy) & "__" & dField`.
      dObjTy*:     IRType    ## Phase 15 R6: the OBJECT pointee type (the `Ref_T`
                             ## sort keys on this; nil for a bare `p[]`).
    of isNew:
      nRetName*:   string    ## Phase 15 R1a: fresh ref let-name the alloc binds.
      nRefTy*:     IRType    ## the allocated `itRef`/`itPtr` type.
    of isDerefWrite:
      dwPtr*:      IRExpr    ## Phase 15 R3: the ref/ptr expr being written through.
      dwValue*:    IRExpr    ## the RHS value stored into `dwPtr[]`.
      dwElemTy*:   IRType    ## the pointee type (the stored value's type). For a
                             ## FIELD write (`dwField != ""`) this is the FIELD's
                             ## type (the heap-array value sort).
      dwPtrFamily*: bool     ## true ⇒ a `ptr T` write (R8); false ⇒ `ref T`.
      dwField*:    string    ## Phase 15 R6: when non-empty, `p.field = v` field
                             ## write — stores into the per-(type,field) heap
                             ## array `refPointeeTypeId(dwObjTy) & "__" & dwField`.
      dwObjTy*:    IRType    ## Phase 15 R6: the OBJECT pointee type (`Ref_T` sort).
    of isUnsupported:
      unKind*: SymexErrorKind    ## RFC-0005 S1b: the classified kind the
                                 ## walker's `isUnsupported` arm records via
                                 ## `degrade()` when a path reaches this node
                                 ## (§2.2: the node used to carry free text
                                 ## only, so the arm tainted with no error).
                                 ## A Class-A site passes the SAME kind as its
                                 ## parse-time error; a Class-B site passes
                                 ## `feUnsupportedStmtKind`.
      reason*: string            ## human-readable diagnostic
      unMarker*: int             ## RFC-0005 S8 (§2.5 point 1): the site's
                                 ## marker id, minted by the parser
                                 ## (`ParseCtx.nextMarker`, from 1) in the
                                 ## SAME act that records a Class-A site's
                                 ## `dskSiteAnchored(unMarker)` parse error.
                                 ## The walker's arm records its reach under
                                 ## the same anchor. Identity only: excluded
                                 ## from `canonicalize` (like a local's name).
    of isUnsafeCast:
      ucReason*: string          ## Phase 15 R11: which unsafe pointer-materialisation
                                 ## pattern was routed (`"cast[ptr T]"`, `"addr"`).
      ucMarker*: int             ## RFC-0005 S8: as `unMarker` -- the anchor of
                                 ## the paired parse-time `heUnsafeCast`.

  IRParam* = object
    name*: string
    ty*: IRType
    rangeLo*: int64
    rangeHi*: int64
    hasRange*: bool
    isVar*: bool       ## #140: var T param — callee mutations propagate
                       ## back to the caller's binding on return.
    isStringBacked*: bool
                       ## Round-6 B1 (ADR-0028 Leg 1). True for a `seq[byte]`
                       ## PARAM whose consuming loop matched the B1a
                       ## scan-shape predicate (`collectStringBackedByteSeq
                       ## Params`, `dsl_parser.nim`) with no mutation site —
                       ## `allocateSym` reads this to allocate the param via
                       ## the itString machinery (ADR-0006 byte-range +
                       ## the [0,1024] length ceiling) instead of the
                       ## ordinary array `itSeq` machinery. The DECLARED
                       ## `IRType` stays `itSeq` unchanged (this is an
                       ## allocation hint sibling to `isVar`, not a type
                       ## change).
    isIntOffset*: bool
                       ## Round-6 B4 (ADR-0028 Leg 1, ADR-0027's recorded
                       ## lift). True for an `int` PARAM whose value flows
                       ## (through at most one direct `var <i> = <param>`
                       ## local rebind) into an accumulating-scan idiom's
                       ## loop index (`collectIntOffsetParams`,
                       ## `dsl_parser.nim`). B4's closed form needs its
                       ## scan's ENTRY OFFSET as an Int-sorted
                       ## `iekStrSubstr` bound — `iekStrAt`/`iekStrFind`
                       ## tolerate a BV-allocated int via a one-way
                       ## `toZ3Int` bridge, but `iekStrSubstr` deliberately
                       ## does not (the CR-17 non-termination finding
                       ## recorded on its own runtime arm), and
                       ## `allocateSym`'s `itInt` arm otherwise always
                       ## chooses a BV representation. `runSymexImpl`'s
                       ## top-level param-allocation loop reads this
                       ## alongside the existing `isLoose`/`isOptimised`
                       ## svInt-promotion machinery to allocate an
                       ## unconstrained `svInt` instead of a BV var — no
                       ## new range constraints (this flag carries no
                       ## proven range, unlike the sound-promotion path).
                       ## The DECLARED `IRType` stays `itInt` unchanged
                       ## (an allocation hint sibling to `isStringBacked`,
                       ## not a type change).

  ProcSig* = object
    name*:    string
    params*:  seq[IRParam]
    body*:    IRStmt
    retTy*:   IRType   ## tBool() sentinel for void; the runtime keys
                       ## off `isVoid` rather than the type itself
    isVoid*:  bool
    conceptConstraints*: seq[string]
                       ## Phase 15 G6. Per-generic-param type-class constraint
                       ## names captured from `nnkGenericParams` (`T: SomeNumber`
                       ## → "SomeNumber"). Metadata only: the parse-time
                       ## conformance check (stdlib concepts) runs in
                       ## `parseCalleeImpl` against the resolved concrete type;
                       ## user-defined concepts are trusted to the semchecker.
                       ## Empty for non-generic / unconstrained procs.

# ---- Public symex-level types -----------------------------------------------
# N47-followup (walker v110): kept in the SAME `type` section as the IR types
# above (no `type` keyword here) -- `IRType`'s new `seqUnsupportedFieldKind`
# field (itSeq case, above) references `SymexErrorKind` (below), and Nim only
# allows forward references among types declared within one shared section.

  SymexTargetKind* = enum
    stkLabel               ## reach a `symexTarget("name")`
    stkAssertionViolation  ## falsify any `symexAssert(cond)` on any path
    stkIndexError          ## find an array OOB index reachable on any
                           ## `arr[i]` access (Phase 4 cycle 8)
    stkFieldDefect         ## Phase 11 cycle 5: find a variant
                           ## arm-field access whose discriminator is
                           ## not in the field's arm set — the SUT
                           ## would raise FieldDefect at runtime.
    stkRaisedExn           ## Phase 15 E2a: find an input on which the SUT
                           ## raises an exception. `typeFilter` (empty = any)
                           ## restricts the search to a specific raised type.
    stkNilAccess           ## Phase 15 R5 (Cluster R): find an input on which the
                           ## SUT dereferences a nil ref/ptr — the `p[]`-of-nil
                           ## NilAccessDefect. The nil-fork's defect path is gated
                           ## on this target; under any other target only the
                           ## non-nil deref continuation surfaces.

  SymexTarget* = object
    case kind*: SymexTargetKind
    of stkLabel:
      label*: string
    of stkAssertionViolation:
      discard
    of stkIndexError:
      discard
    of stkFieldDefect:
      discard
    of stkRaisedExn:
      typeFilter*: string  ## Phase 15 E2a. Empty = any raised exception.
    of stkNilAccess:
      discard              ## Phase 15 R5. No payload — the witness carries `p == nil`.

  SymexStatusKind* = enum
    sxSat       ## witness found
    sxUnsat     ## target proved unreachable / no violation possible
    sxUnknown   ## solver gave up, or every path hit an `isUnsupported` node
    sxRaised    ## Phase 15 E2a. A `raise` is reachable on a feasible path.
                ## STRUCTURAL in E2a (the walker emits this per raise-path with
                ## no handler matching / propagation / witness — those land E2b+).

  Interval* = object
    ## Closed integer interval `[lo, hi]`. Used by the abstraction
    ## layer (ADR-0001) for range tracking and BV-window containment.
    lo*, hi*: int64

  AbstractionEvidence* = enum
    aeTypeRange    ## "from typedesc range[lo..hi] (or Natural/Positive)"
    aeNumericFold  ## "from interval-composing arithmetic"
    aeVariantDisc  ## Phase 14 A6: variant discriminator promoted to
                   ## Z3Int under `isOptimised` (ADR-0003 D6 mandatory).

  AbstractionEntry* = object
    name*:        string
    interval*:    Interval
    evidence*:    AbstractionEvidence
    derivation*:  string

  AbstractionLog* = seq[AbstractionEntry]

  ObligationDisposition* = enum
    ## Issue #161 slice 2. What became of one signed-overflow proof
    ## obligation. Per the ADR-0001 amendment, a promoted (Int-sorted)
    ## value may only be used in arithmetic if the obligation is either
    ## DISCHARGED statically or KEPT LIVE for the solver; these are the
    ## two legal outcomes, and every site records which one it took.
    odDischargedStatic  ## interval arithmetic proved the result stays
                        ## inside `[low(T), high(T)]` — no fork emitted,
                        ## the solver never sees this site
    odLive              ## not proven; `overflowCondInt` was pushed and
                        ## the raise fork is the solver's to resolve

  ObligationEntry* = object
    ## One arithmetic site on a width-typed Int-sorted value.
    op*:          IRBinop
    width*:       int                ## static Nim width of the operands
    signed*:      bool
    disposition*: ObligationDisposition
    bound*:       Option[Interval]   ## the proven result interval when
                                     ## discharged; `none` when live

  ObligationLog* = seq[ObligationEntry]

  SymexErrorSeverity* = enum
    ## Phase 15 Z3. Severity contract (cross-cluster invariant 7):
    ## an `sxUnknown` result must carry >= 1 `sevError`; a result whose
    ## errors are all `sevHint`/`sevWarning` must resolve to sat/unsat.
    sevHint     ## classified hint — informational; does NOT force sxUnknown
    sevWarning  ## non-fatal issue; walker continues; verdict may be valid
    sevError    ## halting error — causes sxUnknown result

  SymexErrorKind* = enum
    ## Phase 15 Z3. Closed set of classified symex error kinds, replacing
    ## the free-form `kind: string`. Prefixes: ek=Z3 engine, fe=front-end,
    ## se=string/seq, ee=exception, ge=generics, ce=closure, he=heap/ref.
    ## Phase-14 Z3Error kinds come first so Phase-15 kinds keep higher ordinals.
    ##
    ## STANDING RULE (RFC-0005 §3.2), which no mechanism can check: reusing an
    ## EXISTING kind at a NEW emission site asserts that the new site shares
    ## that kind's substitution class (`classOf`, below: what the site
    ## SUBSTITUTES -- a fresh unconstrained symbol, a forced value / stale
    ## env, a fabricated continuation, a pure omission, or no answer at all).
    ## `classOf`'s exhaustive `case` forces a row for a NEW kind but cannot
    ## see a reused one. If your site's class differs, split: tail-append ONE
    ## sibling for the minority funnel and keep this member for the majority
    ## (never retire-and-append-two -- each retirement is a permanent
    ## tombstone in every consumer `case`).
    ekZ3Error, ekZ3MemoryError, ekZ3InternalError, ekZ3SolverError,
    feUnsupportedOp, feExtractionFailed,
    feConvDomainExcluded, ## retired R16-2 — do not reuse ordinal.
                          ## (Was: sevHint emitted when float→int conversion domain
                          ## was bounded to the target integer range. Replaced by a
                          ## real RangeDefect raise fork in R16-2; the hint emission
                          ## was removed. Ordinal kept for CR-16 cache-key stability.)
    seUnsupportedStringOp, seUnsupportedRegex, seZ3StringIncomplete,
    seZ3VersionMissing,   ## Phase 15 S5: op requires a newer Z3 (e.g.
                          ## `Z3_mk_seq_replace_all`, absent < 4.15.5).
    seBytesSymbolicLength, seBytesLengthTooLarge,
    seByteIndexUnsupported, ## reserved/unused: no distinct runtime degrade site
                            ## for symbolic byte-index constructs — string index
                            ## `s[i]` is handled upstream through a different path
                            ## (the walker resolves the BV8 element directly).
                            ## Retained for enum ordinal stability (shifting would
                            ## invalidate any external consumer relying on ordinal
                            ## values).
    seByteIterUnsupported,
    seUnsupportedTableValType, seUnsupportedSetCharInterop,
    seNestedSeqUnsupported,
    seParseIntPreE,       ## Phase 15 S10a: parseInt non-digit input returned an
                          ## unconstrained model until S10b's raises-path landed.
                          ## NO LONGER EMITTED (S10b closed the window — a non-digit
                          ## parseInt now RAISES `ValueError`). Variant retained for
                          ## enum/cache stability; the emission is gone.
    eeUninterpRefExtraction,
    eeRaiseUnimplemented,  ## Phase 15 E1: walker hit an `isRaise` while
                           ## raise-flow semantics are not yet modeled
                           ## (structural cycle). sevError → sxUnknown.
    eeTryUnimplemented,    ## Phase 15 E1: walker hit an `isTry` while
                           ## try/except semantics are not yet modeled.
    eeRaiseOutsideHandler, ## Phase 15 E2b: a bare `raise` (re-raise) reached
                           ## with an empty handler stack and no in-flight
                           ## exception — nothing to re-raise. sevError →
                           ## sxUnknown (Invariant 3).
    eeNotInHandler,        ## Phase 15 E8: `getCurrentException()` /
                           ## `getCurrentExceptionMsg()` called outside any
                           ## `except` handler body (no in-flight exception).
                           ## sevError → sxUnknown (Invariant 3 — never a panic).
    eeUnknownExnType,      ## Phase 15 E4: a raised exception type is not in the
                           ## static `ExnTypeTable` nor `userExnHierarchy`. The
                           ## walker matches it ONLY against a bare `except:`
                           ## (conservative — no silent false-negative,
                           ## Invariant 3). sevWarning (verdict may still be
                           ## valid; the type may simply not be modeled yet).
    geInstantiationCapped, geConceptViolation,
    geUnresolvedGeneric,   ## reserved/unused: unresolved-generic constructs
                           ## produce a compile-time error() or fall to
                           ## geInstantiationCapped + sawUnknown → sxUnknown;
                           ## this variant is NEVER emitted. Retained for enum
                           ## ordinal stability (shifting would invalidate any
                           ## external consumer relying on ordinal values).
    geDistinctBijectivitySkipped,
    geDistinctBarrier,    ## Phase 15 G4 (net-new, sevError): an operation
                          ## attempted an IMPLICIT coercion between a `distinct`
                          ## type and its base (or two distinct types) without an
                          ## explicit conversion. The type wall forbids it
                          ## (Invariant 3 — classified, never a silent UNSAT).
    ceNotImplemented,
    ceUnsupportedCapture,  ## reserved/unused: a `ref T`-capturing closure was
                           ## previously classified here (before R13 landed the
                           ## heap machinery). R13 lifts the restriction; captures
                           ## of ref/ptr locals now succeed. This variant is NEVER
                           ## emitted. Retained for enum ordinal stability.
    ceUnsupportedHof,
    ceClosureUnknownCallee, ## Phase 15 C2b (ADR-0009 D6, Invariant 3): a
                            ## closure CALL whose callee variable does not
                            ## resolve to an `svClosure` in the current env
                            ## (e.g. a proc value the walker never bound).
                            ## sevError → sxUnknown (classified, never a
                            ## silent UNSAT or a crash).
    ceInlineBudgetExceeded, ## Phase 15 C2b: closure-application descent
                            ## exceeded `settings.maxClosureInlineCount`
                            ## (the `CallFrameCtx.closureInlineCount` budget).
                            ## sevError → sxUnknown (Invariant 3).
    heDepthExhausted, heUnsafeCast, hePtrArith, hePtrFamily,
    heFreshnessCapExceeded, heUnsupportedVarRef, heRefVariantUnsupported,
    heUnsupportedOwnership,
    heUnresolvedRef,       ## Phase 15 R1a (ADR-0010): the walker reached an
                           ## `itRef`/`itPtr`/`isDeref`/`isNew` while the
                           ## logical-heap semantics are not yet modeled
                           ## (structural cycle). sevError → sxUnknown
                           ## (Invariant 3). R1+ replace the stub with real
                           ## heap semantics. RFC-0005 S4: `liftHeapValue`'s
                           ## unsupported-pointee read no longer emits this
                           ## kind (split to `heUnsupportedPointeeRead`).
    geVtableDispatch,      ## Phase 16 INV (reserved/unused): subtype-dispatch /
                           ## vtable method call — when a `nnkMethodDef` callee
                           ## reaches `ensureProcRegistered`, the current walker
                           ## fires a compile-time `error()` rather than yielding
                           ## a classified sxUnknown (Phase 15 deferred; a future
                           ## phase wires the emission). NEVER EMITTED. Appended
                           ## at enum tail to preserve ordinal stability of all
                           ## preceding members (shifting would invalidate any
                           ## external consumer relying on ordinal values).
                           ## sevError → sxUnknown (Invariant 3).
    ceClosureBodyUncertain ## RFC-chapulin-hardening SND-1b (walker v39): a
                           ## closure-body return sub-path had `cp.uncertain ==
                           ## true` (SND-1 taint from an unmodeled statement,
                           ## or a nested maxCallDepth bail) — `applyClosureGround`
                           ## SKIPS folding that sub-path into
                           ## `currentClosureCallAxioms` (would otherwise
                           ## assert a possibly-wrong value as a PERMANENT
                           ## ground fact for the rest of the run) and instead
                           ## pushes this kind so `closureForcedUnknown`
                           ## whole-run-degrades the verdict to `sxUnknown`
                           ## (Invariant 3 — never a silent wrong sat/unsat).
                           ## Appended at enum tail (ordinal stability).
                           ## RFC-0005 S7: also joins `{scSpurious}` onto the
                           ## calling path (`closureDegrade`); the result is a
                           ## per-occurrence fresh constant (`dcFreshSymbol`).
    weInternalWalkerFault ## RFC-chapulin-hardening CR-1c (walker v43,
                          ## ADR-0020): the walker's last-resort safety net —
                          ## the final `except CatchableError` catch-all on the
                          ## `runSymex` try (`runtime.nim`) — classified a
                          ## genuinely UNANTICIPATED native exception (one that
                          ## matched NONE of the specific arms: NOT one of the
                          ## 18 named construct-gap carriers, NOT
                          ## `SymexClassifiedDegradeError`, NOT a `Z3Error`)
                          ## that escaped the walker from any dispatch depth.
                          ## DISTINCT from every `se*`/`fe*` construct-gap kind
                          ## by design: it means "the walker itself hit a bug
                          ## here", not "this SUT construct isn't modeled yet"
                          ## — CI/telemetry can track its occurrence as a live
                          ## walker-bug backlog (§0's totality-is-an-audit
                          ## philosophy) rather than treat it as an ordinary
                          ## degrade. sevError → sxUnknown (Invariant 3 — never
                          ## a crash, never a silent wrong sat/unsat). Appended
                          ## at enum tail (ordinal stability).
    beBudgetExhausted     ## Chapulin 0.1.0 re-test triage (catalog #5(b),
                          ## walker v64): a WALK BUDGET ran out with paths
                          ## still live — `maxLoopUnwind` k-unroll exhaustion
                          ## (the loop guard was still SAT-able past the
                          ## bound). RFC-0005 S6a narrowed it to exactly that
                          ## (`dcFabricated`): the `maxFrontierSize` prune is
                          ## now `beBudgetExhaustedPrune` and the
                          ## `maxCallDepth` / variant-constructor bails are
                          ## `beBudgetExhaustedUnmodelled`. The
                          ## affected paths are tainted/pruned and the run
                          ## degrades to `sxUnknown`; before v64 these sites
                          ## set `w.sawUnknown` bare, producing the
                          ## Invariant-7-violating "sxUnknown with EMPTY
                          ## errors" chapulin's re-test flagged. sevError →
                          ## sxUnknown. Appended at enum tail (ordinal
                          ## stability).
    feUnsupportedExprKind ## RFC-chapulin-hardening CR-2a (walker v44):
                          ## `parseExpr`'s expression-position catch-all
                          ## (`dsl_parser.nim`) reached a NimNode `kind` not
                          ## in its `case` — previously a macro-expansion
                          ## `error()` that aborted compilation outright
                          ## (strictly worse than `sxUnknown`; the SUT could
                          ## not be analysed at all). Now registers this
                          ## classified `sevError` and emits `mkUnsupported`
                          ## into the preamble, returning a type-correct dummy
                          ## (`classifyType(n).ty`). Sound because `of
                          ## isUnsupported` taints `Path.uncertain` (SND-1) —
                          ## the dummy can never produce a false witness; also
                          ## Class-A (`capForcedUnknown` backstops it
                          ## independently). Covers the whole expression-
                          ## position macro-error class (M2/M5/P1/P2a shapes).
                          ## Appended at enum tail (ordinal stability).
    feUnsupportedParamType ## RFC-chapulin-hardening CR-2b (walker v45):
                          ## `classifyType`'s resolved-type-name text-match
                          ## catch-all (`dsl_typebridge.nim`) reached a
                          ## PARAMETER type not in its supported scalar set
                          ## — previously a macro-expansion `error()` that
                          ## aborted compilation outright, before any proc
                          ## body was even walkable. A different mechanism
                          ## from `feUnsupportedExprKind` (CR-2a):
                          ## `classifyType` takes no `ctx`/`preamble`, so
                          ## there is no statement to taint and no sound
                          ## dummy `IRType`. Now classifies to an
                          ## `itUninterp("__unsupported:" & s)` placeholder;
                          ## `allocateSym` raises the generic
                          ## `SymexClassifiedDegradeError` carrier (CR-1c)
                          ## with this kind at parameter-allocation time —
                          ## before the body is walked — forcing a
                          ## WHOLE-RUN `sxUnknown` (Invariant 3 — never a
                          ## compile failure, never a walk-time crash).
                          ## Appended at enum tail (ordinal stability).
    feUnsupportedWitnessType ## RFC-chapulin-hardening CR-2c (walker v46):
                          ## `emitTyAndReader` (`symex.nim`) — the POST-
                          ## SOLVE witness-reader codegen macro, a THIRD
                          ## macro-`error()` surface distinct from CR-2a
                          ## (SUT-body parse) and CR-2b (param-type
                          ## classify) — reached a `seq`/`Table`/`HashSet`
                          ## element/key/value shape outside its fixed
                          ## renderable fragment (`isRenderableSeqElemTy`/
                          ## `isRenderableTableTy`/`isRenderableSetElemTy`
                          ## above) — previously a macro-expansion `error()`
                          ## that aborted compilation outright. `parseProc*`'s
                          ## TOP-LEVEL SUT parameter-classification loop
                          ## (`dsl_parser.nim`) now runs each parameter's
                          ## `classifyType` result through
                          ## `demoteUnrenderableWitnessTy`, applying the SAME
                          ## renderability predicate, and demotes an
                          ## unrenderable shape to an
                          ## `itUninterp("__unsupported_witness:" & s)`
                          ## placeholder instead of a real `itSeq`/`itTable`/
                          ## `itSet` (deliberately NOT inside `classifyType`
                          ## itself — it is also used for purely-internal,
                          ## non-witness types); `allocateSym` raises the generic
                          ## `SymexClassifiedDegradeError` carrier (CR-1c)
                          ## with this DISTINCT kind (not
                          ## `feUnsupportedParamType` — a different macro,
                          ## different call site, per §0's three-classes
                          ## framing) at parameter-allocation time — before
                          ## the body is walked and before the witness
                          ## reader is ever reached — forcing a WHOLE-RUN
                          ## `sxUnknown` (Invariant 3 — never a compile
                          ## failure, never a walk-time crash). Appended at
                          ## enum tail (ordinal stability).
    heNewFieldZeroUnsupported ## Cluster H Step C (ADR-0022): the universal
                          ## `isNew` zero-write (`runtime_heap.nim`) found a
                          ## freshly-allocated object FIELD whose type has no
                          ## clean zero encoding this cycle
                          ## (`zeroIRExprForType` returned `nil` — a
                          ## `seq`/`Table`/`HashSet`/`array`/variant/distinct
                          ## field). SND-1 taints the whole run to `sxUnknown`
                          ## (Invariant 3) rather than leaving that field's
                          ## heap cell unconstrained (which would risk a false
                          ## `sxSat`). Appended at enum tail (ordinal
                          ## stability).
    seUnsupportedTableKeyType ## N40 (round-6 fix round 6, allocateSym
                          ## totality). `allocateSym(itTable)`'s Table KEY
                          ## type is not modeled (only `Table[string, V]` is
                          ## backed — the Z3 array representation is always
                          ## `Z3Array[Z3String, ...]`). Previously an untagged
                          ## `raise newException(ValueError, ...)` — a crash on
                          ## ORDINARY user syntax (`Table[int, string]` is a
                          ## perfectly valid Nim type, not a walker-internal
                          ## invariant state), which `unallocatableFieldIssue`
                          ## (below) had a false-negative gap for prior to this
                          ## slice. DISTINCT from `seUnsupportedTableValType`
                          ## (the pre-existing sibling for a bad VALUE type)
                          ## so a human reading `errors[0].kind` can tell which
                          ## half of the `(K, V)` pair was unsupported.
                          ## sevError → sxUnknown (Invariant 3 — never a
                          ## crash, never a silent UNSAT). Appended at enum
                          ## tail (ordinal stability).
    seUnsupportedCompoundSortLeaf ## Round-6 N41: `rawAnyAstOf` (`runtime.nim`)
                          ## derives a SINGLE scalar leaf ast/sort for a
                          ## closure funcSym domain/range leaf (`sortOfTuple`)
                          ## or a heap array's value sort (`heapValueSort`,
                          ## `runtime_heap.nim`) — `svTable`/`svSet` are
                          ## COMPOUND values (a data `Z3Array` plus a separate
                          ## present `Z3Array`, never a single scalar ast), so
                          ## there is no sound representative leaf here,
                          ## REGARDLESS of whether the underlying Table/Set
                          ## shape itself is otherwise supported (DISTINCT
                          ## from `seUnsupportedTableKeyType`/
                          ## `seUnsupportedTableValType`/
                          ## `seUnsupportedSetCharInterop`, which classify an
                          ## unsupported KEY/VALUE/ELEMENT type specifically —
                          ## a perfectly valid `Table[string, int]` closure
                          ## param hits THIS gap instead). Previously an
                          ## untagged `raise newException(ValueError, ...)` —
                          ## a crash that escaped uncaught to the top-level
                          ## `runSymexImpl` catch-all (`weInternalWalkerFault`,
                          ## a WHOLE-RUN degrade with no per-path precision),
                          ## masking the itTable/itSet family behind the
                          ## walker's generic "the walker itself hit a bug"
                          ## carrier instead of a construct-gap kind.
                          ## sevError → sxUnknown (Invariant 3 — never a
                          ## crash, never a silent wrong sat/unsat). Appended
                          ## at enum tail (ordinal stability).
    beBudgetExhaustedAssumedBound ## N20 (RFC-chapulin-hardening bucket-2,
                          ## walker v121). A SIBLING of `beBudgetExhausted`,
                          ## not a replacement: the plain while-loop k-unroll
                          ## (`isWhile`, no closed-form recognizer match) never
                          ## consults path-condition feasibility per iteration
                          ## — it structurally forks BOTH the continue and
                          ## exit branches at every one of `maxLoopUnwind`
                          ## iterations regardless of whether the continue
                          ## branch is provably infeasible, so `active.len > 0`
                          ## after the unwind loop fires even for a loop whose
                          ## trip count a `symexAssume` call has ALREADY
                          ## bounded well under `maxLoopUnwind` — reproduced
                          ## concretely (`symexAssume(n < 3)` with
                          ## `maxLoopUnwind` at its default 5 still reports
                          ## exhaustion). This is a STRUCTURAL k-unroll
                          ## limitation, not a real "ran out of budget"
                          ## signal — the honest fix (a per-iteration
                          ## satisfiability check on the continue branch, à la
                          ## `trySolve`) would multiply Z3 calls by
                          ## `unwind × active-path-count` for EVERY plain
                          ## while-loop in EVERY run, a genuine architecture
                          ## change this round's scope excludes (this
                          ## engine's `trySolve`/`s.check()` calls are
                          ## deliberately deferred to path-TERMINAL points
                          ## only — no other walk arm calls the solver
                          ## mid-loop). `collectAssumedLoopBound`
                          ## (`dsl_parser.nim`, parse-time, mirrors
                          ## `collectIntOffsetParams`'s established
                          ## precedent) marks `IRStmt.isWhile.wHasAssumedBound`
                          ## when the guard references a variable ALSO
                          ## constrained by a preceding `symexAssume` in the
                          ## same proc body — a purely LEXICAL, zero-solver-
                          ## cost signal, deliberately conservative (a
                          ## variable-name match, not a provable-bound
                          ## derivation) — so this kind is emitted INSTEAD OF
                          ## `beBudgetExhausted` (never both) exactly when
                          ## that signal fires, letting the ordinary
                          ## "genuinely unbounded loop" case keep its
                          ## unchanged classification while a caller/auditor
                          ## can distinguish "assumed-bounded but the
                          ## structural k-unroll couldn't use it" from
                          ## "no assumed bound exists at all." sevError →
                          ## sxUnknown (Invariant 3 — never a crash, never a
                          ## silent wrong sat/unsat; the STATUS/soundness
                          ## behavior is UNCHANGED from `beBudgetExhausted` —
                          ## only the classification is more honest).
                          ## Appended at enum tail (ordinal stability).
    feOpaqueCallUnmodelled ## Issue #163 (walker v131): `walk`'s `#137`
                          ## opaque-call arm (`runtime.nim`) reached a call
                          ## the front end classified as a black box — a
                          ## member of `OpaqueEffectfulProcs` (`echo`,
                          ## `readLine`, `writeFile`, …) or a user proc
                          ## carrying `{.symexOpaque.}` — whose result or
                          ## effects the walker cannot model, so every
                          ## continuation is tainted. `fe` and not `we`
                          ## deliberately: the black-box decision is the
                          ## FRONT END's (the parser chose `mkOpaqueCall`),
                          ## and this is an ordinary construct gap, not
                          ## "the walker itself hit a bug here". Before
                          ## #163 this arm set `w.sawUnknown` BARE, so an
                          ## `echo` ahead of the interesting branch reported
                          ## `weInternalWalkerFault` — the Invariant-7
                          ## backstop — instead of naming the call that cost
                          ## the answer. The message carries the callee name
                          ## for exactly that reason. sevError → sxUnknown
                          ## (Invariant 3; the soundness behavior is
                          ## UNCHANGED — only the classification is honest).
                          ## Appended at enum tail (ordinal stability).
    feEnumOrdinalUnresolved ## Issue #163 review R19: `dsl_parser.parseExpr`'s
                          ## `nnkSym` arm resolves an enum CONSTANT's ordinal
                          ## by finding its declaring `nnkEnumTy` body via
                          ## `n.getTypeInst` -> `getImpl` (R15's fix — the
                          ## only route that keeps explicit field values,
                          ## per R15's own `getType`-discards-values probe).
                          ## This kind fires when `getTypeInst` does NOT
                          ## resolve to a usable enum impl. The RETIRED
                          ## fallback here used to re-resolve via the direct
                          ## `n.getType` path instead — but that path is
                          ## PROVEN (same R15 probe) to always reconstruct
                          ## the enum with every explicit value discarded,
                          ## so it could only ever be right for a dense
                          ## zero-based enum by coincidence, and silently
                          ## wrong (a confidently-embedded, provably
                          ## incorrect constant) for any enum with an
                          ## explicit non-auto ordinal — the exact defect
                          ## class R15 exists to close, reopened one level
                          ## up. Whether some generic- or alias-mediated
                          ## shape can still defeat `getTypeInst` for a
                          ## legitimately-typed enum field symbol is not
                          ## enumerated; per Invariant 3, the answer to "not
                          ## proven unreachable" is to decline and name the
                          ## cause, not guess. `fe` (front-end): the failure
                          ## is in ordinary constant resolution, not a
                          ## walker-internal fault. sevError → sxUnknown.
                          ## Appended at enum tail (ordinal stability).
    feTransparentArgNotInert ## RETIRED RFC-0005 S8 (§13.3, i3 -- Corey
                          ## 2026-09-26) -- retained for ordinal stability,
                          ## NEVER EMITTED. Not a decline: nothing is
                          ## approximated because of it (the opaque fallback's
                          ## own `feOpaqueCallUnmodelled` taints every path
                          ## through the call); it reports that the user's
                          ## pragma claim is false. That report now rides the
                          ## verdict-neutral `AnnotationViolation` channel
                          ## (`avArgNotInert`). History follows.
                          ## Issue #163 review R7: a `{.symexTransparent.}`
                          ## callee in STATEMENT position was deleted
                          ## UNCONDITIONALLY (`dsl_parser.nim`'s statement-arm
                          ## `hasSymexTransparentPragma` branch) -- never
                          ## consulting `isInertArg`/`isInertOpaqueCall`, the
                          ## very predicate its OPAQUE sibling a few lines
                          ## below applies to the same argument shapes. A
                          ## `var` formal (`nnkHiddenAddr`) or a `ref`/`ptr`/
                          ## object-that-may-carry-a-ref argument lets the
                          ## real callee write through or observe state the
                          ## deleted call's absence cannot account for --
                          ## `withMutateT`/`mutate(m); if m != x: ...` is the
                          ## concrete false-`sxUnsat` witness. The parser now
                          ## emits THIS kind (parse-time, `ctx.parseErrors`)
                          ## naming the callee and which promise it broke,
                          ## alongside the generic `feOpaqueCallUnmodelled`
                          ## the resulting opaque-call fallback also produces
                          ## at walk time -- so the message a caller sees is
                          ## specific ("tagged `{.symexTransparent.}` but
                          ## takes a writable argument, treated as opaque")
                          ## rather than only the generic unmodelled-call
                          ## text, which would otherwise tell an already-
                          ## compliant caller to do the very thing they
                          ## already did. `fe` (front-end): the parser's own
                          ## pragma-honouring decision, not a walker fault.
                          ## sevError -> sxUnknown (Invariant 3 -- fails
                          ## SAFE, never a silent wrong verdict). Appended at
                          ## the enum tail WHEN IT LANDED (ordinal stability);
                          ## `feTransparentResultUsed` (R10) was appended after
                          ## it, so this is no longer the last member -- append
                          ## new kinds after the CURRENT tail, not here.
    feTransparentResultUsed ## RETIRED RFC-0005 S8 (§13.3, i3 -- Corey
                          ## 2026-09-26) -- retained for ordinal stability,
                          ## NEVER EMITTED; now the `AnnotationViolation`
                          ## channel's `avResultUsed` (see
                          ## `feTransparentArgNotInert`, above). History
                          ## follows.
                          ## Issue #163 review R10: the OTHER way a
                          ## `{.symexTransparent.}` callee can over-claim its
                          ## promise -- R7 (`feTransparentArgNotInert`, above)
                          ## covers the statement-position/non-inert-argument
                          ## route; this covers the EXPRESSION-position route,
                          ## where the call's RESULT is used. Both routes fall
                          ## back to `{.symexOpaque.}` handling
                          ## (`dsl_parser.nim`'s expression-position call arm)
                          ## and both also reach the generic
                          ## `feOpaqueCallUnmodelled` at walk time -- but that
                          ## generic message tells the caller to "mark it
                          ## `{.symexTransparent.}`", which is actively wrong
                          ## advice for a callee that already carries the
                          ## pragma. The parser now emits THIS kind
                          ## (parse-time, `ctx.parseErrors`) naming the callee
                          ## and the real broken promise -- the pragma is
                          ## honoured only in STATEMENT position, not that the
                          ## pragma is missing. `fe` (front-end): the parser's
                          ## own pragma-honouring decision, not a walker
                          ## fault. sevError -> sxUnknown (Invariant 3 --
                          ## fails SAFE, never a silent wrong verdict).
                          ## Appended at the enum tail WHEN IT LANDED (ordinal
                          ## stability); `feGlobalReadUnmodelled` was appended
                          ## after it, so this is no longer the last member --
                          ## append new kinds after the CURRENT tail, not here.
    feGlobalReadUnmodelled ## Issues #161/#163 handoff: `lower`'s `iekVar` arm
                          ## (`runtime.nim`) reached a name absent from the
                          ## current `env` -- the walker does not model
                          ## module-level globals AT ALL, and the parser
                          ## deliberately passes a free/global name through as
                          ## a bare `iekVar` (every local/param the parser
                          ## emits is bound before its first read, so an
                          ## unbound name here is never a parser bug). Before
                          ## this kind, the resulting `KeyError` escaped to
                          ## the top-level catch-all and reported
                          ## `weInternalWalkerFault` -- an internal-bug
                          ## attribution for an ordinary, everywhere-
                          ## applicable modeling gap. The message carries the
                          ## unbound name so the user knows which global to
                          ## remove from the reachable computation (or thread
                          ## through as an explicit parameter). sevError ->
                          ## sxUnknown (Invariant 3); the soundness argument
                          ## this unblocks: #163 slice 4's opaque-call
                          ## inertness proof relies on this decline being
                          ## real and classified -- see `isInertOpaqueCall`'s
                          ## doc, dsl_parser.nim. `seVariantFieldOnDeclinedCtor`
                          ## was appended after it, so this is no longer the
                          ## last member -- append new kinds after the
                          ## CURRENT tail, not here.
    seVariantFieldOnDeclinedCtor ## #163 regression fix (post-round-9 gate).
                          ## `isVariantField`'s walker arm (`runtime.nim`)
                          ## reached a receiver SymVal that is NEITHER
                          ## `svVariant` NOR `svMultiVariant` -- reachable
                          ## ONLY when the receiver's own CONSTRUCTION already
                          ## declined (`itVariant`/`itMultiVariant` object-
                          ## constructor edge cases in `dsl_parser.nim` return
                          ## a bound placeholder, per `unsupportedFieldPlaceholder`'s
                          ## own documented residual: no literal IR constructor
                          ## exists for a variant-shaped value, so the
                          ## placeholder is a plain `mkIntLit(0)`, deliberately
                          ## NOT variant-shaped) -- a later field read on that
                          ## already-tainted value is a REAL, reachable
                          ## consequence of an ALREADY-recorded classified
                          ## decline, not a fresh walker bug. Before this
                          ## kind, the receiver-kind mismatch was a bare
                          ## `doAssert false` (an uncatchable `AssertionDefect`
                          ## crash), reported at the `runSymex` boundary as
                          ## `weInternalWalkerFault` -- an internal-bug
                          ## attribution for an ordinary, everywhere-
                          ## applicable consequence of an existing, honestly-
                          ## classified construction gap. sevError ->
                          ## sxUnknown (Invariant 3). Appended at enum tail
                          ## (ordinal stability). The RFC-0005 S1b kinds were
                          ## appended after it, so this is no longer the last
                          ## member -- append new kinds after the CURRENT tail.
    # ---- RFC-0005 S1b (§2.2 "the premise 'every taint site has a kind in
    # hand' is false"): the kinds for the degrade sites that recorded NO
    # `SymexErrorInfo` before S1b. Each of these sites used to reach the
    # drain only through a transitional kindless ⊤ mark, so a run whose ONLY
    # degrade was one of them hit the Invariant-7 backstop and was stamped
    # `weInternalWalkerFault` -- a walker-bug attribution for an ordinary,
    # classifiable degrade. Every one is routed through `degrade()`
    # (`runtime.nim`), which records. All six are `dcNoAnswer` in `classOf`
    # (the conservative ⊤ default); S4-S6 reclassify. Appended at the enum
    # tail, in this order (ordinal stability).
    feUnsupportedStmtKind ## RFC-0005 S1b: a STATEMENT-position shape outside
                          ## the supported fragment that the parser replaces
                          ## by an `isUnsupported` node WITHOUT a parse-time
                          ## error of its own (§2.5's "Class-B" sites in
                          ## `dsl_parser.nim`: the `statement kind ... not in
                          ## supported fragment` catch-all, unmodelled
                          ## `nnkAsgn`/augmented-assign shapes, a statement
                          ## call outside the fragment, the A3/ADR-0014
                          ## iterator-inlining declines, an uninitialised
                          ## `var` of an unmodelled type). The statement is
                          ## DROPPED -- its effects never reach `env` -- so the
                          ## surviving path is tainted. The kind rides the
                          ## `isUnsupported` node (`IRStmt.unKind`) and is
                          ## recorded by the walker's `isUnsupported` arm when
                          ## a path reaches it. The expression-position
                          ## sibling is `feUnsupportedExprKind` (Class-A,
                          ## paired with a parse error). sevError -> sxUnknown.
    weRecursionCycleCut   ## RFC-0005 S1b: the `isCall` arm met a call whose
                          ## `argShapeKey` is already on `w.activeCalls` --
                          ## the callee is being walked further up the stack
                          ## with an identical argument shape (mutual/direct
                          ## recursion, or an `argShapeKey` hash collision).
                          ## The cycle is CUT: the call returns a fresh
                          ## unconstrained `_cyc` symbol, the callee's body
                          ## (its var-param/heap effects and raises) is not
                          ## walked for this occurrence, and the path is
                          ## tainted. Before S1b it recorded nothing and did
                          ## not mark the run (only a later tainted target
                          ## hit did). sevError -> sxUnknown.
    eeHandlerReraiseUnmodelled ## RFC-0005 S1b: a bare `raise` (re-raise)
                          ## reached with a NON-empty handler stack but no
                          ## in-flight exception -- e.g. a bare `raise` in a
                          ## `try` BODY, where real Nim raises
                          ## `ReraiseDefect`. Not modelled; the path is
                          ## dropped. Distinct from `eeRaiseOutsideHandler`
                          ## (empty handler stack). sevError -> sxUnknown.
    ceClosureBodyDiverged ## RFC-0005 S1b: a closure application
                          ## (`applyClosureGround`) whose body produced NO
                          ## value-bearing exit at all -- no `return`, no
                          ## fall-through (every body path raised, halted or
                          ## was dropped) -- so the call's result symbol is
                          ## unconstrained by any body path. A void closure
                          ## that falls through is NOT this (it has
                          ## fall-through paths). Recorded in the WALK sink,
                          ## not the closure sink: it must not trip the
                          ## closure veto (`closureForcedUnknown`), which it
                          ## never did before S1b. sevError -> sxUnknown.
                          ## RFC-0005 S7: the body's raises now reach the
                          ## caller and the continuation past the call is
                          ## made infeasible (exit coverage `false`), so the
                          ## site is a halt: `dcOmitted`.
    weBreakOutsideLoop    ## RFC-0005 S1b: an `isBreak`/`isContinue` reached
                          ## with an EMPTY loop stack. Surface route: the
                          ## parser flattens `block:` into its body, so a
                          ## `break` out of a top-level `block` arrives here
                          ## with no loop frame; the breaking path is dropped
                          ## instead of resuming after the block. (`continue`
                          ## outside a loop is rejected by Nim itself, so it
                          ## is reachable only from hand-built IR.) sevError
                          ## -> sxUnknown.
    beSolverUndef         ## RFC-0005 S1b (§3.1's solver-undef row): `trySolve`
                          ## returned `zsUnknown` -- Z3 gave up on a path that
                          ## reached a finding (the `isTargetLabel` hit or
                          ## `routeRaise`'s raised finding): the deterministic
                          ## `queryRLimit` truncation, or an incomplete theory.
                          ## Distinct from the `ekZ3*` kinds, which are minted
                          ## only from RAISED Z3 exceptions, never from an
                          ## unknown RESULT; before S1b this recorded nothing,
                          ## so a run whose only degrade was a routine solver
                          ## resource-out was stamped `weInternalWalkerFault`.
                          ## The natural carrier for the rlimit provenance
                          ## RFC-0005 §8.2 owes RFC-0011/0008. sevError ->
                          ## sxUnknown.
    heUnsupportedPointeeRead ## RFC-0005 S4 (§3.2 split of `heUnresolvedRef`,
                          ## the minority funnel): a heap READ whose pointee
                          ## kind `liftHeapValue` does not lift (a `string`/
                          ## `seq`/`Table`/`HashSet`/`distinct`/... field or
                          ## bare pointee reached through a `ref`/`ptr`). The
                          ## select happens on the NON-NIL continuation (the
                          ## NilAccessDefect fork already ran), and the read
                          ## value is replaced by a FRESH, per-occurrence,
                          ## UNCONSTRAINED symbol of the pointee type -- a
                          ## superset of whatever the real cell holds, so
                          ## `classOf` is `dcFreshSymbol`. Split off because
                          ## every OTHER `heUnresolvedRef` site substitutes
                          ## differently (the non-ref-SymVal deref arms skip
                          ## the nil fork, the write arms drop the write, the
                          ## boundary arm aborts the run): reusing that kind
                          ## here would have promoted them all. sevError; as
                          ## `dcFreshSymbol` it blocks `sxSat` on its own path
                          ## (a candidate until replay confirms it) but never
                          ## `sxUnsat` on the run.
    seRuneDecodeSymbolic  ## RFC-0005 S5 (§3.2 split of `seZ3StringIncomplete`,
                          ## the minority funnel): a UTF-8 rune decode over a
                          ## SYMBOLIC string -- `runeLen(s)` / `for r in
                          ## s.runes` (ADR-0017). Variable-length grouping over
                          ## an unknown byte stream has no quantifier-free
                          ## encoding, so the PARSER declines: `runeLen(s)` is
                          ## replaced by the literal `0` and the `runes` loop
                          ## statement is dropped (its body's effects never
                          ## happen). Both substitute -- `classOf` is
                          ## `dcSubstituted`. Split off because every OTHER
                          ## `seZ3StringIncomplete` site is a lowering-time
                          ## `degradeStrArm` decline whose result is a fresh
                          ## per-read symbol (`dcFreshSymbol`): reusing that
                          ## kind here would have promoted a forced `0`.
                          ## sevError -> sxUnknown.
    beBudgetExhaustedPrune ## RFC-0005 S6a (§3.2 split of `beBudgetExhausted`,
                          ## the `dcOmitted` minority funnel): the
                          ## `maxFrontierSize` post-step frontier prune
                          ## (`walkBlock`, `runtime.nim`) EVICTED live paths.
                          ## The evicted paths are dropped outright and the
                          ## kept paths are untouched -- a pure
                          ## under-approximation, so `classOf` is `dcOmitted`
                          ## (`{scIncomplete}` on the run: an UNSAT claim over
                          ## the pruned run is void; `{}` on the path, which is
                          ## inert because the site is a HALT -- no survivor
                          ## receives the token). Split off because the
                          ## k-unroll survivor that keeps `beBudgetExhausted`
                          ## is `dcFabricated` and the call-depth/variant bails
                          ## (`beBudgetExhaustedUnmodelled`) substitute:
                          ## classifying the merged kind by THIS site would
                          ## have stripped the path taint from both. sevError
                          ## -> sxUnknown.
    beBudgetExhaustedUnmodelled ## RFC-0005 S6a (§3.2 split of
                          ## `beBudgetExhausted`, the `dcSubstituted` minority
                          ## funnel): a walk budget ran out and the walker
                          ## CONTINUED PAST an operation it did not model. The
                          ## `maxCallDepth` bail (`isCall`) binds the result to
                          ## a fresh havoc `retSym` but drops the callee's
                          ## var-param writes, heap writes and raises, and never
                          ## lowers the actuals; the `maxVariantConstructorForks`
                          ## / `maxVariantConstructorFieldAllocs` declines
                          ## (`isVariantConstructSym`) leave the destination
                          ## UNBOUND and never lower the discriminant or
                          ## plain-field operands. Both leave a stale env (and
                          ## drop raise forks), neither ⊇ nor ⊆ the real
                          ## behaviour set: `classOf` is `dcSubstituted`, ⊤ on
                          ## both coordinates. sevError -> sxUnknown.
    feUnsupportedOpHavoc  ## RFC-0005 S6b (§3.2 split of `feUnsupportedOp`,
                          ## the `dcFreshSymbol` minority funnel): an
                          ## unmodelled operation whose result is replaced by a
                          ## FRESH, per-evaluation, unconstrained symbol of the
                          ## result sort, with every operand already lowered
                          ## and nothing else dropped -- a superset of the real
                          ## behaviours. The sites: `iteSV`'s svUninterpRef /
                          ## genuine-svSeq / svString-svTable-svSet merges, the
                          ## same-width reinterpret of an Int-sorted operand,
                          ## ordering on two bools (system's magic `<`), the
                          ## closure-environment leaf equality conjunct, and
                          ## the three composite call-result bindings whose
                          ## per-call `retSym` (a `synthZ3`-numbered name) is
                          ## left free (explicit `return`, implicit `result`
                          ## fallthrough, untouched result with no
                          ## zero-default). `classOf` is `dcFreshSymbol`:
                          ## `{scSpurious}` on both coordinates -- a hit through
                          ## it is a candidate, and it does not void `sxUnsat`.
                          ## A new site may reuse this kind ONLY if its operands
                          ## are lowered first, its symbol is fresh per
                          ## evaluation and it drops no fork, write or raise.
    feUnsupportedOpAborted ## RFC-0005 S6b (§3.2 split of `feUnsupportedOp`,
                          ## the `dcNoAnswer` minority funnel): the §3.3
                          ## boundary abort -- a `SymexUnsupportedOpError`
                          ## (an unmodelled `math.<name>` / float op raised by
                          ## `runtime_floats.nim`) unwound the whole walk to
                          ## `runSymex`, which reports `sxUnknown` with no
                          ## path at all. No enlarged or shrunk program exists
                          ## for an aborted walk: `classOf` is `dcNoAnswer`.
                          ## sevError -> sxUnknown.
    seParseIntLaxSyntax   ## RFC-0005 S10. `parseInt(s)`'s raise predicate
                          ## on a string with a `+` prefix or a `_`: Nim's
                          ## `rawParseInt` accepts both, Z3's `str.to_int` is
                          ## -1 on both, so the modelled `ValueError` raise
                          ## there is a SUPERSET of the real one
                          ## (`drainParseIntRaises`, `ParseIntRaise.lax`).
                          ## Taints the raise fork only; `classOf` is
                          ## `dcFreshSymbol` (`{scSpurious}` on both
                          ## coordinates): a raise it produces is a
                          ## replay-gated candidate, and it never voids
                          ## `sxUnsat`. sevError.
    feReplayRefuted       ## RFC-0005 S10 (§4.2 `roRefuted`). NOT a degrade:
                          ## the verdict-time replay of a candidate's witness
                          ## ran the real SUT to completion without reaching
                          ## the target -- a CONFIRMED model gap on that
                          ## witness, surfaced as its own classified
                          ## diagnostic on the `sxUnknown` result. Recorded
                          ## by `symex.nim`'s `settleCandidate` AFTER
                          ## `runSymex` returns, so it never enters
                          ## `runTaint`; always `sevHint`. `classOf` is
                          ## `dcFreshSymbol`: only an entirely fresh-symbol
                          ## path is replayed at all (`replayEligible`), so
                          ## the gap it names is that class's.

  DefectKind* = enum
    ## Phase 15 Z3. Nim defect families the walker may model as raise-paths.
    dkAssertionDefect    ## assert / doAssert / raiseAssert
    dkIndexDefect        ## array/seq out-of-bounds
    dkFieldDefect        ## object field access on wrong variant
    dkRangeDefect        ## range constraint violation
    dkOutOfMemoryDefect  ## allocation failure
    dkStackOverflowDefect
    dkOther              ## user-defined defect types
                         ## Phase 15 E6: `dkOther` covers ALL user-defined
                         ## `Defect` subtypes, so they cannot be excluded
                         ## individually — either all user defects are
                         ## excluded (by including `dkOther` in
                         ## `defectExclusions`) or none are.
    ## ⚠ CR-16 ORDINAL-STABILITY RULE: ALWAYS APPEND new members at the END
    ## of this enum. `defectExclusions` is a `set[DefectKind]` rendered into
    ## the cache key; inserting or reordering shifts existing ordinals and
    ## silently changes every cached `;de=` digest. Never reorder — only append.
    dkOverflowDefect     ## R16-1 (Phase 16 ADR-0011 F3): integer +/-/* overflow
    dkDivByZeroDefect    ## R16-1 (Phase 16 ADR-0011 F3): div/mod by zero

  ArithCheck* = enum
    ## R16-1 (Phase 16 ADR-0011 F2). Gates which arithmetic defect forks the
    ## walker EMITS. This is the "policy" axis: an unchecked kind is never
    ## forked so it never pays path-multiplicative cost. Empty set = release-like
    ## (all arithmetic is unchecked / wrapping). Default = all-on (debug-like).
    ## `defectExclusions` is the orthogonal "surfacing" axis: the fork is
    ## emitted but the finding is suppressed when the kind is excluded.
    ##
    ## ⚠ CR-16 ORDINAL-STABILITY RULE: ALWAYS APPEND new members at the END
    ## of this enum. `arithChecks` is a `set[ArithCheck]` rendered into the
    ## cache key (`;ac=`); inserting or reordering silently changes every cached
    ## digest. Never reorder — only append.
    acOverflow   ## fork +/-/* overflow → OverflowDefect raise
    acDivByZero  ## fork div/mod-by-zero → DivByZeroDefect raise
    acRange      ## fork float→int out-of-range → RangeDefect raise (R16-2);
                 ## also int-width narrowing (R16-5, deferred). Scope in R16-1:
                 ## float→int domain checks only (RD2) — no fork emitted yet.

  InlinePolicy* = enum
    ## Phase 15 Z3 (def moved here from Cluster C so SymexSettings.inlinePolicy
    ## resolves before Cluster C opens). `seqInlineThreshold` is only
    ## meaningful under `ipHybrid`.
    ipAlwaysInline      ## walk body for every call site (no axiom)
    ipAlwaysAxiomatize  ## emit summary axiom; never walk body
    ipHybrid            ## walk up to seqInlineThreshold times, then axiomatize

  DeclineScopeKind* = enum
    ## RFC-0005 S8 (§2.5 "Where the scope lives"). WHERE a decline is
    ## anchored, so the verdict can ask the one question the blanket vetoes
    ## (`capForcedUnknown`/`closureForcedUnknown`) insure against instead of
    ## answering: was this decline reached? The CHANNEL stays derived from
    ## `kind` (`classOf`); the scope is different data -- no existing field
    ## carries it.
    dskUnplaced     ## §2.5 point 4 ("bucket 4") -- the engine cannot say where this
                    ## decline sits, so it cannot say whether it was reached:
                    ## a walker-completeness DEFECT, not a property of the
                    ## SUT. The DEFAULT (ordinal 0) on purpose: a record built
                    ## without a scope lands here, where the S8 totality pin
                    ## (`tests/tsymex_rfc0005_s8_scope.nim`) counts it.
    dskSiteAnchored ## §2.5 point 1: a parse-time decline at a program site.
                    ## `markerId` names the `isUnsupported`/`isUnsafeCast` node
                    ## the parser minted in the same act (`declineAtSite`,
                    ## `dsl_parser.nim`); the walker records the SAME anchor
                    ## when a path reaches that node, so reach is a join on
                    ## `markerId`.
    dskSignature    ## §2.5 point 2: the unmodellable thing IS the SUT's
                    ## signature (a parameter type allocation declines before
                    ## any walk state exists). Run-wide by construction.
    dskCalleeKey    ## §2.5 point 3 (added in round 2): an unregistered-
                    ## callee decline (`geInstantiationCapped`,
                    ## `geDistinctBarrier`, `geConceptViolation`, unresolvable-
                    ## `getImpl` `feUnsupportedOp`). `calleeKey` is the
                    ## never-registered `mkCall` key (`unregisteredCalleeKey`);
                    ## the walker's missing-callee arm records the SAME key
                    ## when a path reaches the call.
    dskWalkSite     ## RFC-0005 S8, not in the RFC's §2.5 sketch (which scoped
                    ## only the PARSE-time records the veto reads): a record
                    ## the WALKER made at the site it was walking -- a
                    ## `degrade`/`lowerDegrade`/`closureDegrade`/`allocDegrade`
                    ## funnel, the extraction sink, or a `runSymex` boundary
                    ## abort raised mid-walk. Such a record exists only
                    ## because a path reached its site, so its reach is the
                    ## record itself; it needs no join.

  DeclineScope* = object
    ## RFC-0005 S8 (§2.5). The anchor of one `SymexErrorInfo`. Build with
    ## `siteAnchored`/`calleeKeyed`/`signatureScope`/`walkSite`; the default
    ## value is `dskUnplaced` (bucket 4).
    case kind*: DeclineScopeKind
    of dskSiteAnchored:
      markerId*: int
    of dskCalleeKey:
      calleeKey*: string
    of dskUnplaced, dskSignature, dskWalkSite:
      discard

  SymexErrorInfo* = object
    ## Phase 14 cycle C4 / Phase 15 Z3. Structured symex-error record.
    ## `kind` is a closed `SymexErrorKind` (was a free-form string);
    ## `severity` carries the invariant-7 contract.
    kind*:     SymexErrorKind
    severity*: SymexErrorSeverity
    msg*:      string
    scope*:    DeclineScope
      ## RFC-0005 S8 (§2.5). Where this decline is anchored. Meaningful on
      ## every entry `taintsRun` admits (the declines); a `sevHint`/plain
      ## `sevWarning` diagnostic is not a decline and keeps the default. The
      ## structural invariant, pinned by `tests/tsymex_rfc0005_s8_scope.nim`:
      ## no admitted entry is `dskUnplaced` except a named, enumerated one.

  SymexAnnotation* = enum
    ## RFC-0005 S8 (§13.3, i3 -- Corey 2026-09-26). A user annotation symex
    ## honours on the strength of the user's promise.
    saSymexTransparent  ## `{.symexTransparent.}`: "this call is void and
                        ## observably inert -- drop it"

  AnnotationViolationKind* = enum
    ## RFC-0005 S8 (§13.3). WHICH promise of the annotation the call site
    ## contradicts.
    avResultUsed    ## the call's RESULT is used (expression position), but
                    ## the pragma is honoured only in statement position
                    ## (was `feTransparentResultUsed`, issue #163 review R10)
    avArgNotInert   ## statement position, but an argument is not provably
                    ## inert -- a `var`/`ref`/`ptr`/possibly-ref-carrying
                    ## argument the callee could write through (was
                    ## `feTransparentArgNotInert`, issue #163 review R7)

  AnnotationViolation* = object
    ## RFC-0005 S8 (§13.3, i3 resolved by Corey 2026-09-26). A user's
    ## annotation claim that the parser found to be FALSE at a call site.
    ## NOT a decline: nothing is approximated because of it -- the call falls
    ## back to opaque handling, whose walk-time `feOpaqueCallUnmodelled`
    ## degrade taints every path through it (the soundness), so this record
    ## is verdict-NEUTRAL by construction: no `classOf`, no `DeclineScope`,
    ## no taint, never read by the verdict or by either blanket veto. It is
    ## error-severity in spirit -- the user's code carries a wrong promise --
    ## and rides its own channel (`SymexProgram.annotationViolations` ->
    ## `RawResult`/`SymexResult.annotationViolations`) so it stays loud
    ## without masquerading as a modelling gap. S11 renders it.
    pragma*: SymexAnnotation         ## the annotation that was violated
    kind*:   AnnotationViolationKind ## which of its promises broke
    callee*: string                  ## the annotated callee's name
    site*:   string                  ## `file:line:col` of the call site
    msg*:    string                  ## the human-readable explanation

  # ---- RFC-0005 S1: soundness channels (§2.1) ------------------------------
  # Declared HERE, in `smt/types.nim` (which imports no z3), so the lattice is
  # Z3-free: RFC-0005 §8.2 -- RFC-0007's trace engine shares it.
  SoundnessChannel* = enum
    ## RFC-0005 §2.1. The two structurally opposite ways the walker can be
    ## wrong about a program, named for the FAILURE MODE they license rather
    ## than the approximation direction (so the verdict rule reads
    ## `scSpurious notin winnerTaint` / `scIncomplete notin runTaint`).
    scSpurious    ## over-approximating: modelled ⊇ real. A witness on such a
                  ## path may be spurious. Blocks sxSat for THIS path.
    scIncomplete  ## under-approximating: modelled ⊆ real. A proof over such a
                  ## run may have missed behaviours. Blocks sxUnsat RUN-WIDE.

  Taint* = set[SoundnessChannel]
    ## RFC-0005 §2.1. The powerset lattice on two elements: `⊥ = {}` (clean,
    ## the identity of join), `⊤ = {scSpurious, scIncomplete}` (the
    ## incomparable/"wrong, not merely coarse" class of §0.2); join is set
    ## union. Carried per PATH (`Path.taint`, written at degrade sites) and
    ## per RUN (`WalkCtx.runTaint`, DERIVED at drain from the error seqs --
    ## §2.2 "The run coordinate is derived, not written").

  DegradeClass* = enum
    ## RFC-0005 §2.2. What a degrade site SUBSTITUTES, named -- the five
    ## meaningful points of the four-coordinate (path, run) product. A
    ## `classOf` row is a reviewable judgment ("kind K is dcFabricated"),
    ## and the coordinates are derived once, in `pathTaint`/`runTaint`.
    dcFreshSymbol   ## substitutes a fresh unconstrained symbol: modelled ⊇ real
    dcSubstituted   ## forced value / stale env: modelled neither ⊇ nor ⊆ real
    dcFabricated    ## the survivor path is fiction, but the omission is real:
                    ## ⊤ on the path, {scIncomplete} on the run (k-unroll survivor)
    dcOmitted       ## path drop / halt / prune: modelled ⊆ real
    dcNoAnswer      ## Z3 unknown / walker fault: no modelled program exists

  SymexProgram* = object
    ## Defined here (after `SymexErrorInfo`) so `parseErrors` can name it;
    ## the other fields' types (`IRParam`/`IRStmt`/`ProcSig`) are declared in
    ## the IR `type` section above.
    params*: seq[IRParam]
    body*: IRStmt
    procs*: Table[string, ProcSig]   ## transitively reachable callees
    userExnHierarchy*: Table[string, string]
                                     ## Phase 15 E4a: child -> direct-parent
                                     ## links for USER-defined exception types
                                     ## the SUT raises/catches, captured at
                                     ## parse time via `getImpl` ancestor walks
                                     ## up to a known stdlib base. Empty when
                                     ## the SUT uses only stdlib exn types.
    parseErrors*: seq[SymexErrorInfo]
                                     ## Phase 15 G1c. Errors discovered during
                                     ## parse-time monomorphization (currently
                                     ## `geInstantiationCapped` when a generic
                                     ## proc exceeds `maxInstantiationsPerProc`).
                                     ## `runSymex` drains these into the
                                     ## `RawResult.errors` so a `sevError` here
                                     ## forces `sxUnknown` (Invariant 3).
    annotationViolations*: seq[AnnotationViolation]
                                     ## RFC-0005 S8 (§13.3, i3). Parse-time
                                     ## findings that a user annotation's
                                     ## promise is false at a call site.
                                     ## Verdict-neutral: `runSymex` copies
                                     ## them onto every `RawResult` and reads
                                     ## them for nothing else.

  CallStat* = object
    name*:      string
    walked*:    int   ## times this callee's body was actually walked
    cacheHits*: int   ## times the call was served from the summary cache

  CallStats* = seq[CallStat]

  HeapSnapshotEntry* = object
    ## Phase 15 R12 (ADR-0010, docs/symex/witness-format-v3.md); Cluster H
    ## H_witness (ADR-0022) extends this to the FULL reachable heap graph
    ## (ADR-0010 invariant #4). One entry per ref/ptr-typed SUT PARAM, PLUS one
    ## per REACHABLE non-param cell the model pins (an object field, or a
    ## container element) — in a SAT/raised witness. Rendered under
    ## `renderAsChoicesVersion` `"7"`. The struct SHAPE is unchanged from R12;
    ## H_witness only widens which cells get an entry and what `pointsTo` can
    ## contain for a composite (object) cell.
    ##
    ## The snapshot records, for each cell, what the LOGICAL HEAP committed to
    ## in the SAT model: the abstract address it bound to (`value`), the
    ## modelled pointee rendering (`pointsTo`), and the alias group it belongs
    ## to. Refs that share a `Ref_T` address render as the SAME cell: the
    ## FIRST-DISCOVERED name for an address is the PRIMARY and carries
    ## `pointsTo`; every other cell aliasing the same address carries
    ## `aliasRef = <primary>` (and no `pointsTo`). For param-vs-param aliasing
    ## "first-discovered" is the lexicographically-first PARAM NAME (R12,
    ## unchanged); a reachable (non-param) cell that turns out to alias an
    ## earlier param OR an earlier reachable cell (including a CYCLE back to
    ## an ancestor) is discovered in depth-first traversal order. A nil ref has
    ## `value == "nil"` and `pointsTo == none`.
    ##
    ## Cell naming: a param keeps its bare name (unchanged). A reachable cell
    ## is named by its ACCESS PATH from the param that reached it first: a
    ## field hop appends `.<field>` (`p.next`, `p.next.next`); a container
    ## index appends `[<i>]` (`s[0]`, `arr[1]`).
    ##
    ## `pointsTo` for a COMPOSITE (object) cell is a structural rendering
    ## `"{f1=v1, f2=v2}"`: a primitive field renders its stringified value; a
    ## nil ref/ptr field renders inline as `"nil"`; a non-nil ref/ptr field
    ## renders `"@<cellName>"` — look up that name in this same `seq` (it may
    ## itself be a param, a fresh cell, or an alias entry); a field whose
    ## heap array was never materialised on the winning path (never touched by
    ## the SUT) renders `"<unobserved>"` (Invariant 3 — never fabricate); a
    ## field one hop beyond the effective heap-depth budget renders
    ## `"<max-heap-depth>"` (the hop is never taken); a field of a
    ## container/variant/nested-by-value-object type (not yet witness-
    ## renderable through the field-split heap) renders `"<unsupported>"` — a
    ## documented ceiling, not a crash or a guess. A non-object (primitive)
    ## pointee's `pointsTo` is just the stringified value, as in R12.
    name*:     string          ## the param name, or a reachable cell's access
                               ## path (declaration/discovery order preserved
                               ## by the surrounding `seq`)
    sort*:     string          ## the `Ref_<typeId>` / `ptr`-family sort name
    value*:    string          ## "nil", or the model rendering of the address
    pointsTo*: Option[string]  ## the modelled pointee value rendering; `none`
                               ## for a nil ref or a non-primary alias member
    aliasRef*: Option[string]  ## `some(primary)` when this cell aliases an
                               ## earlier cell's address; `none` otherwise

  DefectFinding*[T] = object
    ## ADR-0012 D2. One non-winning sxRaised path discovered during a
    ## symexFind run — an incidentally found defect or exception raise.
    ## Also the element type of `allRaiseFindings` (which unions the winning
    ## raise with the diagnostics channel). `isDefect` distinguishes stdlib
    ## Defect subtypes from ordinary Exception subtypes.
    raisedTypeId*: string
    defectKind*:   DefectKind
    isDefect*:     bool
    raisedMsg*:    Option[string]
    witness*:      T
    heapSnapshot*: seq[HeapSnapshotEntry]

  SymexResult*[T] = object
    abstractions*: AbstractionLog
    obligations*:  ObligationLog
      ## Issue #161 slice 2. Every signed-overflow proof obligation raised
      ## during THIS run, and whether it was discharged by the static
      ## interval analysis or handed to the solver. The audit trail for
      ## the ADR-0001 amendment: a verifier that silently chooses which
      ## obligations to prove itself is not one you can check. Empty when
      ## `fromCache` — like `abstractions`, this records an exploration
      ## that did not happen.
    callStats*:    CallStats   ## per-callee walk + cache-hit counts
    heapSnapshot*: seq[HeapSnapshotEntry]
      ## Phase 15 R12. The heap-snapshot witness (one entry per ref/ptr param)
      ## on a SAT/raised result. EMPTY (the `heapSnapshot` key ABSENT, not null)
      ## for a SUT with no ref/ptr params — every prior cluster's witness is
      ## unchanged (backward compat). See `HeapSnapshotEntry` and
      ## docs/symex/witness-format-v3.md.
    errors*:       seq[SymexErrorInfo]
      ## Phase 15 F6. Classified errors surfaced during the run. On an
      ## `sxUnknown` verdict caused by an unsupported op, `errors[0].kind`
      ## is `feUnsupportedOp` (Invariant 3 — never a silent UNSAT).
    annotationViolations*: seq[AnnotationViolation]
      ## RFC-0005 S8 (§13.3, i3). Every call site where a user annotation's
      ## promise (today: `{.symexTransparent.}`) was found false. Loud and
      ## verdict-NEUTRAL: it never changes `status`, and a call it names is
      ## still tainted through its own `feOpaqueCallUnmodelled` entry in
      ## `errors`. Empty when `fromCache`.
    fromCache*:    bool
      ## Phase 14 cycle C1. `true` iff this result was served from
      ## the verdict cache (`:unsat`/`:unk` suffix) or the witness
      ## cache (`:sat` suffix) without re-running `runSymex`. When
      ## true, `abstractions` and `callStats` are `@[]` — those
      ## fields record THIS run's exploration, which didn't happen.
    diagnostics*:  seq[DefectFinding[T]]
      ## ADR-0012 D2. Incidentally-discovered defect/exception raises found
      ## while searching for the primary target. Populated by the reduction
      ## in `runSymex`: every non-winning `sxRaised` in `w.found` becomes a
      ## `DefectFinding[T]` here. Best-effort, not exhaustive (the walk may
      ## stop on the first `sxSat` before all paths are explored). Always
      ## empty for `sxUnsat`/`sxUnknown` results.
    case status*: SymexStatusKind
    of sxSat:
      witness*: T
    of sxUnsat, sxUnknown:
      discard
    of sxRaised:
      raisedTypeId*: string   ## Phase 15 E2a. Qualified raised exception type.
      raisedWitness*: T        ## Phase 15 E2b. The reconstructed SUT input that
                               ## reaches the raise (satisfies the raise-path
                               ## condition). Distinct name from the `sxSat`
                               ## `witness` field (Nim forbids a repeated field
                               ## name across variant branches).

  IntegerSemantics* = enum
    isExact      ## BV[W] always. Phase 1 default.
    isOptimised  ## BV[W] + selective Z3Int abstraction (Phase 2 lands this).
    isLoose      ## Z3Int everywhere, unsound. Research-only.

  ResourceBudget* = object
    ## CR-9(b): caps on walker resource usage, consolidated out of
    ## SymexSettings. 0 = unlimited for every field EXCEPT `maxCallDepth`,
    ## `maxLoopUnwind`, and `seqInlineThreshold` (documented once here;
    ## per-field notes give the default value and what happens when the
    ## limit is reached).
    ##
    ## RFC-0010 B4: this promise was FALSE for four fields (`maxCallDepth`,
    ## `maxLoopUnwind`, `maxClosureInlineCount`, `maxBytesEncodingLen`) as
    ## originally written — each enforcement site was missing the
    ## `cap > 0 and` guard `maxFrontierSize`/`maxSplitParts` already used, so
    ## an explicit 0 exhausted the budget on the very FIRST use instead of
    ## behaving as unlimited. Two of the four are fixed and now genuinely
    ## honour 0 = unlimited: `maxClosureInlineCount` (`runtime.nim`'s
    ## `applyClosureGround`) and `maxBytesEncodingLen`
    ## (`runtime_strings.nim`). A guard for `maxCallDepth` was added in the
    ## same round and then REVERTED in round 2 — see below; it traded a
    ## bounded-but-useless `sxUnknown` for a native-stack-exhaustion SIGSEGV.
    ##
    ## THREE fields are DELIBERATE, DOCUMENTED exceptions — not bugs, and
    ## nothing in this slice changes their runtime behavior. All three share
    ## one reason: the walker cannot survive unbounded descent along that
    ## axis, whether the descent is a Z3-level unroll or the host process's
    ## own native call stack.
    ##
    ## `maxCallDepth` (RFC-0010 B4 round 2): `isCall`'s depth check
    ## (`runtime.nim`) is implemented as ordinary native recursion in
    ## `walk` — one native stack frame per SUT call-stack level. A cap of 0
    ## disabling the check does not make the search "unlimited," it removes
    ## the only thing standing between the walker and the host's native
    ## stack limit. `w.activeCalls` does NOT rescue this: it only
    ## cycle-breaks recursion whose argument shape is IDENTICAL across
    ## levels (`argShapeKey`/`symValHash` hash the Z3 AST), so ordinary
    ## linear recursion like `f(n) = if n > 0: f(n-1) + 1 else: 0` produces a
    ## syntactically distinct AST at every level and is never caught. Two
    ## independent reviewers reproduced a SIGSEGV (native stack exhausted in
    ## under a second) against exactly this shape under `maxCallDepth: 0`.
    ## A crash is worse than the `sxUnknown` the guard traded it for: it
    ## takes the whole test BINARY down, not just one query, and violates
    ## this engine's Invariant 3 (never hang, always classify) more severely
    ## than an over-eager decline does. So `maxCallDepth: 0` exhausts
    ## immediately, by design, same as any other implausibly-tight budget —
    ## a caller wanting deep analysis writes an explicit bound sized to the
    ## SUT's real maximum call depth instead, which works and is honest.
    ## Measured directly (this engine's Linux/podman debug build, 8MB
    ## `ulimit -s`): unconstrained linear recursion is safe through a cap of
    ## 85 and SIGSEGVs by 88 — a "large-looking" round number like `1000` is
    ## NOT automatically safe, because the cap bounds NATIVE recursion depth,
    ## and this walker's per-level native stack cost turns out to be large
    ## (roughly 8MB / ~86 levels here). Pick a bound close to the depth you
    ## actually need, not an oversized safety margin, and treat the exact
    ## ceiling as build/platform-dependent rather than a fixed constant.
    ##
    ## `maxLoopUnwind` cannot honour 0 = unlimited without reopening a walker
    ## hang: `isWhile`'s wmExplore k-unroll forks BOTH the continue and exit
    ## branch at EVERY iteration with no per-iteration feasibility check (a
    ## deliberate architecture choice, see `symexWalkerVersion`'s N20 note in
    ## `canonicalize.nim`), so the active-path set never shrinks on its own
    ## for an ordinary loop body — `unwind = 0` read as "no bound" would not
    ## terminate for essentially ANY while loop reaching that arm, violating
    ## this engine's Invariant 3 (never hang, always classify). The
    ## concrete-replay counterpart (`walkWhileFollowConcrete`) is no safer in
    ## principle: its own pre-existing doc comment already says the bound is
    ## kept as a backstop specifically because a malformed/adversarial
    ## `concreteEq` must not hang the walker either. So `maxLoopUnwind`
    ## keeps its own, already-documented ">= 1" contract (below) instead —
    ## an explicit 0 there exhausts immediately, exactly like any other
    ## implausibly-tight budget, not unlimited.
    ##
    ## `seqInlineThreshold` was never actually covered by the promise at all
    ## (an audit gap this slice found and closes here, not a runtime defect —
    ## see its own field doc below for the full mechanism). It selects between
    ## two equally-sound modeling strategies rather than gating an exhaustion
    ## decline, so `0` means the SEMANTIC OPPOSITE of unlimited: "always
    ## axiomatize, never inline."
    queryRLimit*: uint
      ## Z3 logical step count bound. `0` (default) is unbounded.
      ## Wired into `runtime.nim:trySolve` via `Z3_solver_set_params`.
      ## Phase 13.
    maxFrontierSize*: int = 0
      ## Issue #163 item 3 (rev). The one INCREMENTAL per-statement frontier
      ## cap — `walkBlock` (`runtime.nim`) prunes the post-step path
      ## frontier down to this many paths (highest-uncertainty-first
      ## eviction) whenever it grows past the cap, tainting the evicted
      ## paths' contribution as `sxUnknown` via the classified
      ## `beBudgetExhaustedPrune` kind (RFC-0005 S6a; `beBudgetExhausted`
      ## before it) (Invariant 3 — an honest degrade, never a
      ## silent truncation that could fake an `sxSat`/`sxUnsat`). `0` STAYS
      ## the documented opt-out meaning UNLIMITED (this field is in the
      ## `ResourceBudget` majority `0 = unlimited` covers, unlike
      ## `maxCallDepth`/`maxLoopUnwind` — see the type's own umbrella
      ## comment) — this only changes what an OMITTED field gets.
      ##
      ## Before this, the omitted-field default was Nim's bare zero —
      ## unbounded — with no cap at all on multiplicative path growth. This
      ## matters more since finding R22 added a `RangeDefect` fork at ranged
      ## assignments: a ranged loop counter can now fork per iteration
      ## whenever its `ziIvl` discharge is defeated by an unconstrained RHS
      ## operand, and `maxLoopUnwind`/`maxCallDepth` bound other axes but
      ## nothing bounded this one.
      ##
      ## `256` is MEASURED, not guessed (2026-09-18, this engine's Linux/
      ## podman debug build, `walkBlock` instrumented with a temporary
      ## max-frontier-seen counter in a throwaway `git worktree`, never
      ## committed): the LARGEST post-step frontier any of ~20 sampled
      ## heavy/branchy existing suites reached — including every suite this
      ## round's own regression list calls "large"
      ## (`tsymex_161_overflow_obligation`, `tsymex_162_range_base_width`,
      ## `tsymex_163rev_assign_rangedefect`), plus the dedicated frontier-
      ## pruning suite, several deep-nested-if/while/case suites, and every
      ## variant/multivariant/container suite sampled — was **16**
      ## (`tsymex_r6_n9_variant_budget.nim`). `256` is 16x that measured
      ## ceiling: comfortably clear of anything a currently-green, currently-
      ## TERMINATING analysis in this codebase actually reaches, while still
      ## bounding a runaway multiplicative blow-up to a small constant
      ## instead of letting it run unchecked (the R22 concern this field
      ## exists for). Also matches an existing precedent value already
      ## chosen by a test author in this exact codebase for this exact field
      ## (`tsymex_phase7_assertcovered.nim`'s `lax` config), rather than an
      ## arbitrary round number invented fresh.
      ##
      ## One sampled suite (`tsymex_snd3_loopdegrade.nim`) did not terminate
      ## within a 300s bound even at HEAD, with no frontier cap at all
      ## (confirmed independently of this instrumentation) — a pre-existing,
      ## out-of-scope non-termination this change does not need to fix, but
      ## also cannot regress: it was not passing before, so a `256` cap
      ## converting its eventual fate to an honest, fast `sxUnknown` (should
      ## its frontier ever exceed 256) would be a strict improvement, not a
      ## truncation of anything that used to pass.
    maxCallDepth*: int = 3
      ## Upper bound on symbolic call-stack depth explored by `isCall`'s
      ## walker arm (`runtime.nim`) before bailing with a fresh
      ## unconstrained return value. Default `3`. `0` does NOT mean
      ## unlimited (RFC-0010 B4 round 2 — REVERTED from an earlier `0 =
      ## unlimited` claim; see the type's own umbrella comment above for the
      ## full rationale). The check is ordinary native recursion in `walk`,
      ## so disabling it lets ordinary linear recursion (not just a
      ## pathological shape) exhaust the native stack and SIGSEGV the whole
      ## process — `w.activeCalls` only cycle-breaks recursion with
      ## IDENTICAL argument shapes and does not catch this. An explicit `0`
      ## here exhausts on the very first call, same as any other
      ## implausibly-tight budget. A caller who wants deep analysis should
      ## write an explicit bound sized to the SUT's real maximum call depth
      ## instead. Do not assume a "large-looking" round number is
      ## automatically safe: this cap bounds NATIVE recursion depth, and
      ## measured directly (this engine's Linux/podman debug build, 8MB
      ## `ulimit -s`) unconstrained linear recursion is safe through a cap
      ## of 85 and SIGSEGVs by 88 — `maxCallDepth: 1000` itself crashes.
      ## Pick a bound close to the depth actually needed and verify
      ## empirically before raising it substantially; the exact ceiling is
      ## build/platform-dependent, not a fixed constant.
    maxLoopUnwind*: int = 5
      ## Phase-6 loop unrolling cap; >= 1 — one of the ResourceBudget fields
      ## `0` does NOT mean unlimited for (RFC-0010 B4; see the type's own
      ## umbrella comment above for the full hang-safety rationale). Default
      ## 5 (`defaultSymexSettings`).
      ##
      ## This is an INTENTIONAL decidability boundary, not a bug surface
      ## (chapulin round-3/4 doc note): a loop whose trip count is bounded
      ## by a SYMBOLIC quantity cannot be decided by ANY finite unroll —
      ## chapulin's own bisect of its dependent-scan shapes confirmed
      ## unwind 2 vs 5 give the identical `sxUnknown` (it is decidability,
      ## not budget). Raising this helps only loops whose REAL trip count
      ## is a small concrete number above the default. Exhaustion is
      ## always classified (`beBudgetExhausted`, v64 — never a bare
      ## sxUnknown) with the configured bound in the message, and the cap
      ## is per-call: pass a `SymexSettings` with a different value to
      ## `symexFind`. The structural levers for symbolic trip counts are
      ## the closed-form lifts (Q1's scan-to-indexOf, ADR-0025; strip's
      ## decomposition, ADR-0026), not a larger k.
    maxHeapDepth*: int = 8
      ## Phase 15 Cluster R (R1a, ADR-0010). Upper bound on the recursive
      ## `ref object` field-expansion / heap-read (`isDeref`) hop count per
      ## path. Default `8`. `0` means unlimited. When a `p[]` deref would
      ## push `path.heapDepth` past this bound the walker halts with
      ## `sxUnknown` + `SymexErrorInfo{kind: heDepthExhausted}` (R9).
    maxFreshnessAssertions*: int = 256
      ## Phase 15 Cluster R (R2, ADR-0010). Upper bound on the number of
      ## fresh-ref distinctness inequalities (`newRef != prior`) the walker
      ## will emit on a SINGLE path. Default `256`. `0` means unlimited.
      ## SOUND over-approximation (heFreshnessCapExceeded hint).
    maxClosureInlineCount*: int = 64
      ## Phase 15 C2b (ADR-0009 D6). Per-call-stack cap on nested closure
      ## descent. Default `64`. `0` means unlimited.
      ## ceInlineBudgetExceeded (sevError) when exceeded.
      ## R2-10: unlike `maxCallDepth`, this guard has no independent
      ## cycle-breaker behind it (`w.activeCalls` cycle-breaks identical
      ## argument shapes, but closure descent has nothing analogous) — the
      ## `cap > 0 and` check IS the only thing stopping unbounded descent.
      ## `0` is safe today only because a forward-declared self-referencing
      ## closure is declined with `ceClosureUnknownCallee` before it can
      ## recurse — i.e. closure self-recursion is not representable in the
      ## DSL's symex model. Latent, not live: reopen this if that ever
      ## changes.
    maxInstantiationsPerProc*: int = 64
      ## Phase 15 G1c (ADR-0008 D7 / OQ5). Per-base-proc cap on DISTINCT
      ## generic instantiations the parser will register. Default `64`.
      ## `0` means unlimited. geInstantiationCapped (sevError) when exceeded.
    maxVariantConstructorForks*: int = 8
      ## Round-6 A3 (ADR-0029). Structural cap on the number of tags
      ## `isVariantConstructSym` will fork per symbolic-discriminant variant
      ## CONSTRUCTION — checked against `vcsTagSet.len` (parse-time
      ## `case`-branch-narrowed, or the full declared non-else arm count)
      ## BEFORE any solver work, mirroring `maxSplitParts`'s structural-cap
      ## style. Default `8`. `0` means unlimited. Exceeding it classifies a
      ## `beBudgetExhaustedUnmodelled` decline (RFC-0005 S6a; sxUnknown) —
      ## never a crash, never an
      ## unbounded fork explosion for a wide unconstrained enum.
    maxVariantConstructorFieldAllocs*: int = 64
      ## N9 (round-6 review remediation, ADR-0029 companion), unit corrected
      ## by D2 (round-6 review remediation). Structural cap on TOTAL per-fork
      ## LEAF Z3 ALLOCATIONS `isVariantConstructSym` will perform:
      ## `vcsTagSet.len` (the fork count `maxVariantConstructorForks` already
      ## bounds) times the sum of `allocCostOf(ft)` (`smt/types.nim`) over
      ## every field type `ft` across EVERY declared arm of `vcsVariantTy`
      ## (every fork allocates FRESH fields for ALL arms, not just the
      ## fork's own tag — see `isVariantConstructSym`'s own doc comment).
      ## The unit is LEAF ALLOCATIONS, not flat field COUNT: `allocCostOf`
      ## mirrors `allocateSym`'s own recursion, so a composite field type
      ## (`array[N, T]`, nested tuple/variant) contributes its true
      ## allocation cost (e.g. `array[1_000_000, int]` costs 1,000,000, not
      ## `1`) — D2's fix for the gap N9 left open, where a flat field COUNT
      ## bounded the number of fields but nothing bounded what each field
      ## itself cost to allocate. `maxVariantConstructorForks` alone only
      ## bounds the OUTER fork count; it does nothing to bound a wide or
      ## deeply-composite variant, letting per-fork allocation amplify
      ## unboundedly (forks x total-arm-leaf-allocations) even when the fork
      ## count itself is comfortably under budget. Checked BEFORE any solver
      ## work, same structural-cap style as `maxVariantConstructorForks`.
      ## Default `64` (unchanged by D2 — the unit changed from "fields" to
      ## "leaf allocations", which is the honest unit; a composite-fielded
      ## shape that previously passed at exactly 64 flat fields may now
      ## exceed 64 leaf allocations and decline — the intended behavior
      ## change). `0` means unlimited. Exceeding it classifies the SAME
      ## `beBudgetExhaustedUnmodelled` decline kind (RFC-0005 S6a; never a
      ## parallel mechanism) —
      ## never a crash, never unbounded allocation work for a wide- or
      ## deeply-fielded variant.
    maxSplitParts*: int = 8
      ## Phase 15 S5. Upper bound on the number of parts a symbolic
      ## `string.split` decomposition may produce. Default `8`. `0` means
      ## unlimited.
    maxBytesEncodingLen*: int = 32
      ## Phase 15 S7a. Upper bound on the concrete byte/char count a
      ## `bytes(s)` byte-view may materialise. Default `32`. `0` means
      ## unlimited (RFC-0010 B4).
      ## seBytesLengthTooLarge (sxUnknown) when exceeded.
    seqInlineThreshold*: int = 8
      ## Phase 15 C4 (net-new, ADR-0009). Upper bound on CONCRETE seq
      ## length a DSL HOF will UNROLL inline. Default `8`. A concrete
      ## length above this bound — or a SYMBOLIC length — takes the
      ## axiom path. Ignored when `inlinePolicy` is not `ipHybrid`.
      ##
      ## RFC-0010 B4: one of the three fields the umbrella "0 = unlimited"
      ## promise does not reach (see that comment for the full list) — and
      ## the only one of the three for the OPPOSITE reason. The other two are
      ## descent bounds the walker cannot survive removing; this is not an
      ## exhaustion cap at all. It is a strategy-selection threshold between
      ## two equally-sound modeling paths (`lowerHofCall`, `runtime.nim`:
      ## `canInline = lenOpt.isSome and lenOpt.get <= threshold`). `0`
      ## therefore means the SEMANTIC OPPOSITE of unlimited: every concrete
      ## length except an empty seq fails `<= 0`, so `0` selects "always
      ## axiomatize, never inline," not "inline without bound" (a zero-length
      ## seq satisfies `0 <= 0` and inlines, which is a no-op either way).
      ## Exceeding the threshold is not a decline (never
      ## `beBudgetExhausted`, never `sxUnknown` on its own) — it is a normal,
      ## sound path switch, so there is no exhaustion behavior to fix here.

  SymexSettings* = object
    integerSemantics*: IntegerSemantics = isOptimised
    budget*: ResourceBudget
      ## CR-9(b): all resource caps consolidated into one sub-object.
      ## No initializer on purpose (RFC-0010): a nested object field picks up
      ## its own type's declared field defaults recursively, so
      ## `SymexSettings().budget == ResourceBudget()` without restating them.
    acceptUnknownAsCovered*: bool
      ## Phase 7. When `assertCoveredBy` receives `sxUnknown` from the
      ## solver (timeout, unwind exhaustion, opaque-call uncertainty),
      ## the default is to raise — we cannot *prove* coverage. Setting
      ## this to `true` downgrades UNKNOWN to a soft pass for
      ## environments that treat UNKNOWN as "best-effort attempted".
    defectExclusions*: set[DefectKind] =
        {dkOutOfMemoryDefect, dkStackOverflowDefect}
      ## Phase 15 Z3. Defect families the walker must NOT model as
      ## raise-paths. Default excludes OOM + stack-overflow (modelling
      ## those yields spurious sxRaised for virtually all real SUTs).
    arithChecks*: set[ArithCheck] = {acOverflow, acDivByZero, acRange}
      ## R16-1 (Phase 16 ADR-0011 F2). Which arithmetic defect forks to EMIT.
      ## Default all-on `{acOverflow, acDivByZero, acRange}` (debug-like; finds
      ## bugs). Empty = release-like (wrap/unchecked). Orthogonal to
      ## `defectExclusions`: `arithChecks` gates fork emission (2^N cost lever);
      ## `defectExclusions` gates finding surfacing after the fork. In cache key.
    inlinePolicy*: InlinePolicy = ipHybrid
      ## Phase 15 Z3. Call-summary strategy (Cluster C owns the axiom
      ## construction; the type/field live here). Default `ipHybrid`.
    replay*: bool = true
      ## RFC-0005 S10 (§2.3 rule 3). When a run's only SAT lies on a
      ## replay-eligible `scSpurious` path, the entry macro EXECUTES `fn` on
      ## the solver's witness and reports `sxSat`/`sxRaised` only if the real
      ## run reaches the target. On by default, which is a contract change:
      ## `fn` and everything it calls must LINK and LOAD in the calling
      ## binary (an `importc` with no definition, or a `dynlib` the host
      ## lacks, now fails the build or the start-up), and its side effects
      ## happen for real at verdict time. `replay = false` opts out: the
      ## macro emits no reference to `fn`, and a candidate stays `sxUnknown`
      ## as before S10. Static at every entry macro. In the cache key.

# ---- RFC-0005 S1: the channel algebra (§2.2) -------------------------------

func classOf*(k: SymexErrorKind): DegradeClass =
  ## RFC-0005 §2.2 / §3.4. THE exhaustive classification -- one word per
  ## kind, and deliberately NO `else` arm: a new `SymexErrorKind` member is a
  ## compile error here until someone writes its row.
  ##
  ## RFC-0005 S1 DEFAULT: every kind maps to `dcNoAnswer` (⊤ on both
  ## coordinates). That is the conservative choice by construction -- ⊤
  ## blocks sxSat on the path and sxUnsat on the run, which is exactly
  ## today's "any degrade forces sxUnknown" behaviour, so the carrier and the
  ## verdict rule can land as behaviour-preserving refactors (RFC §5
  ## sequencing decision 1). An unaudited kind is therefore never wrong in
  ## the unsound direction. Slices S4-S6 reclassify one funnel at a time,
  ## each flipping only its own pins under its own walker bump.
  ##
  ## RFC-0005 S4 (walker v142) audited the `allocDegrade` funnel
  ## (`runtime.nim`, with its `degradeAlloc` pairing helper and
  ## `runtime_heap.nim`'s `heapArmDegrade` wrapper) site by site against
  ## §3.1's substitution rule. Rows marked `S4` below carry the verdict of
  ## that audit; `dcNoAnswer` on an S4-audited row is the audit's answer,
  ## not the unaudited default. The finding: the funnel's name does not
  ## decide the class -- most of its arms FORCE a value (a `tabSize == 0`
  ## Table/HashSet placeholder, a shared-name 2-valued `svBool` standing in
  ## for an arbitrary `itUninterp` type, a concrete BV64 `0` sort filler, a
  ## forwarded operand, a vacuous `true` binding) or DROP behaviour (a heap
  ## arm that skips the nil-deref fork or the write). Exactly one arm
  ## substitutes a fresh unconstrained symbol: `liftHeapValue`'s
  ## unsupported-pointee read, split off as `heUnsupportedPointeeRead`.
  ##
  ## RFC-0005 S5 (walker v143) audited the `degradeStrArm` funnel and the R1
  ## placeholder funnel the same way (rows marked `S5`). `degradeStrArm`
  ## substitutes a fresh per-read symbol of the result sort, but that alone
  ## does not make a kind `dcFreshSymbol`: the declines that raised before
  ## lowering their operands DROPPED the operands' raise forks. S5 moved
  ## the operand lowering ahead of the `bytes`/`replaceAll`/regex-`replace`/
  ## `split` raises and promoted the four kinds whose every site is then
  ## fresh and effect-preserving; the parse-time rune decode split off as
  ## `seRuneDecodeSymbolic` (a forced `0` / dropped loop). The R1 funnel is
  ## NOT fresh (shared placeholder names, dropped `IndexDefect` forks and
  ## operands) -- RFC §3.1's table is corrected by its `seNestedSeqUnsupported`
  ## row below.
  ##
  ## RFC-0005 S6a (walker v144) audited the BUDGET family (rows marked
  ## `S6a`). `beBudgetExhausted` was one kind at six sites spanning three
  ## classes, merged on purpose ("a sibling of the SAME budget family");
  ## §3.2 split it: the k-unroll survivor keeps the kind (`dcFabricated`),
  ## the frontier prune became `beBudgetExhaustedPrune` (`dcOmitted`, a
  ## halt), and the call-depth / variant-constructor bails became
  ## `beBudgetExhaustedUnmodelled` (`dcSubstituted`). Every class the family
  ## maps to carries `scIncomplete` on the run, so NO budget kind can ever
  ## license `sxUnsat`; the slice is verdict-neutral by construction (the
  ## payoff is attribution and S10 replay eligibility).
  ##
  ## RFC-0005 S6b (walker v145) audited `feUnsupportedOp`'s emission sites,
  ## the heap/halt sites, `eeUnknownExnType` and every kind still at the
  ## default (rows marked `S6b`). `feUnsupportedOp` spanned three classes;
  ## §3.2 split it: the majority (a forwarded operand, a vacuous `true`
  ## binding, a dropped write / mutation / OOB fork, a stale variant, a
  ## statement dropped at parse time, an unregistered callee, and the
  ## composite comparisons whose operator the parser resolves BY NAME, so a
  ## user overload's raise is dropped) keeps the kind as `dcSubstituted`;
  ## the fresh-symbol sites became `feUnsupportedOpHavoc` (`dcFreshSymbol`)
  ## and the boundary abort `feUnsupportedOpAborted` (`dcNoAnswer`). Every
  ## halt (`discard w.degrade(...)` + no survivor) became `dcOmitted`. The
  ## two `dcFreshSymbol` rows are the slice's verdict flips: they no longer
  ## carry `scIncomplete` on the run.
  ##
  ## RFC-0005 S7 (walker v146) audited the closure / HOF declines (rows
  ## marked `S7`) -- the precondition for S9 deleting the closure veto. Every
  ## value-substituting site now records through `closureDegrade`, which
  ## joins its path coordinate onto the consuming path as well as the
  ## closure sink the veto reads: `ceUnsupportedHof` and
  ## `ceClosureUnknownCallee` are `dcSubstituted` (the closure is never
  ## applied / the stand-in has a fixed name), `ceClosureBodyUncertain` is
  ## `dcFreshSymbol` (the call result is fresh per occurrence since S7) and
  ## `ceClosureBodyDiverged` is a halt (`dcOmitted`). `ceNotImplemented` and
  ## `feExtractionFailed` stay `dcNoAnswer`: the former's sites are all ⊤ by
  ## construction; the latter is an extraction / witness sink recorded only
  ## on the SAT branch AFTER the verdict, outside `runTaintOf` -- S10's
  ## replay gate owns it.
  ##
  ## STANDING RULE (RFC-0005 §3.2), which no mechanism can check: reusing an
  ## EXISTING kind at a NEW emission site asserts that the new site shares
  ## that kind's substitution class. If it does not, split the kind
  ## (tail-append one sibling for the minority funnel) -- never add a
  ## per-site class parameter.
  case k
  of ekZ3Error: dcNoAnswer
  of ekZ3MemoryError: dcNoAnswer
  of ekZ3InternalError: dcNoAnswer
  of ekZ3SolverError: dcNoAnswer
  of feUnsupportedOp: dcSubstituted
    # S6b (split -> feUnsupportedOpHavoc, feUnsupportedOpAborted): the
    # majority funnel substitutes -- `retBindEq`'s vacuous `true` (also
    # reached from `applyClosureGround`, where `funcApp` correlates), the
    # svClosure / svVariant / svMultiVariant `iteSV` merges (a forwarded
    # operand; `tyOf` is lossy for variants), the dropped `iekSeqSlice` OOB
    # fork, `iekTableSet` write, `insert`/`pop` mutation and variant
    # reassignment, the borrow op forwarding its operand, the composite
    # `==`/`!=`/`<` and `contains` results (fresh, but the parser maps the
    # operator BY NAME: a user overload's raise is dropped), the multi-leaf
    # closure return's Bool range sort, the parse-time Class-A sites (typed
    # zero / dropped statement) and the unregistered-callee arm (fresh
    # retSym, callee effects dropped).
  of feExtractionFailed: dcNoAnswer
  of feConvDomainExcluded: dcNoAnswer
  of seUnsupportedStringOp: dcNoAnswer
    # S5 audited, NOT reclassified: `degradeStrArm`'s fresh symbol is fine,
    # but the kind's sites drop behaviour -- `requireStr` fails in
    # `iekStrAt`/`iekStrToInt` BEFORE the `IndexDefect`/`ValueError` raise
    # fork is deposited, the `iekStrUnsupported` catch-all carries ops whose
    # real counterpart raises (`parseFloat`), `iekStrSubstr`'s bound decline
    # shares ONE name (`__strSubstrBoundDegrade`) across reads, and the
    # `strip` parse site forces `""`. ⊤ until a raise-behaviour split.
  of seUnsupportedRegex: dcNoAnswer
    # S5 audited: a MALFORMED pattern raises `RegexError` in reality (`re`
    # compiles at run time) and the decline drops that raise; `iekStrFindRe`
    # declines without lowering its receiver (its effects dropped). ⊤.
  of seZ3StringIncomplete: dcFreshSymbol
    # S5 (split -> seRuneDecodeSymbolic): the remaining sites are
    # `lowerStrArm`'s join/split declines, each converted by `degradeStrArm`
    # to a fresh per-read symbol of the result sort, AFTER every operand has
    # been lowered (S5 moved the split receiver/separator lowering ahead of
    # the raise: a dropped operand raise fork was an under-approximation).
  of seZ3VersionMissing: dcFreshSymbol
    # S5: `replaceAll` / regex `replace` without the Z3 >= 4.15.5 gates --
    # operands lowered (and the pattern parsed) first, then a fresh per-read
    # `degradeStrArm` symbol. The op is total in Nim, so nothing is dropped.
  of seBytesSymbolicLength: dcFreshSymbol
    # S5: `bytes(s)` over a non-literal -- the receiver is lowered first
    # (S5), then a fresh per-read `seq[uint8]` symbol (a superset: its
    # `len == len(s)` link is lost, never forced).
  of seBytesLengthTooLarge: dcFreshSymbol
    # S5: `bytes(<literal>)` over `maxBytesEncodingLen` -- the receiver is a
    # literal (no effects to drop); a fresh per-read `seq[uint8]` symbol.
  of seByteIndexUnsupported: dcNoAnswer
  of seByteIterUnsupported: dcSubstituted
    # S6b: the one site is a parse-time decline of `for c in s` over a
    # symbolic string -- the loop statement is DROPPED (`mkUnsupported`,
    # its body's effects never happen): a stale env.
  of seUnsupportedTableValType: dcNoAnswer
    # S4 audited: `allocateSym`'s placeholder FORCES `tabSize == 0`
    # (dcSubstituted); the param boundary aborts (dcNoAnswer). ⊤.
  of seUnsupportedSetCharInterop: dcNoAnswer
    # S4 audited: `allocateSym`'s placeholder FORCES `setSize == 0`
    # (dcSubstituted); the param boundary aborts (dcNoAnswer). ⊤.
  of seNestedSeqUnsupported: dcNoAnswer
    # S5 audited, NOT reclassified (RFC §3.1's "R1 placeholder funnel =
    # fresh symbol" does not survive the audit): `iekSeqLen`'s decline
    # names every occurrence `__seqLenPlaceholderDecline` (reads correlate),
    # the `isIndex` decline continues with the destination UNBOUND and no
    # `IndexDefect` fork, `iekSeqSlice`/`.add`/`.del` return the flagged
    # receiver without lowering their bound/argument operands, `iteSV`
    # forwards one operand, the HOF inline arms share fixed names, and the
    # parse site drops a statement. ⊤.
  of seParseIntPreE: dcNoAnswer
  of eeUninterpRefExtraction: dcNoAnswer
  of eeRaiseUnimplemented: dcNoAnswer
  of eeTryUnimplemented: dcNoAnswer
  of eeRaiseOutsideHandler: dcOmitted
    # S6b: the live site (`isRaise`, a bare `raise` with no in-flight
    # exception and no handler) is a HALT -- the token is discarded and the
    # path returns no survivor, where reality raises `ReraiseDefect` (a
    # caller's handler could catch it): a pure omission. The `runSymex`
    # boundary arm that also names this kind is dead (nothing raises
    # `SymexRaiseOutsideHandlerError` since round-6 N37).
  of eeNotInHandler: dcNoAnswer
  of eeUnknownExnType: dcSubstituted
    # S6b (RFC §3.1's round-2 row): an unknown raised type is matched only
    # by a bare `except:` -- where reality's subtype match would catch, the
    # walker skips the named handler (fabricating the continuation past it
    # and dropping the handler's), and at the SUT boundary its defect-ness
    # and the `stkRaisedExn` filter are guessed. Behaviour substitution,
    # recorded at `sevWarning`: the ONE warning `runTaintOf` counts (see its
    # severity carve-out). `routeRaise` records it through `degrade` and
    # joins the token onto the path wherever the guess is acted on.
  of geInstantiationCapped: dcSubstituted
    # S6b: the over-cap instantiation is never registered; the walker's
    # missing-callee arm binds a fresh `retSym` and drops the callee's
    # var-param / heap writes and raises (its actuals are never lowered).
  of geConceptViolation: dcNoAnswer
  of geUnresolvedGeneric: dcNoAnswer
  of geDistinctBijectivitySkipped: dcNoAnswer
  of geDistinctBarrier: dcSubstituted
    # S6b: as geInstantiationCapped -- the declined callee key reaches the
    # same missing-callee arm (fresh retSym, callee effects dropped).
  of ceNotImplemented: dcNoAnswer
    # S7 audited: every site is ⊤ on both coordinates by construction -- the
    # parse-time closure-iterator `mkUnsupported` marker (the walker's
    # `isUnsupported` arm), the extraction sink's closure-typed SUT result,
    # and the `runSymex` boundary abort. None is a value substitution the
    # veto alone guards: the marker taints its reaching path ⊤ itself.
  of ceUnsupportedCapture: dcNoAnswer
  of ceUnsupportedHof: dcSubstituted
    # S7: all four `lowerHofCall` axiom-path declines (symbolic-length
    # `filter`, capturing / non-int `map`, the `mapArray` map whose function
    # symbol no axiom constrains, `fold`) stand a value in for a closure that
    # is NEVER applied -- its raises and captured writes are dropped, so the
    # stand-in is not a fresh symbol. Recorded through `closureDegrade`, which
    # joins the ⊤ path coordinate onto the consuming path.
  of ceClosureUnknownCallee: dcSubstituted
    # S7: both sites (unresolved callee in `lowerClosureCall`, unstashed body
    # in `applyClosureGround`) return a FIXED-name `int64` stand-in whatever
    # the closure's return type, and the unresolved-callee site returns
    # before lowering the call's arguments (their raises are dropped).
  of ceInlineBudgetExceeded: dcSubstituted
    # S6a: both sites (`applyClosureGround`'s inline-budget guard and its
    # no-walk-context guard) return the closure's uninterpreted `funcApp`
    # WITHOUT descending the body: its captured-variable writes and raises
    # are dropped (a stale env) and equal arguments correlate where the real
    # closure need not. Not a fresh symbol -- substituted. Same sites, same
    # class: no split.
  of heDepthExhausted: dcOmitted
    # S6b: `heapDepthExhausted` is the one emission site; all four callers
    # (`isDeref` x2, `isDerefWrite` x2) `continue` past the path on a true
    # return -- a HALT (token discarded, no survivor), a pure omission. Its
    # `dsHeapDepth` sink is drained into `exnWarnings`, so the run
    # coordinate `{scIncomplete}` reaches `runTaint`.
  of heUnsafeCast: dcOmitted
    # S6b: recorded at parse time (the `cast[ptr T]`/`addr` binding); the
    # walker's `isUnsafeCast` arm returns `@[]` -- every path through the
    # binding is dropped, nothing is bound in its place.
  of hePtrArith: dcSubstituted
    # S6b: parse-time `mkUnsupported` for `inc`/`dec` on a pointer -- the
    # statement is dropped, so the pointer keeps its stale value.
  of hePtrFamily: dcNoAnswer
  of heFreshnessCapExceeded: dcNoAnswer
  of heUnsupportedVarRef: dcNoAnswer
  of heRefVariantUnsupported: dcNoAnswer
    # S4 audited (reaches `allocDegrade` via `heapArmDegrade`): the
    # multi-variant field READ forks every path to a placeholder BEFORE
    # `nilDerefFork` (a dropped NilAccessDefect branch) and the field WRITE
    # drops the write -- dcSubstituted; the boundary arm is dcNoAnswer. ⊤.
  of heUnsupportedOwnership: dcNoAnswer
    # S4 audited: `allocateSym`'s `__ownership:` arm substitutes a
    # `.unalloc` svBool keyed on the allocation's own name (a 2-valued sort
    # lie, shared across repeat allocations: dcSubstituted); the param
    # boundary (`raiseParamAllocIssue`) aborts the run (dcNoAnswer). ⊤ both.
  of heUnresolvedRef: dcNoAnswer
    # S4 audited (split -> heUnsupportedPointeeRead): the remaining sites
    # substitute, they do not havoc -- `walkHeapArm`'s non-ref/ptr-SymVal
    # deref reads bind a placeholder WITHOUT the NilAccessDefect fork (a
    # dropped raise branch), its deref writes DROP the write (stale heap),
    # and `runSymex`'s `SymexRefUnresolvedError` boundary arm aborts the run.
  of geVtableDispatch: dcNoAnswer
  of ceClosureBodyUncertain: dcFreshSymbol
    # S7: the tainted body arm is dropped from the ground axioms, so the
    # call's result -- a fresh constant PER OCCURRENCE since S7 (was a
    # function application shared by every call with equal arguments) -- is
    # free under that arm and fully defined under every other. The arm's
    # operands were lowered before descent, its raises are routed, its heap
    # and defect-survivor facts still merge: nothing is dropped. The arm's
    # own degrade taint joins the calling path through the descent join.
  of weInternalWalkerFault: dcNoAnswer
    # S4 audited: a walker bug is never an approximation (§3.1), including
    # its two `degradeAlloc` seq-element sites. S5: likewise its R1
    # placeholder-funnel sites (`placeholderReadDeclineKind`).
  of beBudgetExhausted: dcFabricated
    # S6a (split -> beBudgetExhaustedPrune, beBudgetExhaustedUnmodelled):
    # the remaining sites are the `maxLoopUnwind` k-unroll exhaustion in
    # BOTH walk modes (`isWhile`'s `wmExplore` arm, `walkWhileFollowConcrete`).
    # Each still-active path is forked onto the POST-loop continuation with
    # the guard still satisfiable on its pc -- a continuation reality never
    # takes there (⊤ on the path) -- and iterations past the bound are never
    # walked (`{scIncomplete}` on the run). The RFC's flagship dcFabricated.
  of feUnsupportedExprKind: dcNoAnswer
    # S4 audited, NOT reclassified: one `degradeAlloc` site (`iekField` on an
    # unsupported receiver) plus the Class-A `mkUnsupported` parse sites,
    # whose typed-zero dummy is §0.2's flagship dcSubstituted example.
  of feUnsupportedParamType: dcNoAnswer
    # S4 audited: signature-scoped (§2.5 item 2) -- dcNoAnswer by the RFC;
    # the in-walk `allocateSym` arm is the same 2-valued `.unalloc` sort lie.
  of feUnsupportedWitnessType: dcNoAnswer
    # S4 audited: as feUnsupportedParamType (signature-scoped, §2.5 item 2).
  of heNewFieldZeroUnsupported: dcFreshSymbol
    # S6b: `isNew`'s zero-write is SKIPPED for a field with no clean zero
    # encoding (seq/table/set/array/variant/distinct/uninterp). The field's
    # cell is then `heap[newRef]` of that field's heap array at the fresh,
    # freshness-asserted `newRef` -- a read of an index no store has
    # touched, i.e. unconstrained; reality's zero value is one of its
    # values. Nothing else is dropped (the other fields are still written,
    # the path is not forked). `dcFreshSymbol`.
  of seUnsupportedTableKeyType: dcNoAnswer
    # S4 audited: `allocateSym`'s placeholder FORCES `tabSize == 0`
    # (dcSubstituted); the param boundary aborts (dcNoAnswer). ⊤.
  of seUnsupportedCompoundSortLeaf: dcSubstituted
    # S4: the ONE site (`rawAnyAstOf`) returns a concrete BV64 `0` as the
    # compound value's ast, and heap stores / closure args consume it as a
    # VALUE -- a forced value, not a havoc. Same coordinates as the default.
  of beBudgetExhaustedAssumedBound: dcFabricated
    # S6a: the `isWhile` k-unroll site's `wHasAssumedBound` branch -- the
    # identical survivor fork as `beBudgetExhausted` (one site, one shape).
  of feOpaqueCallUnmodelled: dcSubstituted
    # S6b (RFC §3.1's round-2 correction): the opaque call's result is a
    # fresh havoc, but the callee's mutations and raises are DROPPED.
  of feEnumOrdinalUnresolved: dcSubstituted
    # S6b: the parser replaces the unresolved enum constant with the literal
    # `0` -- a forced value.
  of feTransparentArgNotInert, feTransparentResultUsed: dcNoAnswer
    # RFC-0005 S8 (§13.3, i3): retired, never emitted -- the report rides
    # the verdict-neutral `AnnotationViolation` channel. The row stays only
    # because `classOf` is total over the (ordinal-stable) enum.
  of feGlobalReadUnmodelled: dcSubstituted
    # S6b: the read returns `__globalReadHavoc_<name>` -- ONE name per
    # global, so two reads correlate where a write between them makes them
    # differ in reality -- at a sort guessed as `tInt(64)` when no prototype
    # is in scope. Correlated / mis-sorted, not fresh.
  of seVariantFieldOnDeclinedCtor: dcOmitted
    # S6b: `isVariantField` on a receiver whose construction already
    # declined is a HALT (`discard w.degrade(...)` + `continue`).
  # RFC-0005 S1b: the minted kinds (classified by S6b).
  of feUnsupportedStmtKind: dcSubstituted
    # S6b: every site is a parse-time Class-B `mkUnsupported` -- the
    # statement is dropped (the walker's `isUnsupported` arm forks the path
    # on unchanged): a stale env.
  of weRecursionCycleCut: dcSubstituted
    # S6b: the cut binds a fresh `_cyc` retSym but does not walk the callee:
    # its var-param / heap writes and raises are dropped.
  of eeHandlerReraiseUnmodelled: dcOmitted
    # S6b: a HALT -- the bare re-raise inside a handler with no in-flight
    # exception returns no survivor (token discarded).
  of ceClosureBodyDiverged: dcOmitted
    # S7: a HALT. Since S7 the caller continuation past a body with no
    # value-bearing exit is infeasible (the exit-coverage fact is `false`),
    # and the body's raises are routed to the caller, so nothing survives
    # past the call to carry a coordinate; the token is discarded. The run
    # keeps `{scIncomplete}` for any body path a budget or halt dropped.
  of weBreakOutsideLoop: dcOmitted
    # S6b: both sites (`isBreak` / `isContinue` outside a loop) are HALTS --
    # the token is discarded and the walk returns `@[]`.
  of beSolverUndef: dcNoAnswer
  # RFC-0005 S4: the one fresh-symbol arm of the `allocDegrade` funnel.
  of heUnsupportedPointeeRead: dcFreshSymbol
  # RFC-0005 S5: the parse-time rune-decode split of seZ3StringIncomplete.
  of seRuneDecodeSymbolic: dcSubstituted
    # `runeLen(s)` is replaced by the literal `0` (a forced value) and the
    # `for r in s.runes` statement is dropped (a stale env) -- both substitute.
  # RFC-0005 S6a: the two minority funnels split off beBudgetExhausted.
  of beBudgetExhaustedPrune: dcOmitted
    # `walkBlock`'s `maxFrontierSize` eviction drops paths and forks none:
    # a pure under-approximation. Its `{}` path coordinate is sound only
    # because the site is a HALT (the token is discarded -- pinned).
  of beBudgetExhaustedUnmodelled: dcSubstituted
    # the `maxCallDepth` bail (fresh havoc retSym, callee var-param/heap
    # writes and raises dropped, actuals never lowered) and the two
    # `isVariantConstructSym` budgets (destination unbound, operands never
    # lowered): stale env + dropped raise forks.
  # RFC-0005 S6b: the two minority funnels split off feUnsupportedOp.
  of feUnsupportedOpHavoc: dcFreshSymbol
    # Fresh per evaluation (`degradeAlloc`'s `freshDegradeName` counter, a
    # uniquified `rawConstOf`, or a `synthZ3`-numbered `retSym`), its init
    # facts discarded or type-only, every operand lowered, nothing forked
    # away and no effect dropped (see the enum member's doc for the sites).
  of feUnsupportedOpAborted: dcNoAnswer
    # The §3.3 boundary abort: the walk never finished, so there is no
    # approximation in either direction -- ⊤, never "promoted" (§3.3).
  # RFC-0005 S10.
  of seParseIntLaxSyntax: dcFreshSymbol
    # The lax half of a `parseInt` raise predicate: the model raises on
    # every `+`-prefixed / `_`-bearing string, reality on a subset -- the
    # raise fork over-approximates and drops nothing (the exact half is
    # forked clean alongside it, the digits survivor is unchanged).
  of feReplayRefuted: dcFreshSymbol
    # A verdict-time diagnostic, never drained into `runTaint` (see the
    # enum member): the refuted witness came from a `dcFreshSymbol`-only
    # path, which is the only taint replay runs on.

func pathTaint*(c: DegradeClass): Taint =
  ## RFC-0005 §2.2. The PATH coordinate a degrade of class `c` joins into the
  ## surviving path's `taint`. Consumed by the SAT rule (`scSpurious`); the
  ## path's `scIncomplete` bit is inert by design (§2.1: uniformity is worth
  ## two idle bits). Its codomain is `{}`, `{scSpurious}` or ⊤ -- closed under
  ## union, so no path ever carries `{scIncomplete}` alone (§2.6).
  case c
  of dcFreshSymbol:                            {scSpurious}
  of dcSubstituted, dcFabricated, dcNoAnswer:  {scSpurious, scIncomplete}
  of dcOmitted:                                {}

func runTaint*(c: DegradeClass): Taint =
  ## RFC-0005 §2.2. The RUN coordinate a drained `sevError` of class `c`
  ## contributes to `runTaint` at drain time. Consumed by the UNSAT rule
  ## (`scIncomplete`); the run's `scSpurious` bit is diagnostics-only (§8.1).
  case c
  of dcFreshSymbol:                            {scSpurious}
  of dcSubstituted, dcNoAnswer:                {scSpurious, scIncomplete}
  of dcFabricated, dcOmitted:                  {scIncomplete}

func channels*(k: SymexErrorKind): tuple[path, run: Taint] =
  ## RFC-0005 §2.2 convenience: both coordinates of kind `k`'s class.
  (pathTaint(classOf(k)), runTaint(classOf(k)))

func taintsRun*(e: SymexErrorInfo): bool =
  ## RFC-0005 §2.2's SEVERITY RULE, as one predicate: does drained entry `e`
  ## contribute to the run coordinate? Every `sevError` does; `sevWarning` /
  ## `sevHint` entries do not (Invariant 7: they never forced sxUnknown) --
  ## with ONE carve-out, landed by S6b per RFC §3.1: `eeUnknownExnType` is a
  ## behaviour substitution (a named handler skipped, a boundary defect-ness
  ## guessed) recorded at `sevWarning` for its consumers, so it taints at
  ## its class's coordinate anyway. `runTaintOf` and `checkUnsatOverTaintOnly`
  ## both read this, so the two can never disagree about which entries count.
  e.severity == sevError or e.kind == eeUnknownExnType

func runTaintOf*(errors: openArray[SymexErrorInfo]): Taint =
  ## RFC-0005 §2.2 "The run coordinate is derived, not written". The union of
  ## `runTaint(classOf(e.kind))` over every entry in `errors` that
  ## `taintsRun` admits (every `sevError`, plus the `eeUnknownExnType`
  ## warning -- the severity rule and its one carve-out). `runSymexImpl`
  ## applies this to the drained sinks (`exnWarnings` ∪ `prog.parseErrors` ∪
  ## `closureErrs`) to produce `WalkCtx.runTaint`; S1b's correspondence pin
  ## and S11's `checkUnsatOverTaintOnly` read the SAME predicate, so
  ## recording and classification have one source of truth.
  for e in errors:
    if taintsRun(e):
      result = result + runTaint(classOf(e.kind))

func siteAnchored*(markerId: int): DeclineScope =
  ## RFC-0005 S8. §2.5 point 1: anchored at the parser-minted marker node
  ## `markerId` (`isUnsupported.unMarker` / `isUnsafeCast.ucMarker`).
  DeclineScope(kind: dskSiteAnchored, markerId: markerId)

func calleeKeyed*(calleeKey: string): DeclineScope =
  ## RFC-0005 S8. §2.5 point 3: anchored at a never-registered `mkCall` key.
  DeclineScope(kind: dskCalleeKey, calleeKey: calleeKey)

func signatureScope*(): DeclineScope =
  ## RFC-0005 S8. §2.5 point 2: the SUT's signature is the unmodellable thing.
  DeclineScope(kind: dskSignature)

func walkSite*(): DeclineScope =
  ## RFC-0005 S8. Recorded by the walker at the site it reached.
  DeclineScope(kind: dskWalkSite)

func `==`*(a, b: DeclineScope): bool =
  ## RFC-0005 S8. Structural equality (the system `==` does not iterate a
  ## case object's branch fields).
  if a.kind != b.kind: return false
  case a.kind
  of dskSiteAnchored: a.markerId == b.markerId
  of dskCalleeKey: a.calleeKey == b.calleeKey
  of dskUnplaced, dskSignature, dskWalkSite: true

func `$`*(s: DeclineScope): string =
  case s.kind
  of dskSiteAnchored: "siteAnchored(" & $s.markerId & ")"
  of dskCalleeKey: "calleeKey(" & s.calleeKey & ")"
  of dskUnplaced: "unplaced"
  of dskSignature: "signature"
  of dskWalkSite: "walkSite"

func `==`*(a, b: SymexErrorInfo): bool =
  ## RFC-0005 S8: spelled out because `scope` is a case object.
  a.kind == b.kind and a.severity == b.severity and a.msg == b.msg and
    a.scope == b.scope

func unplacedDeclines*(errors: openArray[SymexErrorInfo]): seq[SymexErrorInfo] =
  ## RFC-0005 S8 (§2.5 point 4, §6.6). The bucket-4 members of `errors`: every
  ## entry `taintsRun` admits (a decline) whose scope is `dskUnplaced`. The
  ## invariant S9 deletes the blanket vetoes on is that this is empty for
  ## every run; the S8 totality pin enumerates any exception by name.
  for e in errors:
    if taintsRun(e) and e.scope.kind == dskUnplaced:
      result.add e

proc checkUnsatOverTaintOnly*[T](r: SymexResult[T]) =
  ## RFC-0005 §4.3 (landed S4): the checked justification for a pin that
  ## flipped `sxUnknown` -> `sxUnsat`. Asserts `r.status == sxUnsat` AND that
  ## every drained entry `taintsRun` admits (each `sevError`, plus the
  ## `eeUnknownExnType` warning) maps through `classOf` to a class
  ## whose run coordinate lacks `scIncomplete` -- i.e. the run is
  ## over-approximation-only, so the UNSAT is licensed by §0.1 rather than by
  ## a classification slip. Reads `runTaintOf`, the same function the drain
  ## derives `WalkCtx.runTaint` from (one source of truth). Raises an
  ## `AssertionDefect` naming the offending kind(s) otherwise, so a test
  ## calls it as a statement.
  var offending: seq[string]
  for e in r.errors:
    if taintsRun(e) and scIncomplete in runTaint(classOf(e.kind)):
      offending.add $e.kind & " (" & $classOf(e.kind) & ")"
  if r.status != sxUnsat or offending.len > 0:
    raiseAssert "checkUnsatOverTaintOnly: status=" & $r.status &
      " (want sxUnsat); under-approximating sevError kinds: " & $offending

# ---- Constructors -----------------------------------------------------------
#
# Plain constructor procs over the variant types. The parser builds the
# IR at macro time using these (or the generated NimNode equivalent);
# the runtime consumes the IR built by the emitted code at runtime.

proc mkIntLit*(v: int64): IRExpr =
  IRExpr(kind: iekIntLit, ival: v)

proc mkFloatLit*(v: float64, width = 64): IRExpr =   ## Phase 15 F2
  IRExpr(kind: iekFloatLit, fval: v, fwidth: width)
proc mkFloat32Lit*(v: float32): IRExpr =             ## Phase 15 F2
  IRExpr(kind: iekFloatLit, fval: float64(v), fwidth: 32)

proc mkConvIntToFloat*(e: IRExpr, targetWidth = 64): IRExpr =   ## Phase 15 F5
  IRExpr(kind: iekConvIntToFloat, convOperand: e, convWidth: targetWidth)
proc mkConvFloatToInt*(e: IRExpr, targetWidth = 64): IRExpr =   ## Phase 15 F5
  IRExpr(kind: iekConvFloatToInt, convOperand: e, convWidth: targetWidth)

proc mkConvIntWidth*(e: IRExpr, srcWidth: int, srcSigned: bool,
                      tgtWidth: int, tgtSigned: bool): IRExpr =
  ## Round-6 B2: WIDENING-only int-family width conversion. Zero-/sign-
  ## extend is keyed on `srcSigned` (the SOURCE value's own signedness);
  ## `tgtSigned` becomes the resulting SymVal's `signed` flag.
  doAssert tgtWidth > srcWidth,
    "mkConvIntWidth: widening only — src=" & $srcWidth & " tgt=" & $tgtWidth
  IRExpr(kind: iekConvIntWidth, ciwOperand: e, ciwSrcWidth: srcWidth,
         ciwSrcSigned: srcSigned, ciwTgtWidth: tgtWidth, ciwTgtSigned: tgtSigned)

proc mkConvIntReinterpret*(e: IRExpr, width: int, tgtSigned: bool): IRExpr =
  ## A1 adjudication (walker v116): SAME-WIDTH signedness reinterpret (e.g.
  ## `uint(x)` from an `int`). No widening/narrowing — the underlying Z3 BV
  ## bit pattern is unchanged; only the result SymVal's `signed` tag flips to
  ## `tgtSigned`.
  IRExpr(kind: iekConvIntReinterpret, cirOperand: e, cirWidth: width,
         cirTgtSigned: tgtSigned)

proc mkMathCall*(op: string, args: seq[IRExpr]): IRExpr =   ## Phase 15 F6
  IRExpr(kind: iekMathCall, mathOp: op, mathArgs: args)

proc mkBoolLit*(v: bool): IRExpr =
  IRExpr(kind: iekBoolLit, bval: v)

proc mkVar*(name: string): IRExpr =
  IRExpr(kind: iekVar, vname: name)

proc mkBinop*(op: IRBinop, lhs, rhs: IRExpr): IRExpr =
  IRExpr(kind: iekBinop, bop: op, lhs: lhs, rhs: rhs)

proc mkUnop*(op: IRUnop, operand: IRExpr): IRExpr =
  IRExpr(kind: iekUnop, uop: op, operand: operand)

proc mkBorrowOp*(op: IRBinop, lhs, rhs: IRExpr,
                 returnsDistinct: bool, distinctName: string): IRExpr =
  ## Phase 15 G5: a `{.borrow.}`-proc operator on a `distinct T`.
  IRExpr(kind: iekBorrowOp, borrowOp: op, borrowLhs: lhs, borrowRhs: rhs,
         borrowReturnsDistinct: returnsDistinct,
         borrowDistinctName: distinctName)

proc mkLambda*(siteHash: int64, declOrder: int, params: seq[IRParam],
               body: IRStmt, captures: seq[string], retTy: IRType): IRExpr =
  ## Phase 15 Cluster C (C1, ADR-0009). A lambda expression node. `siteHash`/
  ## `declOrder` form the formatting-stable lambda-site key (D3); `params`/
  ## `retTy` are concrete post-monomorphization (D8); `captures` are the
  ## free-variable names snapshotted from the enclosing scope (D2).
  IRExpr(kind: iekLambda, lambdaSite: (siteHash, declOrder),
         lambdaParams: params, lambdaBody: body,
         lambdaCaptures: captures, lambdaRetTy: retTy)

proc mkClosureCall*(callee: string, args: seq[IRExpr]): IRExpr =
  ## Phase 15 Cluster C (C1, ADR-0009 D6). A call through a proc-valued
  ## variable. A-normalised like `isCall`.
  IRExpr(kind: iekClosureCall, ccCallee: callee, ccArgs: args)

proc mkSeqLit*(elems: seq[IRExpr], elemTy: IRType,
               declinedPlaceholder: bool = false): IRExpr =
  ## Phase 15 C4. A concrete seq literal `@[a, b, c]` (incl. empty `@[]`).
  ## `declinedPlaceholder` (Round-6 N15) is set true ONLY by
  ## `declineUnsupportedFieldRead`'s fake empty-seq stand-in — see
  ## `seqLitDeclinedPlaceholder`'s doc comment above.
  IRExpr(kind: iekSeqLit, seqLitElems: elems, seqLitElemTy: elemTy,
         seqLitDeclinedPlaceholder: declinedPlaceholder)

proc mkHofCall*(op: string, sq: IRExpr, closure: IRExpr,
                retElemTy: IRType, init: IRExpr = nil): IRExpr =
  ## Phase 15 C4. A std/sequtils higher-order call (`filter`/`map`/`fold`).
  IRExpr(kind: iekHofCall, hofOp: op, hofSeq: sq, hofClosure: closure,
         hofInit: init, hofRetElemTy: retElemTy)

proc mkNil*(pointee: IRType): IRExpr =
  ## Phase 15 R5 (Cluster R). The `nil` ref/ptr literal in a comparison. `pointee`
  ## is the full `itRef`/`itPtr` type of the ref/ptr `nil` is compared against
  ## (resolved at parse time from the OTHER operand) so the walker can mint the
  ## per-sort `nilConst`.
  IRExpr(kind: iekNil, nilPointee: pointee)

proc mkField*(obj: IRExpr, fieldIx: int, fieldName: string = ""): IRExpr =
  IRExpr(kind: iekField, obj: obj, fieldIx: fieldIx, fieldName: fieldName)

proc mkIndex*(arr, idx: IRExpr): IRExpr =
  IRExpr(kind: iekIndex, arr: arr, idx: idx)

proc mkArrayLit*(elems: seq[IRExpr], elemTy: IRType): IRExpr =
  IRExpr(kind: iekArrayLit, lelems: elems, lelemTy: elemTy)

proc mkTupleLit*(elems: seq[IRExpr], tupleTy: IRType): IRExpr =
  ## RFC-chapulin-hardening P1. `tupleTy` must be an `itTuple` IRType (as
  ## returned by `classifyType` on the tuple-constructor expression node)
  ## whose `fields.len == elems.len`.
  doAssert tupleTy.kind == itTuple, "mkTupleLit: not an itTuple: " & $tupleTy.kind
  doAssert tupleTy.fields.len == elems.len,
    "mkTupleLit: arity mismatch — type has " & $tupleTy.fields.len &
    " fields, got " & $elems.len & " elements"
  IRExpr(kind: iekTupleLit, telems: elems, ttupleTy: tupleTy)

proc mkVariantLit*(ty: IRType, tagOrd: int, tagName: string,
                    armFields: seq[IRExpr],
                    plainFields: seq[IRExpr]): IRExpr =
  ## Round-6 A1 (ADR-0029). `ty` must be the full `itVariant` IRType (as
  ## returned by `classifyType` on the object-constructor node). `tagOrd`
  ## is the literal discriminant's ordinal — the caller has already matched
  ## it against one non-else `VariantArm.tagOrdinal` in `ty.vArms` (else-arm
  ## literal construction is out of A1 scope). `armFields`/`plainFields`
  ## are the ACTIVE arm's and the shared plain fields' constructor exprs,
  ## in `VariantArm.fieldNames`/`ty.vPlainFieldNames` order respectively.
  doAssert ty.kind == itVariant,
    "mkVariantLit: not an itVariant: " & $ty.kind
  doAssert plainFields.len == ty.vPlainFieldNames.len,
    "mkVariantLit: plain-field arity mismatch — type has " &
    $ty.vPlainFieldNames.len & " plain fields, got " & $plainFields.len
  IRExpr(kind: iekVariantLit, vlVariantTy: ty, vlTagOrd: tagOrd,
         vlTagName: tagName, vlArmFields: armFields,
         vlPlainFields: plainFields)

proc mkSeqLen*(obj: IRExpr, loc: string = ""): IRExpr =
  IRExpr(kind: iekSeqLen, lenObj: obj, lenLoc: loc)

proc mkSeqSlice*(base, lo, hi: IRExpr): IRExpr =
  ## v67: seq-slice VALUE (array-lambda view — see `iekSeqSlice`). `hi` is
  ## INCLUSIVE; the parser pre-adjusts `..<` to `hi - 1`.
  IRExpr(kind: iekSeqSlice, ssBase: base, ssLo: lo, ssHi: hi)

proc mkStrLit*(s: string): IRExpr =
  IRExpr(kind: iekStrLit, sval: s)

proc zeroIRExprForType*(ty: IRType): IRExpr =
  ## Cluster H Step C (ADR-0022). The sound ZERO-value IR for a heap pointee
  ## FIELD's type, used by the universal `isNew` zero-write
  ## (`runtime_heap.nim`'s `isNew` walker arm) so every field of a freshly
  ## allocated object reads its Nim zero rather than an unconstrained free
  ## heap cell (a fresh field-split heap array is a FREE Z3 const — an
  ## Invariant-3 false-SAT hole without this). Mirrors `zeroValueForType`
  ## (`dsl_parser.nim`, the PARSE-TIME sibling for omitted `nnkObjConstr`
  ## fields) but additionally handles the two shapes only a heap FIELD can
  ## have: a recursive REF field (`itRef`/`itPtr` → `mkNil(ty)` — sound, the
  ## nil-const self-heals via `allocRefSort`, `runtime.nim`'s `iekNil` arm)
  ## and a by-value NESTED-OBJECT field (`itTuple` → recurse field-by-field;
  ## bounded because Nim forbids cyclic VALUE nesting). Returns `nil` for a
  ## type with no clean zero encoding this cycle (`itSeq`/`itTable`/`itSet`/
  ## `itArray`/`itVariant`/`itMultiVariant`/`itDistinct`/`itUninterp`) — the
  ## CALLER degrades that one field (SND-1 taint), never guesses.
  case ty.kind
  of itInt: mkIntLit(0)
  of itBool: mkBoolLit(false)
  of itFloat32: mkFloatLit(0.0, 32)
  of itFloat64: mkFloatLit(0.0, 64)
  of itString: mkStrLit("")
  of itRef, itPtr: mkNil(ty)
  of itTuple:
    var zeros: seq[IRExpr]
    for f in ty.fields:
      let z = zeroIRExprForType(f)
      if z == nil: return nil
      zeros.add z
    mkTupleLit(zeros, ty)
  else: nil    ## seq/table/set/array/variant/distinct/uninterp — no clean
               ## zero this cycle; caller degrades (SND-1), never guesses.

const StrOpKinds* = {
  iekStrLen, iekStrAt, iekStrSubstr, iekStrFind, iekStrRfind, iekStrContains,
  iekStrStartsWith, iekStrEndsWith, iekStrReplace, iekStrReplaceAll,
  iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe, iekStrReplaceRe,
  iekStrBytes, iekStrConcat,
  iekIntToStr, iekStrToInt, iekRadixFmt, iekStrUnsupported,
  iekStrToLower, iekStrToUpper, iekRuneToStr, iekStrStrip,
  iekStrInOptionRegion}
  ## Phase 15 Cluster S: the uniform-payload string-op expression kinds.

proc mkStrOp*(kind: IRExprKind, op: string, args: seq[IRExpr] = @[],
              retTy: IRType = IRType(kind: itString)): IRExpr =
  ## Phase 15 Cluster S (S1). Build a string-op IR node. `kind` must be one of
  ## `StrOpKinds`; `op` is the surface op name (diagnostics); `args` the
  ## operands. `retTy` (fix-slice item 5) defaults to the `itString`
  ## sentinel — correct for every caller except `iekStrUnsupported`'s
  ## name-keyed fallback, which passes the call expression's actual
  ## classified type explicitly (see `strRetTy`'s own doc comment).
  doAssert kind in StrOpKinds, "mkStrOp: " & $kind & " is not a string-op kind"
  result = IRExpr(kind: kind)
  result.strOp = op
  result.strArgs = args
  result.strRetTy = retTy

proc mkContains*(container, key: IRExpr): IRExpr =
  IRExpr(kind: iekContains, container: container, key: key)

proc mkGetCurrentExn*(): IRExpr =
  ## Phase 15 E8: `getCurrentException()` magic intrinsic node.
  IRExpr(kind: iekGetCurrentExn)

proc mkGetCurrentExnMsg*(): IRExpr =
  ## Phase 15 E8: `getCurrentExceptionMsg()` magic intrinsic node.
  IRExpr(kind: iekGetCurrentExnMsg)

proc mkSeqAdd*(recv, val: IRExpr): IRExpr =
  IRExpr(kind: iekSeqAdd, mutRecv: recv, mutArg: val)
proc mkSeqDel*(seqx, idx: IRExpr): IRExpr =
  IRExpr(kind: iekSeqDel, delSeq: seqx, delIdx: idx)
proc mkSeqInsert*(seqx, val, idx: IRExpr): IRExpr =
  IRExpr(kind: iekSeqInsert, insSeq: seqx, insVal: val, insIdx: idx)
proc mkSeqPop*(seqx: IRExpr): IRExpr =
  IRExpr(kind: iekSeqPop, popSeq: seqx)
proc mkTableSet*(recv, key, val: IRExpr): IRExpr =
  IRExpr(kind: iekTableSet, tabRecv: recv, tabKey: key, tabVal: val)
proc mkTableDel*(recv, key: IRExpr): IRExpr =
  IRExpr(kind: iekTableDel, mutRecv: recv, mutArg: key)
proc mkSetIncl*(recv, elem: IRExpr): IRExpr =
  IRExpr(kind: iekSetIncl, mutRecv: recv, mutArg: elem)
proc mkSetExcl*(recv, elem: IRExpr): IRExpr =
  IRExpr(kind: iekSetExcl, mutRecv: recv, mutArg: elem)

proc mkAssign*(name: string, value: IRExpr, aty: IRType = nil): IRStmt =
  ## #163 review R27: `aty` is the target's declared range-relevant type
  ## when the call site could resolve one by true symbol identity, nil
  ## otherwise (default) -- see `IRStmt.isAssign.aty`'s own doc comment.
  IRStmt(kind: isAssign, aname: name, avalue: value, aty: aty)

proc mkWhile*(cond: IRExpr, body: IRStmt, hasAssumedBound = false): IRStmt =
  IRStmt(kind: isWhile, wcond: cond, wbody: body,
         wHasAssumedBound: hasAssumedBound)

proc mkBreak*(): IRStmt = IRStmt(kind: isBreak)
proc mkContinue*(): IRStmt = IRStmt(kind: isContinue)

proc mkBlock*(stmts: seq[IRStmt]): IRStmt =
  IRStmt(kind: isBlock, stmts: stmts)

proc mkIf*(branches: seq[IRBranch], elseBody: IRStmt = nil): IRStmt =
  IRStmt(kind: isIf, branches: branches, elseBody: elseBody)

proc mkLet*(name: string, ty: IRType, value: IRExpr,
           isIntOffsetLocal = false): IRStmt =
  IRStmt(kind: isLet, lname: name, lty: ty, lvalue: value,
         lIsIntOffsetLocal: isIntOffsetLocal)

# IRType constructors — used by the parser/typebridge and by tests.
proc tBool*(): IRType =
  IRType(kind: itBool)

proc tInt*(width: int = 64, signed: bool = true): IRType =
  IRType(kind: itInt, width: width, signed: signed)

proc tUInt*(width: int): IRType =
  IRType(kind: itInt, width: width, signed: false)

proc withRange*(ty: IRType, lo, hi: int64): IRType =
  ## Issue #162. Refine an `itInt` with the declared bounds of the range
  ## subtype it came from. A fresh `IRType` rather than a mutation: `IRType`
  ## is a `ref` and base types are shared freely across the IR, so refining
  ## one in place would silently narrow every unrelated use of it.
  doAssert ty.kind == itInt, "withRange: not an itInt: " & $ty.kind
  IRType(kind: itInt, width: ty.width, signed: ty.signed,
         hasRange: true, rangeLo: lo, rangeHi: hi, enumName: ty.enumName)

proc withEnumName*(ty: IRType, name: string): IRType =
  ## Issue #163 (rev item 1). Stamp the lifted `itInt`'s ORIGIN enum name —
  ## see `IRType.enumName`'s own field doc for why witness reconstruction
  ## needs it. A fresh `IRType` for the same reason `withRange` is: `IRType`
  ## is a shared `ref`, so mutating one in place would leak the name onto
  ## every other use of the same base type. Carries every existing `itInt`
  ## field forward (unlike `withRange`, which is always called FIRST in the
  ## enum arm and so has nothing of its own to preserve beyond width/signed)
  ## so `ranged(...).withEnumName(...)` chains without dropping the range
  ## just attached.
  doAssert ty.kind == itInt, "withEnumName: not an itInt: " & $ty.kind
  IRType(kind: itInt, width: ty.width, signed: ty.signed,
         hasRange: ty.hasRange, rangeLo: ty.rangeLo, rangeHi: ty.rangeHi,
         enumName: name)

proc tTuple*(fields: seq[IRType], fieldNames: seq[string] = @[],
             objectName: string = "", nominalId: string = "",
             isPlaceholder: bool = false, nameIsRefAlias: bool = false): IRType =
  ## `fieldNames.len` must equal `fields.len` or be empty (positional).
  ## `isPlaceholder` (Cluster H Step C): true ONLY for a recursion-truncated
  ## named-ref placeholder (`namedRefPlaceholder` and the inline-ref-field
  ## placeholder, `dsl_typebridge.nim`) — see the `IRType.isPlaceholder`
  ## field doc. `nameIsRefAlias` (Cluster H Step C): true iff `objectName`
  ## itself names a `ref`/`ptr` alias — see the `IRType.nameIsRefAlias` field
  ## doc. Both default false for every ordinary tuple/object construction.
  doAssert fieldNames.len == 0 or fieldNames.len == fields.len
  let names = if fieldNames.len > 0: fieldNames
              else: newSeq[string](fields.len)   ## all-""
  IRType(kind: itTuple, fields: fields, fieldNames: names, objectName: objectName,
         nominalId: nominalId, isPlaceholder: isPlaceholder,
         nameIsRefAlias: nameIsRefAlias)

proc tArray*(elemTy: IRType, size: int): IRType =
  IRType(kind: itArray, elemTy: elemTy, size: size)

proc tString*(): IRType =
  IRType(kind: itString)

proc tUninterp*(name: string): IRType =
  ## Phase 15 Z3b: the IR type of an uninterpreted reference (`svUninterpRef`).
  IRType(kind: itUninterp, uninterpName: name)

proc tFloat32*(): IRType = IRType(kind: itFloat32)   ## Phase 15 F1
proc tFloat64*(): IRType = IRType(kind: itFloat64)   ## Phase 15 F1

proc tDistinct*(name: string, base: IRType): IRType =
  ## Phase 15 G4 (ADR-0008 D4): a `distinct T` type modelled as a fresh
  ## uninterpreted Z3 sort named `name`, carrying its base `IRType`.
  IRType(kind: itDistinct, distinctName: name, distinctBase: base)

proc tRef*(pointeeTy: IRType): IRType =
  ## Phase 15 R1a (ADR-0010): a `ref T` type carrying its pointee `T`.
  IRType(kind: itRef, refPointeeTy: pointeeTy)

proc tPtr*(pointeeTy: IRType): IRType =
  ## Phase 15 R1a (ADR-0010): a `ptr T` type carrying its pointee `T`.
  IRType(kind: itPtr, ptrPointeeTy: pointeeTy)

proc tSeq*(elemTy: IRType): IRType =
  IRType(kind: itSeq, seqElemTy: elemTy)

proc tUnsupportedFieldSeq*(elemTy: IRType, reason: string,
                            kind: SymexErrorKind = seNestedSeqUnsupported): IRType =
  ## Round-6 Bug #2 (scoped decline) — see the doc block beside
  ## `isUnsupportedFieldPlaceholder` for the full mechanism. `reason` is a
  ## `dsl_typebridge.fieldDeclineMsg`-formatted string (parse-time-captured
  ## location + note); non-empty, always (an empty `reason` would silently
  ## look like an ordinary seq to `isUnsupportedFieldPlaceholder`). `kind`
  ## (N47-followup, walker v110) defaults to `seNestedSeqUnsupported` — every
  ## PRE-EXISTING caller (the declared-field-type-gap origin) keeps its exact
  ## classification unchanged; an OPERATION-level degrade origin (e.g.
  ## `iekSeqAdd`, runtime.nim) passes its own kind explicitly. See
  ## `seqUnsupportedFieldKind`'s doc (above) for why the two origins need
  ## different classifications.
  doAssert reason.len > 0, "tUnsupportedFieldSeq: reason must be non-empty"
  IRType(kind: itSeq, seqElemTy: elemTy, seqUnsupportedFieldReason: reason,
         seqUnsupportedFieldKind: kind)

proc tTable*(keyTy, valTy: IRType): IRType =
  IRType(kind: itTable, tabKeyTy: keyTy, tabValTy: valTy)

proc tSet*(elemTy: IRType): IRType =
  IRType(kind: itSet, setElemTy: elemTy)

proc satAdd64*(a, b: int64): int64 =
  ## D2 (round-6 review remediation, N9 companion). Saturating add: caps at
  ## `high(int64)` instead of wrapping. Shared by `allocCostOf` (below) and
  ## any caller that folds a sequence of costs without risking overflow.
  if a >= high(int64) - b: high(int64) else: a + b

proc satMul64*(a, b: int64): int64 =
  ## D2 companion to `satAdd64`: saturating multiply. `a`/`b` are always
  ## non-negative counts (array sizes / allocation costs) in this module's
  ## callers, so the simple `high div b` guard is sufficient (no negative-
  ## operand sign case to handle).
  if a == 0 or b == 0: 0'i64
  elif a > high(int64) div b: high(int64)
  else: a * b

proc allocCostOf*(t: IRType): int64 =
  ## D2 (round-6 review remediation, N9 companion). Predicts, WITHOUT
  ## allocating anything, the number of leaf Z3 constant/array allocations
  ## `allocateSym` (`runtime.nim`) would perform for a value of type `t`.
  ## Mirrors `allocateSym`'s own recursive dispatch kind-for-kind — this is
  ## the fix for the gap N9's flat `arm.fieldTypes.len` count missed: N9
  ## bounded the NUMBER of fields but not what each field itself costs to
  ## allocate, so a composite field type (nested array/tuple/variant) could
  ## amplify allocation work far past what the flat field count suggested
  ## (a single `array[1_000_000, int]` field counts as `1` under N9's flat
  ## scheme but costs 1,000,000 real Z3 allocations).
  ##   - itArray:  `size` COPIES of the element cost (mirrors allocateSym's
  ##     `for i in 0 ..< ty.size` loop) — the dominant amplifier this slice
  ##     targets.
  ##   - itTuple:  the SUM of each field's cost (one recursive `allocateSym`
  ##     call per field).
  ##   - itVariant: disc cost + all plain-field costs + EVERY declared arm's
  ##     field costs summed — allocateSym's `itVariant` arm allocates fields
  ##     for ALL arms unconditionally, not just the constructed tag (see
  ##     `isVariantConstructSym`'s own doc comment for why construction has
  ##     no "active arm" to narrow to).
  ##   - itMultiVariant: same shape, per axis (disc + that axis's arms'
  ##     fields), plus the shared plain fields once.
  ##   - itSeq: O(1) — `allocateSeqDataRaw` is a SINGLE `mkArrayVar` call
  ##     regardless of element type; it never loops per element. Cost is the
  ##     length var + the data array var, a flat `2`.
  ##   - itTable / itSet: O(1) for the same reason (a fixed small number of
  ##     backing Z3 array/int consts, never a per-entry loop) — `3`/`2`.
  ##   - itDistinct: `1` (the fresh distinct-sort const) PLUS the recursive
  ##     cost of the ejected base (`allocDistinctSym` allocates both).
  ##   - every other scalar leaf (int/bool/float/string/uninterp/ref/ptr):
  ##     `1` (a single fresh Z3 const; `itRef`/`itPtr` allocate one address
  ##     const at THIS level — the pointee is materialised lazily on deref,
  ##     never at allocation time, so it does not recurse here).
  ## Saturates at `high(int64)` (via `satAdd64`/`satMul64`) instead of
  ## overflowing on a pathological shape (e.g. `array[1_000_000, T]` nested
  ## under more composites) — a saturated "huge" cost still trips whatever
  ## budget check consumes it, the honest/safe outcome (never wraps to a
  ## small/negative number that would silently clear a budget it should
  ## have exceeded).
  case t.kind
  of itInt, itBool, itFloat32, itFloat64, itString, itUninterp, itRef, itPtr:
    1'i64
  of itDistinct:
    satAdd64(1'i64, allocCostOf(t.distinctBase))
  of itTuple:
    var total = 0'i64
    for f in t.fields:
      total = satAdd64(total, allocCostOf(f))
    total
  of itArray:
    satMul64(int64(t.size), allocCostOf(t.elemTy))
  of itSeq:
    2'i64
  of itTable:
    3'i64
  of itSet:
    2'i64
  of itVariant:
    var total = allocCostOf(t.vDiscTy)
    for pf in t.vPlainFieldTypes:
      total = satAdd64(total, allocCostOf(pf))
    for arm in t.vArms:
      for ft in arm.fieldTypes:
        total = satAdd64(total, allocCostOf(ft))
    total
  of itMultiVariant:
    var total = 0'i64
    for pf in t.mvPlainFieldTypes:
      total = satAdd64(total, allocCostOf(pf))
    for ax in t.mvAxes:
      total = satAdd64(total, allocCostOf(ax.discTy))
      for arm in ax.arms:
        for ft in arm.fieldTypes:
          total = satAdd64(total, allocCostOf(ft))
    total

# ---------------------------------------------------------------------------
# Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution 2026-08-15) —
# per-field UNSUPPORTED PLACEHOLDER.
#
# `classifyObjectRecordFields` (dsl_typebridge.nim) marks a declared
# object/variant field whose type is structurally unsupported for allocation
# backing (today: `seq[T]` where `T` is not in `allocateSeqDataRaw`'s backed
# element set, `runtime.nim`) with `seqUnsupportedFieldReason` set — the
# `itSeq` KIND and `seqElemTy` are otherwise UNCHANGED (deliberately NOT an
# `itUninterp` swap: this field still needs a real `seq[T]`-shaped witness
# reader — see `emitTyAndReader`'s `itSeq` arm — and must still pass
# `isRenderableWitnessTy` so it never re-triggers CR-2c's WHOLE-PARAMETER
# demotion, which would reintroduce a whole-run poison by a different
# route). This extends R8's `unsupportedFieldPlaceholder` precedent from
# "omitted constructor field" to "declared field type" scope.
# `allocateSym`'s `itSeq` arm recognizes the flag and allocates a FRESH,
# length-FORCED-TO-ZERO placeholder (never raises, never calls
# `allocateSeqDataRaw`) instead of the CR-2b/CR-2c `__unsupported:`/
# `__unsupported_witness:` `itUninterp` placeholders' whole-run raise —
# those are reached at top-level PARAMETER-allocation time (before ANY body
# is walked, so a whole-run degrade is the only sound option); this one is
# reached allocating one FIELD of a possibly-otherwise-clean object, so
# eagerly raising would reintroduce exactly Bug #2 (an untouched arm's field
# poisoning the whole type). `dsl_parser.nim`'s `nnkDotExpr` field-read arms
# use `isUnsupportedFieldPlaceholder` to detect a READ of this placeholder
# and deposit an SND-1 taint on that read's own statement (classified,
# path-scoped) instead of building a real field accessor; `retBindEq`
# (runtime.nim) uses the mirrored `SymVal.isUnsupportedFieldPlaceholder` flag
# to SKIP the eq constraint on such a field (no-constraint = sound
# over-approximation — the read-taint owns honesty).
proc isUnsupportedFieldPlaceholder*(ty: IRType): bool =
  ty.kind == itSeq and ty.seqUnsupportedFieldReason.len > 0

proc isBackedSeqElemTy*(elemTy: IRType): bool =
  ## Mirrors EXACTLY the element kinds `allocateSeqDataRaw` (`runtime.nim`)
  ## can back with a real Z3 array-of-`V` representation — its `case
  ## elemTy.kind` arms for `itRef`/`itPtr` (uninterpreted `Ref_T` element
  ## sort), `itBool`, `itFloat32`, `itFloat64`, `itString`, and `itInt` (any
  ## fixed width). Every OTHER element kind (itTuple, itSeq, itTable, itSet,
  ## itVariant, itMultiVariant, itDistinct, itUninterp, …) falls to
  ## `allocateSeqDataRaw`'s `else` arm, which raises
  ## `SymexNestedSeqUnsupportedError` — this is the SAME "never duplicate the
  ## match" discipline `isRenderableSeqElemTy` documents for the witness-
  ## reader fragment, but for the (broader, allocation-time) backing
  ## fragment; the two predicates are intentionally DIFFERENT (a `seq[bool]`/
  ## `seq[string]` is backed here but not witness-renderable there — do not
  ## conflate them). Used by `classifyObjectRecordFields`
  ## (dsl_typebridge.nim) to detect a field needing the scoped-decline
  ## placeholder above.
  elemTy.kind in {itBool, itFloat32, itFloat64, itString, itRef, itPtr} or
  elemTy.kind == itInt

# ---------------------------------------------------------------------------
# RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality) shared
# renderability predicates.
#
# `emitTyAndReader` (`symex.nim`) is a POST-SOLVE witness-reader codegen
# macro that only knows how to build a Nim reader expression for a fixed
# sub-fragment of `itSeq`/`itTable`/`itSet` element/key/value shapes; every
# other shape used to `error()` at macro-expansion time (a compile abort,
# strictly worse than `sxUnknown` under §0 Invariant 3). `classifyType`
# (`dsl_typebridge.nim`) now consults these SAME predicates at classify
# time to decide whether to build a real `itSeq`/`itTable`/`itSet` or fall
# back to an `itUninterp("__unsupported_witness:" & s)` placeholder (which
# `allocateSym` turns into a classified whole-run `sxUnknown` at
# parameter-allocation time, before the witness reader is ever reached).
# ONE shared helper per container kind — never duplicate the match between
# the classify site and the codegen site, or the two can silently drift
# apart (over- or under-triggering the degrade).
proc isRenderableSeqElemTy*(elemTy: IRType): bool =
  ## Mirrors exactly the shapes `emitTyAndReader`'s `itSeq` arm can render:
  ## any fixed-width int (`int8/16/32/64`, `uint8/16/32/64` — `byte` is the
  ## `uint8` alias), `float64`, `float32`, or a `ref` element (rendered via
  ## `new(T)` defaults, R3).
  ##
  ## RFC-chapulin-hardening M1 widened this from int64-only to the full
  ## fixed-width-int family: `extractSeqElements`/`allocateSeqDataRaw`/
  ## `seqElemAt` (`smt/runtime.nim`) already dispatched on every `(signed,
  ## width)` combination below (Phase 15 C4's seq-index/HOF plumbing) — only
  ## the witness READER (`emitTyAndReader`'s `itSeq` arm) was missing cases,
  ## so this predicate is widened in lockstep with that reader per this
  ## proc's own contract (see module doc comment above).
  (elemTy.kind == itInt and
   (elemTy.width == 8 or elemTy.width == 16 or
    elemTy.width == 32 or elemTy.width == 64)) or
  elemTy.kind == itFloat64 or
  elemTy.kind == itFloat32 or
  elemTy.kind == itRef

proc isRenderableTableTy*(keyTy, valTy: IRType): bool =
  ## Mirrors exactly the shape `emitTyAndReader`'s `itTable` arm can render:
  ## `Table[string, int64]`.
  keyTy.kind == itString and
  valTy.kind == itInt and valTy.signed and valTy.width == 64

proc isRenderableSetElemTy*(elemTy: IRType): bool =
  ## Mirrors exactly the shape `emitTyAndReader`'s `itSet` arm can render:
  ## `HashSet[int64]`.
  elemTy.kind == itInt and elemTy.signed and elemTy.width == 64

proc isRecursionPlaceholder*(ty: IRType): bool =
  ## Cluster H Step C (ADR-0022 Round-2). True iff `ty` is a
  ## recursion-truncated named-ref POINTEE PLACEHOLDER
  ## (`namedRefPlaceholder` / the inline-ref-field placeholder,
  ## `dsl_typebridge.nim`) — built to break a self-referential field's
  ## compile-time recursion, and carrying NO real field list. This is the
  ## explicit PROVENANCE check (`IRType.isPlaceholder`), replacing the old
  ## `pointee.kind == itTuple and pointee.fields.len == 0` heuristic that was
  ## duplicated at two witness-rendering sites (`symex.nim`'s
  ## `emitTyAndReader`, this module's `isRenderableWitnessTy`). That
  ## heuristic was AMBIGUOUS: a legitimately zero-field named ref type
  ## (`type Token = ref object`, no fields) also has `fields.len == 0` at its
  ## TOP-LEVEL full pointee, so a proven-non-nil `p: Token` would have
  ## mis-rendered as `nil` (an unsound witness). The explicit flag fires ONLY
  ## for a genuine recursion placeholder, never for a real (possibly
  ## zero-field) object pointee.
  ty.kind == itTuple and ty.isPlaceholder

proc isRenderableWitnessTy*(ty: IRType): bool =
  ## RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality), nested-aggregate
  ## completeness. RECURSIVE renderability predicate over the WHOLE witness
  ## type-tree, mirroring EXACTLY the type-tree `emitTyAndReader` (`symex.nim`)
  ## walks — so the predicate and the reader can never drift. Returns true iff
  ## every leaf `emitTyAndReader` would reach is renderable (i.e. it would build
  ## a compiling witness reader without hitting one of its three
  ## `itSeq`/`itTable`/`itSet` `error()` sites).
  ##
  ## The leaf checks reuse `isRenderableSeqElemTy`/`isRenderableTableTy`/
  ## `isRenderableSetElemTy` — ONE recursive source of truth — so a nested
  ## `seq[Widget]`/`Table[string,string]`/`HashSet[string]` inside a tuple /
  ## object / array / variant / distinct / ref pointee degrades the WHOLE
  ## top-level parameter to `sxUnknown` at parameter-allocation time rather than
  ## aborting compilation at witness codegen.
  ##
  ## Each arm below corresponds to the same-kind arm of `emitTyAndReader`:
  case ty.kind
  of itBool, itInt, itString, itFloat32, itFloat64:
    true                                      ## primitive leaf readers
  of itUninterp:
    # `emitTyAndReader`'s `itUninterp` arm handles `__closure` /
    # `__unsupported:*` / `__unsupported_witness:*` placeholders (and defers a
    # raw opaque-ref to cluster E). NONE of these are the CR-2c seq/Table/Set
    # `error()` sites, so an `itUninterp` never contributes an unrenderable
    # witness leaf in THIS sense — leave its existing handling untouched.
    true
  of itDistinct:
    isRenderableWitnessTy(ty.distinctBase)    ## renders base then wraps
  of itTuple:
    # `emitTyAndReader`'s `itTuple` arm: a heuristically-"likely variant"
    # object (`fields.len > 2`, `fieldNames[0] == "kind"`) renders as
    # `default(Object)` WITHOUT recursing into its fields — so it is trivially
    # renderable regardless of field types. Mirror that exactly (do not
    # over-demote it). Otherwise it recurses into every field.
    let isLikelyVariant = ty.objectName.len > 0 and ty.fields.len > 2 and
                          ty.fieldNames.len > 0 and ty.fieldNames[0] == "kind"
    if isLikelyVariant:
      true
    else:
      var ok = true
      for fty in ty.fields:
        if not isRenderableWitnessTy(fty): ok = false; break
      ok
  of itArray:
    isRenderableWitnessTy(ty.elemTy)          ## recurses into elem type + values
  of itSeq:
    # Round-6 Bug #2: a scoped-decline placeholder seq is ALWAYS renderable
    # regardless of its (unbacked) element kind — `emitTyAndReader`'s `itSeq`
    # arm special-cases `seqUnsupportedFieldReason` to render a type-correct
    # EMPTY literal instead of reading (nonexistent) witness content, so it
    # never reaches the renderable-element-kind check below. Checked FIRST:
    # if this were routed through the ordinary `isRenderableSeqElemTy` check,
    # an unbacked element kind (the very reason this placeholder exists)
    # would demote the WHOLE parameter to `__unsupported_witness:` — a
    # different route back to Bug #2's whole-run poisoning.
    if isUnsupportedFieldPlaceholder(ty):
      true
    # `emitTyAndReader`'s `itSeq` arm: int64/float64/float32 are leaf readers;
    # a `ref` element renders `new(T)` defaults but STILL builds the pointee
    # TYPE by recursing `emitTyAndReader(refPointeeTy)` — so a `seq[ref P]` is
    # renderable iff `P` is. Every other element kind hits the `error()` site.
    elif isRenderableSeqElemTy(ty.seqElemTy):
      if ty.seqElemTy.kind == itRef:
        isRenderableWitnessTy(ty.seqElemTy.refPointeeTy)
      else:
        true
    else:
      false
  of itTable:
    isRenderableTableTy(ty.tabKeyTy, ty.tabValTy)   ## leaf-only (no recursion)
  of itSet:
    isRenderableSetElemTy(ty.setElemTy)             ## leaf-only (no recursion)
  of itVariant:
    # `emitTyAndReader`'s `itVariant` arm recurses into: the discriminator,
    # every plain (shared) field, and every arm's fields (including the else
    # arm). All must be renderable.
    var ok = isRenderableWitnessTy(ty.vDiscTy)
    if ok:
      for fty in ty.vPlainFieldTypes:
        if not isRenderableWitnessTy(fty): ok = false; break
    if ok:
      for arm in ty.vArms:
        for fty in arm.fieldTypes:
          if not isRenderableWitnessTy(fty): ok = false; break
        if not ok: break
    ok
  of itMultiVariant:
    # `emitTyAndReader`'s `itMultiVariant` arm recurses into: every plain
    # field, every axis's discriminator, and every arm's fields across all axes.
    var ok = true
    for fty in ty.mvPlainFieldTypes:
      if not isRenderableWitnessTy(fty): ok = false; break
    if ok:
      for ax in ty.mvAxes:
        if not isRenderableWitnessTy(ax.discTy): ok = false; break
        for arm in ax.arms:
          for fty in arm.fieldTypes:
            if not isRenderableWitnessTy(fty): ok = false; break
          if not ok: break
        if not ok: break
    ok
  of itRef, itPtr:
    # `emitTyAndReader`'s `itRef`/`itPtr` arm: a recursive-ref FIELD placeholder
    # (empty-fielded named `itTuple` pointee) renders as `nil` WITHOUT recursing
    # — trivially renderable. Otherwise it recurses `emitTyAndReader(pointee)`.
    let pointee = if ty.kind == itRef: ty.refPointeeTy else: ty.ptrPointeeTy
    if isRecursionPlaceholder(pointee):
      true
    else:
      isRenderableWitnessTy(pointee)

proc tVariant*(objectName, discName: string, discTy: IRType,
               arms: seq[VariantArm],
               plainFieldNames: seq[string] = @[],
               plainFieldTypes: seq[IRType] = @[],
               discTags: seq[tuple[name: string, ord: int]] = @[]): IRType =
  ## Phase 11 + Phase 14 (A2). Tagged sum type — Nim variant object.
  ##
  ## `plainFieldNames`/`plainFieldTypes` carry the always-present
  ## prefix from `nnkRecCase`-bearing objects' plain `nnkIdentDefs`
  ## members — allocated ONCE and shared across all arms.
  ##
  ## `discOrdinals` is the disc enum's full ordinal domain. Required
  ## when any arm has `isElse=true` so the walker can derive the
  ## legal disc range. Empty for exhaustive-`of` variants without
  ## `else:` (the per-arm equality disjunction is then sufficient).
  IRType(kind: itVariant, vObjectName: objectName,
         vDiscName: discName, vDiscTy: discTy, vArms: arms,
         vDiscTags: discTags,
         vPlainFieldNames: plainFieldNames,
         vPlainFieldTypes: plainFieldTypes)

proc mkMultiVariant*(objectName: string,
                     axes: seq[VariantAxis],
                     plainFieldNames: seq[string] = @[],
                     plainFieldTypes: seq[IRType] = @[]): IRType =
  ## Phase 14 (ADR-0003 D1). Constructor for multi-recCase variants.
  ## Asserts `axes.len >= 2` — single-recCase objects MUST use
  ## `tVariant` instead. The two IR kinds are intentionally disjoint
  ## (see itMultiVariant doc).
  doAssert axes.len >= 2,
    "mkMultiVariant requires axes.len >= 2; single-axis objects " &
    "must use tVariant. Got axes.len = " & $axes.len
  IRType(kind: itMultiVariant, mvObjectName: objectName,
         mvAxes: axes,
         mvPlainFieldNames: plainFieldNames,
         mvPlainFieldTypes: plainFieldTypes)

proc `==`*(a, b: IRType): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of itBool, itString: true
  of itUninterp: a.uninterpName == b.uninterpName
  of itFloat32, itFloat64: true   ## Phase 15 F1: kind already matched; no payload
  of itDistinct:   ## Phase 15 G4: nominal name + structural base.
    a.distinctName == b.distinctName and a.distinctBase == b.distinctBase
  of itRef:  a.refPointeeTy == b.refPointeeTy   ## Phase 15 R1a
  of itPtr:  a.ptrPointeeTy == b.ptrPointeeTy   ## Phase 15 R1a
  of itInt:  a.width == b.width and a.signed == b.signed
  of itTuple:
    # N22 (round-6 review, Low): this arm also skips `nominalId` and
    # `nameIsRefAlias` — undocumented until now, unlike the `isPlaceholder`
    # skip's own explicit field-doc rationale ("`IRType.==` stays STRUCTURAL
    # and does NOT compare this field", above). Same rationale, extended:
    # neither field is a STRUCTURAL/shape property. `nominalId` is
    # symbol-identity provenance consumed ONLY by `refPointeeTypeId`
    # (runtime_heap.nim) to key the heap `Ref_T` SORT — and it exists
    # PRECISELY so that two structurally-DIFFERENT renderings of the same
    # named type (a full pointee vs. its empty-fielded recursion
    # placeholder) can still share one sort; folding it into `==` would
    # pull that identity concern back into structural equality and make two
    # otherwise-identical shapes (same `fields`/`fieldNames`/`objectName`)
    # compare unequal merely because they came from different symbol
    # instantiations. `nameIsRefAlias` is likewise a WITNESS-RENDERING
    # concern only (`emitTyAndReader`'s `new`-wrapping decision for a named
    # ref-alias object, Cluster H Step C) — not a property of the tuple's
    # own field shape. Comparing structurally-identical `IRType`s equal
    # regardless of either field matches this proc's own documented
    # contract for `isPlaceholder` and is relied upon the same way
    # (dedup/cache-key-adjacent structural comparisons that must not be
    # perturbed by non-structural provenance metadata).
    if a.fields.len != b.fields.len: return false
    if a.objectName != b.objectName: return false
    for i, f in a.fields:
      if f != b.fields[i]: return false
      if a.fieldNames[i] != b.fieldNames[i]: return false
    true
  of itArray: a.size == b.size and a.elemTy == b.elemTy
  of itSeq:   a.seqElemTy == b.seqElemTy
  of itTable: a.tabKeyTy == b.tabKeyTy and a.tabValTy == b.tabValTy
  of itSet:   a.setElemTy == b.setElemTy
  of itVariant:
    if a.vObjectName != b.vObjectName: return false
    if a.vDiscName != b.vDiscName: return false
    if a.vDiscTy != b.vDiscTy: return false
    if a.vPlainFieldNames != b.vPlainFieldNames: return false
    if a.vPlainFieldTypes.len != b.vPlainFieldTypes.len: return false
    for j, ft in a.vPlainFieldTypes:
      if ft != b.vPlainFieldTypes[j]: return false
    if a.vArms.len != b.vArms.len: return false
    for i, arm in a.vArms:
      if arm.tagOrdinal != b.vArms[i].tagOrdinal: return false
      if arm.tagName    != b.vArms[i].tagName:    return false
      if arm.fieldNames != b.vArms[i].fieldNames: return false
      if arm.fieldTypes.len != b.vArms[i].fieldTypes.len: return false
      for j, ft in arm.fieldTypes:
        if ft != b.vArms[i].fieldTypes[j]: return false
      if arm.isElse != b.vArms[i].isElse: return false
    if a.vDiscTags != b.vDiscTags: return false
    true
  of itMultiVariant:
    if a.mvObjectName      != b.mvObjectName:      return false
    if a.mvPlainFieldNames != b.mvPlainFieldNames: return false
    if a.mvPlainFieldTypes.len != b.mvPlainFieldTypes.len: return false
    for j, ft in a.mvPlainFieldTypes:
      if ft != b.mvPlainFieldTypes[j]: return false
    if a.mvAxes.len != b.mvAxes.len: return false
    for i, ax in a.mvAxes:
      let bx = b.mvAxes[i]
      if ax.discName     != bx.discName:     return false
      if ax.discTy       != bx.discTy:       return false
      if ax.discTags != bx.discTags: return false
      if ax.arms.len     != bx.arms.len:     return false
      for k, arm in ax.arms:
        let barm = bx.arms[k]
        if arm.tagOrdinal != barm.tagOrdinal: return false
        if arm.tagName    != barm.tagName:    return false
        if arm.fieldNames != barm.fieldNames: return false
        if arm.fieldTypes.len != barm.fieldTypes.len: return false
        for j, ft in arm.fieldTypes:
          if ft != barm.fieldTypes[j]: return false
        if arm.isElse != barm.isElse: return false
    true

proc `$`*(t: IRType): string =
  if t.isNil: return "nil"
  case t.kind
  of itBool: "bool"
  of itUninterp: "uninterp[" & t.uninterpName & "]"
  of itFloat32: "float32"
  of itFloat64: "float64"
  of itDistinct: "distinct " & t.distinctName & "(" & $t.distinctBase & ")"  ## G4
  of itRef: "ref " & $t.refPointeeTy    ## Phase 15 R1a
  of itPtr: "ptr " & $t.ptrPointeeTy    ## Phase 15 R1a
  of itInt:
    let prefix = if t.signed: "i" else: "u"
    prefix & $t.width &
      (if t.hasRange: "[" & $t.rangeLo & ".." & $t.rangeHi & "]" else: "")
  of itTuple:
    var s = if t.objectName.len > 0: t.objectName & "{" else: "("
    for i, f in t.fields:
      if i > 0: s.add ", "
      if t.fieldNames[i].len > 0: s.add t.fieldNames[i] & ":"
      s.add $f
    s & (if t.objectName.len > 0: "}" else: ")")
  of itArray:
    "array[" & $t.size & ", " & $t.elemTy & "]"
  of itString:
    "string"
  of itSeq:
    "seq[" & $t.seqElemTy & "]"
  of itTable:
    "Table[" & $t.tabKeyTy & ", " & $t.tabValTy & "]"
  of itSet:
    "HashSet[" & $t.setElemTy & "]"
  of itVariant:
    var plainStr = ""
    for i, fn in t.vPlainFieldNames:
      plainStr.add fn & ": " & $t.vPlainFieldTypes[i] & "; "
    var armsStr = ""
    for i, arm in t.vArms:
      if i > 0: armsStr.add " | "
      armsStr.add arm.tagName & "("
      for j, fn in arm.fieldNames:
        if j > 0: armsStr.add ", "
        armsStr.add fn & ": " & $arm.fieldTypes[j]
      armsStr.add ")"
    t.vObjectName & "{" & plainStr & t.vDiscName & ": " & $t.vDiscTy &
      " ⇒ " & armsStr & "}"
  of itMultiVariant:
    var plainStr = ""
    for i, fn in t.mvPlainFieldNames:
      plainStr.add fn & ": " & $t.mvPlainFieldTypes[i] & "; "
    var axesStr = ""
    for i, ax in t.mvAxes:
      if i > 0: axesStr.add " × "
      var armsStr = ""
      for j, arm in ax.arms:
        if j > 0: armsStr.add " | "
        armsStr.add (if arm.isElse: "else" else: arm.tagName)
      axesStr.add ax.discName & ": " & $ax.discTy & " ⇒ {" & armsStr & "}"
    t.mvObjectName & "{" & plainStr & axesStr & "}"

proc plainEnglishTypeKind*(k: IRTypeKind): string =
  ## Round-6 N12 (message-formatting boundary). Several classified-decline
  ## message builders interpolate a BARE `IRTypeKind` (`$elemTy.kind`,
  ## `$ty.tabKeyTy.kind`, etc.) rather than the structural `$IRType` above —
  ## Nim's default enum `$` renders the IDENTIFIER itself ("itTuple",
  ## "itSeq", ...), leaking internal IR vocabulary verbatim into a
  ## `SymexErrorInfo.msg` that reaches the user through `SymexResult.errors`
  ## (there is no other user-facing rendering boundary in this codebase —
  ## `.msg` IS the user-facing string). This is the SINGLE translation point
  ## every such emitting site should route through instead of interpolating
  ## `$k` directly — plain language for a user who never sees `dsl_typebridge
  ## .classifyType`'s internal type-tag names, not a machine identifier.
  ## Internal audit/log strings that never reach a `SymexResult` (comments,
  ## `checkpoint()` debug output, etc.) may keep using `$k` freely — this
  ## helper is for message TEXT specifically, not every stringification of
  ## an `IRTypeKind` in the codebase.
  case k
  of itInt: "integer"
  of itBool: "bool"
  of itString: "string"
  of itTuple: "tuple type"
  of itArray: "array type"
  of itSeq: "seq type"
  of itTable: "table type"
  of itSet: "set type"
  of itVariant: "variant type"
  of itMultiVariant: "multi-axis variant type"
  of itUninterp: "unmodeled type"
  of itFloat32: "float32"
  of itFloat64: "float64"
  of itRef: "ref type"
  of itPtr: "ptr type"
  of itDistinct: "distinct type"

type
  FieldAllocIssue* = object
    ## N39 (round-6 fix round 5). Carries the SAME classified
    ## `SymexErrorKind` + message `allocateSym` (`runtime.nim`) would have
    ## RAISED for an unclassifiable field type, computed WITHOUT calling it
    ## -- see `unallocatableFieldIssue` below.
    kind*: SymexErrorKind
    msg*: string

proc unallocatableFieldIssue*(t: IRType): Option[FieldAllocIssue] =
  ## N39 (round-6 fix round 5 — closing a mis-scoped safety certification in
  ## the raw-raise-in-lower CLASS), extended by N40 (round-6 fix round 6,
  ## allocateSym totality). Predicts, WITHOUT allocating anything, whether
  ## `allocateSym` (`runtime.nim`) would have DECLINED for a value of type
  ## `t` -- the `itUninterp` `__ownership:`/`__unsupported:`/
  ## `__unsupported_witness:` cases and the `itTable` (both key- and
  ## value-type mismatch) / `itSet` unsupported-shape cases. Mirrors
  ## `allocateSym`'s own recursive dispatch kind-for-kind, exactly like
  ## `allocCostOf` above (same "update both together" discipline) --
  ## recurses through every COMPOSITE kind `allocateSym` recurses through
  ## (`itDistinct`'s base, `itTuple`'s fields, `itArray`'s element,
  ## `itVariant`/`itMultiVariant`'s disc + plain fields + every arm's
  ## fields), so a field type nested arbitrarily deep under any of these
  ## (e.g. `array[3, Table[string, string]]`) is still caught, not just a
  ## bare top-level unsupported field.
  ##
  ## N40 fixed a FALSE NEGATIVE this predicate carried since N39: a
  ## non-string-key Table (`Table[int, string]` -- ordinary, unrestricted
  ## Nim syntax, reachable via `classifyType` like any other field type) was
  ## NOT flagged here even though `allocateSym`'s `itTable` arm could not
  ## back it (previously an untagged `ValueError` crash there; N40 converts
  ## that arm to the classified `seUnsupportedTableKeyType` in-band degrade
  ## -- see its own doc comment). Every OTHER arm below was re-verified
  ## against `allocateSym`'s actual dispatch this slice and confirmed to
  ## already mirror it correctly.
  ##
  ## Deliberately does NOT flag: the `itMultiVariant` axis-disc-kind
  ## `ValueError` raise (a Defect-class walker-bug sentinel -- the axis
  ## discriminator is always a BV/Int representation by construction, never
  ## a user-reachable shape -- out of the raw-raise-in-lower CLASS's own
  ## scope per N36's audit header, "Defect-class invariant raises ... are
  ## NOT in scope"); or `itSeq` (already self-guarded inside `allocateSym`'s
  ## own `itSeq` arm via `isBackedSeqElemTy`, PLUS `scopedDeclineFieldTy`'s
  ## Bug #2 scoped decline upstream at classify time) -- flagging either
  ## here would be a false positive, not a real `allocateSym` decline.
  result = none(FieldAllocIssue)
  case t.kind
  of itUninterp:
    let n = t.uninterpName
    if n.len >= 12 and n[0 ..< 12] == "__ownership:":
      result = some(FieldAllocIssue(kind: heUnsupportedOwnership,
        msg: "ownership wrapper `" & n[12 .. ^1] &
             "` is out of scope for the ref cluster (Breadth-LOW-L4)"))
    elif n.len >= 22 and n[0 ..< 22] == "__unsupported_witness:":
      # N40: message widened to match `allocateSym`'s own text verbatim (was
      # missing this suffix since N39 -- a drift this slice's "update both
      # together" pass caught and closed; the `FieldAllocIssue` doc comment's
      # own contract already claimed "the SAME ... message", which this
      # restores).
      result = some(FieldAllocIssue(kind: feUnsupportedWitnessType,
        msg: "unsupported witness shape `" & n[22 .. ^1] &
             "`; the supported fragment is {seq[int64], seq[float64], " &
             "seq[float32], seq[ref T], Table[string, int64], " &
             "HashSet[int64]} plus scalar/tuple/array/object element or " &
             "value types therein"))
    elif n.len >= 14 and n[0 ..< 14] == "__unsupported:":
      # N40: same message-drift fix as the witness-type arm above.
      result = some(FieldAllocIssue(kind: feUnsupportedParamType,
        msg: "unsupported parameter type `" & n[14 .. ^1] &
             "`; the supported fragment is {bool, int, int{8,16,32,64}, " &
             "uint, uint{8,16,32,64}, range[..], Natural, Positive, float, " &
             "float{32,64}, string, char, byte}"))
  of itTable:
    # N40: the false-negative this slice closes -- see this proc's own doc
    # comment above.
    if t.tabKeyTy.kind != itString:
      result = some(FieldAllocIssue(kind: seUnsupportedTableKeyType,
        msg: "Table key type not modeled: " & $t.tabKeyTy &
             " — only Table[string, V] is supported " &
             "(seUnsupportedTableKeyType)"))
    elif not (t.tabValTy.kind == itInt and t.tabValTy.width == 64 and
              t.tabValTy.signed):
      result = some(FieldAllocIssue(kind: seUnsupportedTableValType,
        msg: "Table value type not modeled: " & $t.tabValTy &
             " — only Table[string, int] is supported " &
             "(seUnsupportedTableValType)"))
  of itSet:
    if not (t.setElemTy.kind == itInt and t.setElemTy.width == 64):
      result = some(FieldAllocIssue(kind: seUnsupportedSetCharInterop,
        msg: "HashSet element type not modeled: " & $t.setElemTy &
             " — only HashSet[int] (BV[64]) is supported " &
             "(seUnsupportedSetCharInterop)"))
  of itDistinct:
    result = unallocatableFieldIssue(t.distinctBase)
  of itTuple:
    for f in t.fields:
      result = unallocatableFieldIssue(f)
      if result.isSome: return result
  of itArray:
    result = unallocatableFieldIssue(t.elemTy)
  of itVariant:
    result = unallocatableFieldIssue(t.vDiscTy)
    if result.isSome: return result
    for pf in t.vPlainFieldTypes:
      result = unallocatableFieldIssue(pf)
      if result.isSome: return result
    for arm in t.vArms:
      for ft in arm.fieldTypes:
        result = unallocatableFieldIssue(ft)
        if result.isSome: return result
  of itMultiVariant:
    for pf in t.mvPlainFieldTypes:
      result = unallocatableFieldIssue(pf)
      if result.isSome: return result
    for ax in t.mvAxes:
      result = unallocatableFieldIssue(ax.discTy)
      if result.isSome: return result
      for arm in ax.arms:
        for ft in arm.fieldTypes:
          result = unallocatableFieldIssue(ft)
          if result.isSome: return result
  else:
    discard

proc mkReturn*(): IRStmt =
  IRStmt(kind: isReturn, retExpr: nil)

proc mkReturnVal*(e: IRExpr): IRStmt =
  IRStmt(kind: isReturn, retExpr: e)

proc mkCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType,
            retIntOffsetPositions: seq[int] = @[]): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy, opaque: false,
         retIntOffsetPositions: retIntOffsetPositions)

proc mkOpaqueCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType,
                   inert = false): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy, opaque: true, opaqueInert: inert)

proc mkVariantFieldStmt*(retName: string, recv: IRExpr, fieldName: string,
                         fieldTy: IRType, matchingTags: seq[int]): IRStmt =
  IRStmt(kind: isVariantField, vfRetName: retName, vfRecv: recv,
         vfFieldName: fieldName, vfFieldTy: fieldTy,
         vfMatchingTags: matchingTags)

proc mkVariantReassign*(objName: string, newTag: int,
                        tagName: string): IRStmt =
  IRStmt(kind: isVariantReassign, vrObjName: objName,
         vrNewTag: newTag, vrTagName: tagName)

proc mkVariantReassignSymbolic*(objName, discName: string,
                                rhs: IRExpr): IRStmt =
  ## Phase 14 cycle A4a (ADR-0003 D4). Symbolic-RHS variant disc
  ## reassignment: `discName == ""` selects the only axis on a
  ## single-axis itVariant; non-empty names a specific axis on an
  ## itMultiVariant.
  IRStmt(kind: isVariantReassignSymbolic,
         vrsObjName: objName, vrsDiscName: discName, vrsRhs: rhs)

proc mkVariantConstructSym*(resultVar: string, variantTy: IRType,
                            discExpr: IRExpr, tagSet: seq[int],
                            plainFields: seq[IRExpr], loc: string): IRStmt =
  ## Round-6 A3 (ADR-0029). Symbolic-discriminant variant CONSTRUCTION,
  ## A-normalised: the parser hoists `resultVar` fresh and emits this
  ## statement into the preamble, returning `mkVar(resultVar)` in its place.
  doAssert variantTy.kind == itVariant,
    "mkVariantConstructSym: not an itVariant: " & $variantTy.kind
  doAssert plainFields.len == variantTy.vPlainFieldNames.len,
    "mkVariantConstructSym: plain-field arity mismatch — type has " &
    $variantTy.vPlainFieldNames.len & " plain fields, got " & $plainFields.len
  IRStmt(kind: isVariantConstructSym, vcsResultVar: resultVar,
         vcsVariantTy: variantTy, vcsDiscExpr: discExpr, vcsTagSet: tagSet,
         vcsPlainFields: plainFields, vcsLoc: loc)

proc mkIndexStmt*(retName: string, arr, idx: IRExpr, elemTy: IRType,
                   loc: string = ""): IRStmt =
  IRStmt(kind: isIndex, ixRetName: retName, ixArr: arr,
         ixIdx: idx, ixElemTy: elemTy, ixLoc: loc)

proc mkIndexAssignStmt*(recvName: string, idx, val: IRExpr,
                         loc: string = ""): IRStmt =
  ## N14: `xs[idx] = val` on a seq-typed local/param `recvName`.
  IRStmt(kind: isIndexAssign, iaRecvName: recvName, iaIdx: idx,
         iaVal: val, iaLoc: loc)

proc mkSeqPopStmt*(recvName, retName: string, loc: string = ""): IRStmt =
  ## N14: `retName := recvName.pop()`.
  IRStmt(kind: isSeqPop, spRecvName: recvName, spRetName: retName, spLoc: loc)

proc mkAssert*(cond: IRExpr): IRStmt =
  IRStmt(kind: isAssert, acond: cond)

proc mkAssume*(cond: IRExpr): IRStmt =
  ## Phase 16 SND-2 (ADR-0019): `symexAssume(cond)` — filter/prune, not
  ## assert. Mirrors `mkAssert` structurally (same `acond` field) but
  ## constructs the distinct `isAssume` IR kind.
  IRStmt(kind: isAssume, acond: cond)

proc mkBranch*(cond: IRExpr, body: IRStmt): IRBranch =
  IRBranch(cond: cond, body: body)

proc mkTargetLabel*(name: string): IRStmt =
  IRStmt(kind: isTargetLabel, tname: name)

proc mkRaise*(typeId: string, msg: IRExpr): IRStmt =
  ## Phase 15 E1. `raise newException(T, msg)` — `typeId` is the qualified
  ## exception type, `msg` the (already-parsed) message expression (may be nil).
  IRStmt(kind: isRaise, raiseTypeId: typeId, raiseMsg: msg,
         raiseIsReraise: false)

proc mkReraise*(): IRStmt =
  ## Phase 15 E1. Bare `raise` (re-raise the in-flight exception).
  IRStmt(kind: isRaise, raiseTypeId: "", raiseMsg: nil, raiseIsReraise: true)

proc mkTry*(body: IRStmt, handlers: seq[ExceptHandler],
            finallyBlock: IRStmt = nil): IRStmt =
  ## Phase 15 E1. `try: body  except …: …  [finally: …]`. `finallyBlock` nil
  ## when absent.
  IRStmt(kind: isTry, tryBody: body, tryHandlers: handlers,
         tryFinally: finallyBlock)

proc mkDeref*(retName: string, p: IRExpr, elemTy: IRType): IRStmt =
  ## Phase 15 R1a (ADR-0010). A-normalised `let retName = p[]` for a `ref T`.
  IRStmt(kind: isDeref, dRetName: retName, dPtr: p, dElemTy: elemTy,
         dPtrFamily: false)

proc mkFieldDeref*(retName: string, p: IRExpr, fieldTy: IRType,
                   objTy: IRType, field: string,
                   ptrFamily = false): IRStmt =
  ## Phase 15 R6 (ADR-0010). A-normalised `let retName = p.field` — a FIELD read
  ## through a `ref object`/`ptr object`. The field-split heap array is keyed by
  ## `refPointeeTypeId(objTy) & "__" & field` (value sort = `fieldTy`); the
  ## `Ref_T` sort keys on the OBJECT `objTy` (so every field of the same ref
  ## shares one address).
  IRStmt(kind: isDeref, dRetName: retName, dPtr: p, dElemTy: fieldTy,
         dPtrFamily: ptrFamily, dField: field, dObjTy: objTy)

proc mkPtrDeref*(retName: string, p: IRExpr, elemTy: IRType): IRStmt =
  ## Phase 15 R1a (ADR-0010). A-normalised `let retName = p[]` for a `ptr T`
  ## (the pointer-family deref; pointer arithmetic is classified in R8).
  IRStmt(kind: isDeref, dRetName: retName, dPtr: p, dElemTy: elemTy,
         dPtrFamily: true)

proc mkNewT*(retName: string, refTy: IRType): IRStmt =
  ## Phase 15 R1a (ADR-0010). `let retName = new(T)` allocation binding a fresh
  ## ref. `refTy` is the allocated `itRef`/`itPtr` type.
  IRStmt(kind: isNew, nRetName: retName, nRefTy: refTy)

proc mkDerefWrite*(p: IRExpr, value: IRExpr, elemTy: IRType,
                   ptrFamily = false): IRStmt =
  ## Phase 15 R3 (ADR-0010). `p[] = value` — a heap WRITE through a `ref T`/
  ## `ptr T` deref. Structural at R3 (walker no-ops it); the real `store` lands
  ## R4.
  IRStmt(kind: isDerefWrite, dwPtr: p, dwValue: value, dwElemTy: elemTy,
         dwPtrFamily: ptrFamily)

proc mkFieldDerefWrite*(p: IRExpr, value: IRExpr, fieldTy: IRType,
                        objTy: IRType, field: string,
                        ptrFamily = false): IRStmt =
  ## Phase 15 R6 (ADR-0010). `p.field = value` — a FIELD WRITE through a
  ## `ref object`/`ptr object`. Stores `value` into the per-(type,field) heap
  ## array `refPointeeTypeId(objTy) & "__" & field` at `p`'s address (only that
  ## field's array changes; an aliased read of the same field sees the write).
  IRStmt(kind: isDerefWrite, dwPtr: p, dwValue: value, dwElemTy: fieldTy,
         dwPtrFamily: ptrFamily, dwField: field, dwObjTy: objTy)

proc mkUnsupported*(kind: SymexErrorKind; reason: string;
                    marker: int): IRStmt =
  ## RFC-0005 S1b. An `isUnsupported` node now carries the classified `kind`
  ## the walker records when a path reaches it (§2.2). Reuse the kind the
  ## site already classifies under -- a Class-A site passes its parse-time
  ## error's kind -- and `feUnsupportedStmtKind` for a statement-position
  ## Class-B decline. RFC-0005 §3.2's standing rule applies: the kind you
  ## pass asserts your site shares that kind's substitution class.
  ## RFC-0005 S8: `marker` is the site's anchor (`unMarker`). The parser
  ## never calls this directly -- `declineAtSite`/`declineMarker`
  ## (`dsl_parser.nim`) mint the id; hand-built IR passes its own.
  IRStmt(kind: isUnsupported, unKind: kind, reason: reason, unMarker: marker)

# ---- RFC-0005 S1b: unregistered-callee keys (§2.5 point 3) ------------------
# The parser declines three kinds of callee by NOT registering a `ProcSig`
# (an over-cap generic instantiation, `geInstantiationCapped`; a bodyless
# non-borrow proc over a `distinct` type, `geDistinctBarrier`; an unresolvable
# `getImpl`, `feUnsupportedOp`) and still emits the `mkCall`, so the walker's
# missing-callee arm degrades the reaching path. The arm used to have no kind
# in hand (it lived only in `prog.parseErrors`). The callee KEY is the anchor:
# the parser mints the unregistered key through `unregisteredCalleeKey`,
# which encodes the decline's kind, and the walker reads it back with
# `unregisteredCalleeKind` -- one kind mention at the parse site, recorded at
# the walk site. The key is never registered, so it can never shadow a real
# `ProcSig`.

const unregisteredCalleePrefix* = "__unregistered:"

proc unregisteredCalleeKey*(kind: SymexErrorKind; key: string): string =
  ## The `mkCall` callee key for a declined, never-registered callee.
  unregisteredCalleePrefix & $kind & ":" & key

proc unregisteredCalleeKind*(callee: string;
                             kind: var SymexErrorKind): bool =
  ## Reads back the decline kind `unregisteredCalleeKey` encoded. `false` for
  ## any other key (a missing callee with no parse-time decline behind it).
  ## (Plain slicing, no `strutils`: this module imports it only further down.)
  const pl = unregisteredCalleePrefix.len
  if callee.len <= pl or callee[0 ..< pl] != unregisteredCalleePrefix:
    return false
  var colon = pl
  while colon < callee.len and callee[colon] != ':': inc colon
  if colon == pl or colon >= callee.len: return false
  let name = callee[pl ..< colon]
  for k in SymexErrorKind:
    if $k == name:
      kind = k
      return true
  false

proc mkUnsafeCast*(reason: string; marker: int): IRStmt =
  ## Phase 15 R11 (ADR-0010, RFC §R11). Construct an `isUnsafeCast` node for an
  ## unsafe pointer-materialisation RHS (`cast[ptr T]`/`addr`/`unsafeAddr`); the
  ## walker raises a classified `heUnsafeCast` (sevError) for it.
  ## RFC-0005 S8: `marker` anchors the paired parse-time `heUnsafeCast`.
  IRStmt(kind: isUnsafeCast, ucReason: reason, ucMarker: marker)

# ---- Defaults ---------------------------------------------------------------

proc defaultResourceBudget*(): ResourceBudget =
  ## CR-9(b). Defaults for all resource caps. 0 = unlimited where noted.
  ## RFC-0010: the values now live on the type, so this is `ResourceBudget()`
  ## and a partial literal carries them too. Kept as a name for one release.
  ResourceBudget()

proc defaultSymexSettings*(): SymexSettings =
  ## Phase 2 endpoint: `isOptimised` is now the default. Range-typed
  ## parameters auto-promote to Z3Int when the abstraction-soundness
  ## proof holds; everything else falls back to BV[W]. `isExact` is
  ## available as an explicit override for users who want the
  ## abstraction layer's static analysis itself off the trust chain.
  ##
  ## RFC-0010: the values now live on the type, so this is `SymexSettings()`.
  ## Kept as a name for one release rather than deprecated in the same release
  ## that already changes what every partial literal means.
  SymexSettings()

proc withSymexSettings*(f: proc(s: var SymexSettings) {.closure.},
                        base = defaultSymexSettings()): SymexSettings {.deprecated:
    "RFC-0010: a partial `SymexSettings(...)` literal now carries the defaults, " &
    "so the builder is no longer needed -- write the literal instead. Removed at " &
    "the next major.".} =
  ## Phase 15 Z3d. Builder: start from `base` (default settings) and apply the
  ## mutator `f`. `f` is first so the trailing `do` block binds to it:
  ##   let s = withSymexSettings() do (s: var SymexSettings):
  ##     s.maxFrontierSize = 1
  ## Pass an explicit base by name: `withSymexSettings(base = b) do (s): ...`.
  result = base
  f(result)

proc `+`*(a, b: ResourceBudget): ResourceBudget {.deprecated:
    "RFC-0010: partial literals now carry the defaults, so composition through " &
    "a merge is rarely what you want. This operator keys on differs-from-default, " &
    "which makes the default value itself unwritable through it. Removed at the " &
    "next major.".} =
  ## CR-9(b). Merge: each field of `b` that differs from the default
  ## overrides `a`; a field of `b` left at the default keeps `a`'s value.
  result = a
  let d = defaultResourceBudget()
  if b.queryRLimit != d.queryRLimit: result.queryRLimit = b.queryRLimit
  if b.maxFrontierSize != d.maxFrontierSize: result.maxFrontierSize = b.maxFrontierSize
  if b.maxCallDepth != d.maxCallDepth: result.maxCallDepth = b.maxCallDepth
  if b.maxLoopUnwind != d.maxLoopUnwind: result.maxLoopUnwind = b.maxLoopUnwind
  if b.maxHeapDepth != d.maxHeapDepth: result.maxHeapDepth = b.maxHeapDepth
  if b.maxFreshnessAssertions != d.maxFreshnessAssertions:
    result.maxFreshnessAssertions = b.maxFreshnessAssertions
  if b.maxClosureInlineCount != d.maxClosureInlineCount:
    result.maxClosureInlineCount = b.maxClosureInlineCount
  if b.maxInstantiationsPerProc != d.maxInstantiationsPerProc:
    result.maxInstantiationsPerProc = b.maxInstantiationsPerProc
  if b.maxSplitParts != d.maxSplitParts: result.maxSplitParts = b.maxSplitParts
  if b.maxBytesEncodingLen != d.maxBytesEncodingLen:
    result.maxBytesEncodingLen = b.maxBytesEncodingLen
  if b.seqInlineThreshold != d.seqInlineThreshold:   ## Phase 15 C4
    result.seqInlineThreshold = b.seqInlineThreshold
  if b.maxVariantConstructorForks != d.maxVariantConstructorForks:  ## Round-6 A3
    result.maxVariantConstructorForks = b.maxVariantConstructorForks
  if b.maxVariantConstructorFieldAllocs != d.maxVariantConstructorFieldAllocs:  ## N9
    result.maxVariantConstructorFieldAllocs = b.maxVariantConstructorFieldAllocs

proc `+`*(a, b: SymexSettings): SymexSettings {.deprecated:
    "RFC-0010: partial literals now carry the defaults, so composition through " &
    "a merge is rarely what you want. This operator keys on differs-from-default, " &
    "which makes the default value itself unwritable through it. Removed at the " &
    "next major.".} =
  ## Phase 15 Z3d. Merge: each field of `b` that differs from the default
  ## overrides `a`; a field of `b` left at the default keeps `a`'s value.
  ## Lets per-cluster overrides compose.
  result = a
  let d = defaultSymexSettings()
  if b.integerSemantics != d.integerSemantics: result.integerSemantics = b.integerSemantics
  {.push warning[Deprecated]: off.}
  result.budget = a.budget + b.budget   # its own deprecated sibling
  {.pop.}
  if b.acceptUnknownAsCovered != d.acceptUnknownAsCovered:
    result.acceptUnknownAsCovered = b.acceptUnknownAsCovered
  if b.defectExclusions != d.defectExclusions: result.defectExclusions = b.defectExclusions
  if b.arithChecks != d.arithChecks: result.arithChecks = b.arithChecks  ## R16-1
  if b.inlinePolicy != d.inlinePolicy: result.inlinePolicy = b.inlinePolicy
  if b.replay != d.replay: result.replay = b.replay   ## RFC-0005 S10

proc validateSymexSettings*(s: SymexSettings): seq[string] =
  ## Phase 15 C4 / R16-1. Returns a list of human-readable warnings about
  ## settings that are coherent-but-suspicious (NOT errors — the run proceeds).
  ## Warnings:
  ##   (a) `seqInlineThreshold` is only meaningful under `ipHybrid`
  ##       (ADR-0009); a non-default value paired with
  ##       `ipAlwaysInline`/`ipAlwaysAxiomatize` is silently ignored.
  ##   (b) R16-1: `arithChecks` is empty → no arithmetic forks will be
  ##       emitted; OverflowDefect/DivByZeroDefect/RangeDefect are unreachable.
  ##   (c) R16-1: an arithmetic check is ENABLED in `arithChecks` but its
  ##       corresponding `DefectKind` is in `defectExclusions` → the fork is
  ##       emitted (paying path cost) but the finding is always suppressed.
  ##       This is pure waste; the user likely intended to disable the check
  ##       via `arithChecks` instead.
  ##   (d) RFC-0010 B4 round 2: `budget.maxCallDepth == 0` does NOT mean
  ##       unlimited (unlike most `ResourceBudget` fields) — it exhausts the
  ##       call-depth budget on the very first call. A caller who wrote `0`
  ##       expecting the general "0 = unlimited" convention should write an
  ##       explicit large bound instead.
  ##   (e) Same shape as (d), for symmetry: `budget.maxLoopUnwind == 0` is
  ##       the ONE other field the same false convention would mislead —
  ##       it exhausts after zero loop iterations rather than meaning
  ##       unlimited.
  result = @[]
  let d = defaultSymexSettings()
  if s.budget.seqInlineThreshold != d.budget.seqInlineThreshold and
     s.inlinePolicy != ipHybrid:
    result.add "seqInlineThreshold (" & $s.budget.seqInlineThreshold &
      ") is set but inlinePolicy is " & $s.inlinePolicy &
      " (not ipHybrid); the threshold is ignored under this policy."
  # R16-1 (b): all arith checks disabled → no arithmetic defects can be found.
  if s.arithChecks == {}:
    result.add "arithChecks is empty: no arithmetic defect forks will be " &
      "emitted (OverflowDefect, DivByZeroDefect, and RangeDefect are all " &
      "unreachable). Set acOverflow/acDivByZero/acRange to re-enable."
  # RFC-0010 B4 round 2 (d): maxCallDepth == 0 exhausts immediately rather
  # than meaning unlimited -- a native-stack SIGSEGV was the alternative
  # (see ResourceBudget's umbrella doc comment above), so this field keeps
  # its "0 exhausts" contract permanently, but a caller relying on the
  # general convention needs to be told loudly.
  if s.budget.maxCallDepth == 0:
    result.add "budget.maxCallDepth is 0: unlike most ResourceBudget " &
      "fields, this does NOT mean unlimited -- it exhausts the call-depth " &
      "budget on the very first call (an unlimited cap would let ordinary " &
      "recursion exhaust the native stack). Write an explicit bound sized " &
      "to the SUT's real max call depth instead -- do not assume a " &
      "large-looking round number is automatically safe, since this cap " &
      "bounds NATIVE recursion depth."
  # RFC-0010 B4 round 2 (e): maxLoopUnwind == 0 is the pre-existing sibling
  # exception (never guarded, per this type's umbrella comment) -- warn for
  # the same reason, so both non-unlimited-0 fields are equally visible.
  if s.budget.maxLoopUnwind == 0:
    result.add "budget.maxLoopUnwind is 0: unlike most ResourceBudget " &
      "fields, this does NOT mean unlimited -- it exhausts after zero loop " &
      "iterations (an unlimited cap cannot terminate for an ordinary while " &
      "loop). Write an explicit bound instead, e.g. maxLoopUnwind: 5."
  # R16-1 (c): check enabled in arithChecks but its DefectKind is suppressed
  # by defectExclusions → fork cost paid, finding always suppressed — pure waste.
  const arithCheckToDefectKind: array[ArithCheck, DefectKind] = [
    acOverflow:  dkOverflowDefect,
    acDivByZero: dkDivByZeroDefect,
    acRange:     dkRangeDefect,
  ]
  for ac in s.arithChecks:
    let dk = arithCheckToDefectKind[ac]
    if dk in s.defectExclusions:
      result.add $ac & " is enabled in arithChecks but " & $dk &
        " is in defectExclusions: the fork will be emitted (paying path cost)" &
        " but the finding will always be suppressed. Either remove " & $dk &
        " from defectExclusions or remove " & $ac & " from arithChecks."

proc tLabel*(name: string): SymexTarget =
  SymexTarget(kind: stkLabel, label: name)

proc tAssertionViolation*(): SymexTarget =
  SymexTarget(kind: stkAssertionViolation)

proc tIndexError*(): SymexTarget =
  SymexTarget(kind: stkIndexError)

proc tFieldDefect*(): SymexTarget =
  ## Phase 11 cycle 5. Symex searches for an input that drives a
  ## variant arm-field access while the discriminator's value is
  ## outside the field's arm set — i.e. an input the SUT would
  ## answer with a `FieldDefect` at runtime.
  SymexTarget(kind: stkFieldDefect)

proc tRaisedExn*(typeFilter: string = ""): SymexTarget =
  ## Phase 15 E2a. Symex searches for an input on which the SUT raises an
  ## exception. `typeFilter` (empty = any) restricts the search to a specific
  ## raised type. STRUCTURAL in E2a (real path-constrained search lands E2b).
  SymexTarget(kind: stkRaisedExn, typeFilter: typeFilter)

proc tNilAccess*(): SymexTarget =
  ## Phase 15 R5 (Cluster R, ADR-0010). Symex searches for an input on which the
  ## SUT dereferences a possibly-nil ref/ptr (`p[]` read or write) while `p` is
  ## nil — the NilAccessDefect. The walker forks every deref of a SYMBOLIC ref
  ## into a nil path (`p == nil`, the defect — `sxRaised("NilAccessDefect")`
  ## conceptually) and a non-nil path (`p != nil`, continues normally). Under
  ## this target the nil path's witness (`p == nil`) surfaces as a finding; under
  ## any other target the nil path terminates silently and only the non-nil
  ## continuation is searched. A freshly `new`-allocated (provably non-nil) ref
  ## is short-circuited — its nil fork is UNSAT by construction and skipped.
  SymexTarget(kind: stkNilAccess)

proc optimisedSymexSettings*(): SymexSettings {.deprecated:
    "RFC-0010: byte-identical to defaultSymexSettings() since isOptimised " &
    "became the default at the Phase-2 endpoint. Use SymexSettings(). Removed " &
    "at the next major.".} =
  ## Convenience: settings with `integerSemantics: isOptimised`.
  ##
  ## RFC-0010 C3a: the parenthetical here used to say the flip was still
  ## pending -- "`defaultSymexSettings()` will flip to optimised at the end of
  ## Phase 2". It flipped. This has been byte-identical to
  ## `defaultSymexSettings()`, and now to `SymexSettings()`, ever since, and
  ## the stale comment was the only thing suggesting otherwise.
  ## `looseSymexSettingsPreset` (below) is the genuine non-default preset.
  result = defaultSymexSettings()
  result.integerSemantics = isOptimised

const looseSymexSettingsPreset* = SymexSettings(integerSemantics: isLoose)
  ## Settings with `integerSemantics: isLoose` (UNSOUND — research/
  ## educational only; see ADR-0001).
  ##
  ## RFC-0010 §5's preset-as-const idiom (`README.md:50-57`): this is a
  ## genuine non-default preset (unlike `optimisedSymexSettings`, it is
  ## NOT byte-identical to `SymexSettings()`), so it cannot just be
  ## replaced by the bare default literal -- but a library-shipped preset
  ## still belongs in a `const`, not a second construction path through a
  ## proc, which is what the now-deprecated `looseSymexSettings()` was.

proc looseSymexSettings*(): SymexSettings {.deprecated:
    "RFC-0010: a proc-returning preset is a second construction path " &
    "beside the literal -- use the const looseSymexSettingsPreset instead. " &
    "Removed at the next major.".} =
  ## Deprecated alias for `looseSymexSettingsPreset`. Kept (not deleted) so
  ## existing callers keep compiling across the 0.8.0 release per RFC-0010's
  ## no-downstream-break policy.
  looseSymexSettingsPreset

# ---- Rendering --------------------------------------------------------------
#
# Canonical S-expression form for the IR. Used by Layer-1 isolation
# tests (per ADR-0002) to assert on the parser's output without going
# through the runtime — the renderer is the test-side oracle.

import std/sequtils
import std/strutils

proc render*(e: IRExpr): string =
  if e == nil: return "nil"
  case e.kind
  of iekIntLit:  $e.ival
  of iekFloatLit: $e.fval
  of iekConvIntToFloat: "float(" & render(e.convOperand) & ")"
  of iekConvFloatToInt: "int(" & render(e.convOperand) & ")"
  of iekConvIntWidth:
    "widen" & $e.ciwTgtWidth & "(" & render(e.ciwOperand) & ")"
  of iekConvIntReinterpret:
    "reinterpret" & (if e.cirTgtSigned: "signed" else: "unsigned") &
      $e.cirWidth & "(" & render(e.cirOperand) & ")"
  of iekMathCall:
    var parts: seq[string]
    for a in e.mathArgs: parts.add render(a)
    e.mathOp & "(" & parts.join(", ") & ")"
  of iekBoolLit: $e.bval
  of iekVar:     e.vname
  of iekBinop:   "(" & $e.bop & " " & render(e.lhs) & " " & render(e.rhs) & ")"
  of iekUnop:    "(" & $e.uop & " " & render(e.operand) & ")"
  of iekBorrowOp:  ## Phase 15 G5
    "(borrow:" & e.borrowDistinctName & " " & $e.borrowOp & " " &
      render(e.borrowLhs) & " " & render(e.borrowRhs) & ")"
  of iekField:
    let suffix = if e.fieldName.len > 0: "." & e.fieldName else: "[" & $e.fieldIx & "]"
    render(e.obj) & suffix
  of iekIndex:   render(e.arr) & "[" & render(e.idx) & "]"
  of iekSeqSlice:
    render(e.ssBase) & "[" & render(e.ssLo) & ".." & render(e.ssHi) & "]"
  of iekArrayLit:
    var inner = ""
    for i, c in e.lelems:
      if i > 0: inner.add ","
      inner.add render(c)
    "[" & inner & "]"
  of iekTupleLit:
    var inner = ""
    for i, c in e.telems:
      if i > 0: inner.add ","
      inner.add render(c)
    "(" & inner & ")"
  of iekVariantLit:
    var inner = "@" & e.vlTagName
    for c in e.vlArmFields:
      inner.add "," & render(c)
    for c in e.vlPlainFields:
      inner.add "," & render(c)
    "Vr(" & inner & ")"
  of iekSeqLen:
    render(e.lenObj) & ".len"
  of iekStrLit:
    "\"" & e.sval & "\""
  of iekContains:
    render(e.key) & " in " & render(e.container)
  of iekSeqAdd:    render(e.mutRecv) & ".add(" & render(e.mutArg) & ")"
  of iekSeqDel:    render(e.delSeq) & ".del(" & render(e.delIdx) & ")"
  of iekSeqInsert: render(e.insSeq) & ".insert(" & render(e.insVal) &
                   "," & render(e.insIdx) & ")"
  of iekSeqPop:    render(e.popSeq) & ".pop()"
  of iekTableSet:  render(e.tabRecv) & "[" & render(e.tabKey) & "]:=" &
                   render(e.tabVal)
  of iekTableDel:  render(e.mutRecv) & ".del(" & render(e.mutArg) & ")"
  of iekSetIncl:   render(e.mutRecv) & ".incl(" & render(e.mutArg) & ")"
  of iekSetExcl:   render(e.mutRecv) & ".excl(" & render(e.mutArg) & ")"
  of StrOpKinds:
    var parts: seq[string]
    for a in e.strArgs: parts.add render(a)
    "str." & e.strOp & "(" & parts.join(", ") & ")"
  of iekGetCurrentExn:    "getCurrentException()"
  of iekGetCurrentExnMsg: "getCurrentExceptionMsg()"
  of iekLambda:           ## Phase 15 C1
    var ps: seq[string]
    for p in e.lambdaParams: ps.add p.name
    "lambda@" & $e.lambdaSite.siteHash & "/" & $e.lambdaSite.declOrder &
      "(" & ps.join(",") & ")[caps:" & e.lambdaCaptures.join(",") & "]"
  of iekClosureCall:      ## Phase 15 C1
    var asr: seq[string]
    for a in e.ccArgs: asr.add render(a)
    e.ccCallee & "@(" & asr.join(",") & ")"
  of iekSeqLit:           ## Phase 15 C4
    var es: seq[string]
    for c in e.seqLitElems: es.add render(c)
    "@[" & es.join(",") & "]"
  of iekHofCall:          ## Phase 15 C4
    let initPart = if e.hofInit != nil: "," & render(e.hofInit) else: ""
    render(e.hofSeq) & "." & e.hofOp & "(" & render(e.hofClosure) &
      initPart & ")"
  of iekNil:              ## Phase 15 R5
    "nil"

proc render*(s: IRStmt): string =
  if s == nil: return "nil"
  case s.kind
  of isBlock:
    "{" & s.stmts.mapIt(render(it)).join(";") & "}"
  of isIf:
    var arms = ""
    for br in s.branches:
      arms.add "[" & render(br.cond) & "=>" & render(br.body) & "]"
    if s.elseBody != nil:
      arms.add "[else=>" & render(s.elseBody) & "]"
    "if(" & arms & ")"
  of isLet:
    "let(" & s.lname & ":" & $s.lty & "=" & render(s.lvalue) & ")"
  of isAssign:
    s.aname & ":=" & render(s.avalue)
  of isWhile:
    "while(" & render(s.wcond) & "){" & render(s.wbody) & "}"
  of isBreak:    "break"
  of isContinue: "continue"
  of isReturn:
    if s.retExpr == nil: "return"
    else: "return(" & render(s.retExpr) & ")"
  of isAssert:       "assert(" & render(s.acond) & ")"
  of isAssume:       "assume(" & render(s.acond) & ")"
  of isCall:
    var argstr = ""
    for i, a in s.cargs:
      if i > 0: argstr.add ","
      argstr.add render(a)
    let lhs = if s.retName.len > 0: s.retName & ":=" else: ""
    "call(" & lhs & s.callee & "(" & argstr & "))"
  of isIndex:
    "index(" & s.ixRetName & ":=" & render(s.ixArr) & "[" & render(s.ixIdx) & "])"
  of isIndexAssign:
    "indexAssign(" & s.iaRecvName & "[" & render(s.iaIdx) & "]:=" &
      render(s.iaVal) & ")"
  of isSeqPop:
    "seqPop(" & s.spRetName & ":=" & s.spRecvName & ".pop())"
  of isVariantField:
    "vfield(" & s.vfRetName & ":=" & render(s.vfRecv) & "." &
      s.vfFieldName & ")"
  of isVariantReassign:
    "vreassign(" & s.vrObjName & ".kind:=" & s.vrTagName &
      ")"
  of isVariantReassignSymbolic:
    "vreassignSym(" & s.vrsObjName & "." &
      (if s.vrsDiscName.len == 0: "kind" else: s.vrsDiscName) &
      ":=" & render(s.vrsRhs) & ")"
  of isVariantConstructSym:
    var tags = ""
    for t in s.vcsTagSet: tags.add $t & ","
    var plains = ""
    for c in s.vcsPlainFields: plains.add render(c) & ","
    "vconstructSym(" & s.vcsResultVar & ":=disc(" & render(s.vcsDiscExpr) &
      ")@[" & tags & "];plain=[" & plains & "])"
  of isTargetLabel:  "target(" & s.tname & ")"
  of isRaise:
    if s.raiseIsReraise: "raise()"
    elif s.raiseMsg == nil: "raise(" & s.raiseTypeId & ")"
    else: "raise(" & s.raiseTypeId & "," & render(s.raiseMsg) & ")"
  of isTry:
    var hs = ""
    for h in s.tryHandlers:
      hs.add "[" & h.typeIds.join("|") & "=>" & render(h.body) & "]"
    let fin = if s.tryFinally != nil:
                "[finally=>" & render(s.tryFinally) & "]"
              else: ""
    "try{" & render(s.tryBody) & "}except" & hs & fin
  of isDeref:
    let fam = if s.dPtrFamily: "ptr" else: "ref"
    let fld = if s.dField.len > 0: "." & s.dField else: ""
    s.dRetName & "=deref<" & fam & ">(" & render(s.dPtr) & ")" & fld & ":" &
      $s.dElemTy
  of isNew:
    s.nRetName & "=new(" & $s.nRefTy & ")"
  of isDerefWrite:
    let fam = if s.dwPtrFamily: "ptr" else: "ref"
    let fld = if s.dwField.len > 0: "." & s.dwField else: ""
    "deref<" & fam & ">(" & render(s.dwPtr) & ")" & fld & ":" & $s.dwElemTy &
      "=" & render(s.dwValue)
  of isUnsupported:  "unsupported(" & $s.unKind & ": " & s.reason & ")"
  of isUnsafeCast:   "unsafeCast(" & s.ucReason & ")"
