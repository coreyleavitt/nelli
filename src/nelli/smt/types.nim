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
                       ## on the converted value are correct. Narrowing and
                       ## same-width signedness reinterpretation are OUT of
                       ## scope (recorded declines — no truncate/reinterpret
                       ## primitive is modeled; the pre-B2 identity
                       ## pass-through was silently unsound for both).
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
                      ## (`beBudgetExhausted`) when exceeded — a WALK-TIME
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
    of isWhile:
      wcond*: IRExpr
      wbody*: IRStmt
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
      reason*: string            ## human-readable diagnostic
    of isUnsafeCast:
      ucReason*: string          ## Phase 15 R11: which unsafe pointer-materialisation
                                 ## pattern was routed (`"cast[ptr T]"`, `"addr"`).

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

type
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
                           ## heap semantics.
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
                          ## bound) or a `maxFrontierSize` path prune. The
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

  SymexErrorInfo* = object
    ## Phase 14 cycle C4 / Phase 15 Z3. Structured symex-error record.
    ## `kind` is a closed `SymexErrorKind` (was a free-form string);
    ## `severity` carries the invariant-7 contract.
    kind*:     SymexErrorKind
    severity*: SymexErrorSeverity
    msg*:      string

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
    ## SymexSettings. 0 = unlimited for every field (documented once
    ## here; per-field notes give the default value and what happens
    ## when the limit is reached).
    queryRLimit*: uint
      ## Z3 logical step count bound. `0` (default) is unbounded.
      ## Wired into `runtime.nim:trySolve` via `Z3_solver_set_params`.
      ## Phase 13.
    maxFrontierSize*: int
    maxCallDepth*: int
    maxLoopUnwind*: int
      ## Phase-6 loop unrolling cap; >= 1. Default 5 (`defaultSymexSettings`).
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
    maxHeapDepth*: int
      ## Phase 15 Cluster R (R1a, ADR-0010). Upper bound on the recursive
      ## `ref object` field-expansion / heap-read (`isDeref`) hop count per
      ## path. Default `8`. `0` means unlimited. When a `p[]` deref would
      ## push `path.heapDepth` past this bound the walker halts with
      ## `sxUnknown` + `SymexErrorInfo{kind: heDepthExhausted}` (R9).
    maxFreshnessAssertions*: int
      ## Phase 15 Cluster R (R2, ADR-0010). Upper bound on the number of
      ## fresh-ref distinctness inequalities (`newRef != prior`) the walker
      ## will emit on a SINGLE path. Default `256`. `0` means unlimited.
      ## SOUND over-approximation (heFreshnessCapExceeded hint).
    maxClosureInlineCount*: int
      ## Phase 15 C2b (ADR-0009 D6). Per-call-stack cap on nested closure
      ## descent. Default `64`. `0` means unlimited.
      ## ceInlineBudgetExceeded (sevError) when exceeded.
    maxInstantiationsPerProc*: int
      ## Phase 15 G1c (ADR-0008 D7 / OQ5). Per-base-proc cap on DISTINCT
      ## generic instantiations the parser will register. Default `64`.
      ## `0` means unlimited. geInstantiationCapped (sevError) when exceeded.
    maxVariantConstructorForks*: int
      ## Round-6 A3 (ADR-0029). Structural cap on the number of tags
      ## `isVariantConstructSym` will fork per symbolic-discriminant variant
      ## CONSTRUCTION — checked against `vcsTagSet.len` (parse-time
      ## `case`-branch-narrowed, or the full declared non-else arm count)
      ## BEFORE any solver work, mirroring `maxSplitParts`'s structural-cap
      ## style. Default `8`. Exceeding it classifies a `beBudgetExhausted`
      ## decline (sxUnknown) — never a crash, never an unbounded fork
      ## explosion for a wide unconstrained enum.
    maxVariantConstructorFieldAllocs*: int
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
      ## change). Exceeding it classifies the SAME `beBudgetExhausted`
      ## decline kind (never a parallel mechanism) — never a crash, never
      ## unbounded allocation work for a wide- or deeply-fielded variant.
    maxSplitParts*: int
      ## Phase 15 S5. Upper bound on the number of parts a symbolic
      ## `string.split` decomposition may produce. Default `8`.
    maxBytesEncodingLen*: int
      ## Phase 15 S7a. Upper bound on the concrete byte/char count a
      ## `bytes(s)` byte-view may materialise. Default `32`.
      ## seBytesLengthTooLarge (sxUnknown) when exceeded.
    seqInlineThreshold*: int
      ## Phase 15 C4 (net-new, ADR-0009). Upper bound on CONCRETE seq
      ## length a DSL HOF will UNROLL inline. Default `8`. A concrete
      ## length above this bound — or a SYMBOLIC length — takes the
      ## axiom path. Ignored when `inlinePolicy` is not `ipHybrid`.

  SymexSettings* = object
    integerSemantics*: IntegerSemantics
    budget*: ResourceBudget
      ## CR-9(b): all resource caps consolidated into one sub-object.
      ## Use `defaultResourceBudget()` for the defaults.
    acceptUnknownAsCovered*: bool
      ## Phase 7. When `assertCoveredBy` receives `sxUnknown` from the
      ## solver (timeout, unwind exhaustion, opaque-call uncertainty),
      ## the default is to raise — we cannot *prove* coverage. Setting
      ## this to `true` downgrades UNKNOWN to a soft pass for
      ## environments that treat UNKNOWN as "best-effort attempted".
    defectExclusions*: set[DefectKind]
      ## Phase 15 Z3. Defect families the walker must NOT model as
      ## raise-paths. Default excludes OOM + stack-overflow (modelling
      ## those yields spurious sxRaised for virtually all real SUTs).
    arithChecks*: set[ArithCheck]
      ## R16-1 (Phase 16 ADR-0011 F2). Which arithmetic defect forks to EMIT.
      ## Default all-on `{acOverflow, acDivByZero, acRange}` (debug-like; finds
      ## bugs). Empty = release-like (wrap/unchecked). Orthogonal to
      ## `defectExclusions`: `arithChecks` gates fork emission (2^N cost lever);
      ## `defectExclusions` gates finding surfacing after the fork. In cache key.
    inlinePolicy*: InlinePolicy
      ## Phase 15 Z3. Call-summary strategy (Cluster C owns the axiom
      ## construction; the type/field live here). Default `ipHybrid`.

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

proc mkSeqLit*(elems: seq[IRExpr], elemTy: IRType): IRExpr =
  ## Phase 15 C4. A concrete seq literal `@[a, b, c]` (incl. empty `@[]`).
  IRExpr(kind: iekSeqLit, seqLitElems: elems, seqLitElemTy: elemTy)

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

proc mkStrOp*(kind: IRExprKind, op: string, args: seq[IRExpr] = @[]): IRExpr =
  ## Phase 15 Cluster S (S1). Build a string-op IR node. `kind` must be one of
  ## `StrOpKinds`; `op` is the surface op name (diagnostics); `args` the operands.
  doAssert kind in StrOpKinds, "mkStrOp: " & $kind & " is not a string-op kind"
  result = IRExpr(kind: kind)
  result.strOp = op
  result.strArgs = args

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

proc mkAssign*(name: string, value: IRExpr): IRStmt =
  IRStmt(kind: isAssign, aname: name, avalue: value)

proc mkWhile*(cond: IRExpr, body: IRStmt): IRStmt =
  IRStmt(kind: isWhile, wcond: cond, wbody: body)

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

proc tUnsupportedFieldSeq*(elemTy: IRType, reason: string): IRType =
  ## Round-6 Bug #2 (scoped decline) — see the doc block beside
  ## `isUnsupportedFieldPlaceholder` for the full mechanism. `reason` is a
  ## `dsl_typebridge.fieldDeclineMsg`-formatted string (parse-time-captured
  ## location + note); non-empty, always (an empty `reason` would silently
  ## look like an ordinary seq to `isUnsupportedFieldPlaceholder`).
  doAssert reason.len > 0, "tUnsupportedFieldSeq: reason must be non-empty"
  IRType(kind: itSeq, seqElemTy: elemTy, seqUnsupportedFieldReason: reason)

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
    prefix & $t.width
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

proc mkReturn*(): IRStmt =
  IRStmt(kind: isReturn, retExpr: nil)

proc mkReturnVal*(e: IRExpr): IRStmt =
  IRStmt(kind: isReturn, retExpr: e)

proc mkCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType,
            retIntOffsetPositions: seq[int] = @[]): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy, opaque: false,
         retIntOffsetPositions: retIntOffsetPositions)

proc mkOpaqueCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy, opaque: true)

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

proc mkUnsupported*(reason: string): IRStmt =
  IRStmt(kind: isUnsupported, reason: reason)

proc mkUnsafeCast*(reason: string): IRStmt =
  ## Phase 15 R11 (ADR-0010, RFC §R11). Construct an `isUnsafeCast` node for an
  ## unsafe pointer-materialisation RHS (`cast[ptr T]`/`addr`/`unsafeAddr`); the
  ## walker raises a classified `heUnsafeCast` (sevError) for it.
  IRStmt(kind: isUnsafeCast, ucReason: reason)

# ---- Defaults ---------------------------------------------------------------

proc defaultResourceBudget*(): ResourceBudget =
  ## CR-9(b). Defaults for all resource caps. 0 = unlimited where noted.
  ResourceBudget(
    queryRLimit: 0,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5,
    maxHeapDepth: 8,          ## Phase 15 R1a (ADR-0010)
    maxFreshnessAssertions: 256,  ## Phase 15 R2 (ADR-0010)
    maxClosureInlineCount: 64,    ## Phase 15 C2b (ADR-0009 D6)
    maxInstantiationsPerProc: 64, ## Phase 15 G1c (ADR-0008 D7)
    maxSplitParts: 8,         ## Phase 15 S5
    maxBytesEncodingLen: 32,  ## Phase 15 S7a
    seqInlineThreshold: 8,    ## Phase 15 C4 (net-new)
    maxVariantConstructorForks: 8,  ## Round-6 A3 (ADR-0029)
    maxVariantConstructorFieldAllocs: 64,  ## N9 (round-6 review remediation);
                                            ## unit is LEAF allocations as of
                                            ## D2 (round-6 review remediation)
  )

proc defaultSymexSettings*(): SymexSettings =
  ## Phase 2 endpoint: `isOptimised` is now the default. Range-typed
  ## parameters auto-promote to Z3Int when the abstraction-soundness
  ## proof holds; everything else falls back to BV[W]. `isExact` is
  ## available as an explicit override for users who want the
  ## abstraction layer's static analysis itself off the trust chain.
  SymexSettings(
    integerSemantics: isOptimised,
    budget: defaultResourceBudget(),
    defectExclusions: {dkOutOfMemoryDefect, dkStackOverflowDefect},
    arithChecks: {acOverflow, acDivByZero, acRange},  ## R16-1: all-on default
    inlinePolicy: ipHybrid,
  )

proc withSymexSettings*(f: proc(s: var SymexSettings) {.closure.},
                        base = defaultSymexSettings()): SymexSettings =
  ## Phase 15 Z3d. Builder: start from `base` (default settings) and apply the
  ## mutator `f`. `f` is first so the trailing `do` block binds to it:
  ##   let s = withSymexSettings() do (s: var SymexSettings):
  ##     s.maxFrontierSize = 1
  ## Pass an explicit base by name: `withSymexSettings(base = b) do (s): ...`.
  result = base
  f(result)

proc `+`*(a, b: ResourceBudget): ResourceBudget =
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

proc `+`*(a, b: SymexSettings): SymexSettings =
  ## Phase 15 Z3d. Merge: each field of `b` that differs from the default
  ## overrides `a`; a field of `b` left at the default keeps `a`'s value.
  ## Lets per-cluster overrides compose.
  result = a
  let d = defaultSymexSettings()
  if b.integerSemantics != d.integerSemantics: result.integerSemantics = b.integerSemantics
  result.budget = a.budget + b.budget
  if b.acceptUnknownAsCovered != d.acceptUnknownAsCovered:
    result.acceptUnknownAsCovered = b.acceptUnknownAsCovered
  if b.defectExclusions != d.defectExclusions: result.defectExclusions = b.defectExclusions
  if b.arithChecks != d.arithChecks: result.arithChecks = b.arithChecks  ## R16-1
  if b.inlinePolicy != d.inlinePolicy: result.inlinePolicy = b.inlinePolicy

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

proc optimisedSymexSettings*(): SymexSettings =
  ## Convenience: settings with `integerSemantics: isOptimised`.
  ## (`defaultSymexSettings()` will flip to optimised at the end of
  ## Phase 2 once the abstraction layer has shipped end-to-end.)
  result = defaultSymexSettings()
  result.integerSemantics = isOptimised

proc looseSymexSettings*(): SymexSettings =
  ## Convenience: settings with `integerSemantics: isLoose` (UNSOUND
  ## — research/educational only; see ADR-0001).
  result = defaultSymexSettings()
  result.integerSemantics = isLoose

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
  of isUnsupported:  "unsupported(" & s.reason & ")"
  of isUnsafeCast:   "unsafeCast(" & s.ucReason & ")"
