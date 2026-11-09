## RFC-0016 K4a-table (section 8.1) -- the magic axis: one row per Nim magic,
## keyed by its `TMagic` name. Z3-free; imports only the admission machinery.
##
## `magicAxis` is the table K4a-dispatch will generate its per-site `case`
## from, and the one the universe ledger derives its `magic:` cells from. It
## absorbs `dsl_parser.varParamMagics`: every key of that table is a row here
## with the same verdict (`tsymex_0016_k4a_table` pins it). The rows were
## derived from `docs/rfc/0016-research/magic_table.md`; the lib-wide guard in
## the same test fails on a `{.magic.}` in `lib/` with no row.
##
## Row states (section 8.2), from the research table's status column:
##   * `mModelled`, `mPartial`, `mFolded`, `mBody`: admitted at `msArm`. A
##     partial one is modelled for the shapes its arm accepts and declines the
##     rest at the call; a folded one never reaches the walker as a call (the
##     compiler folds it); a bodied one is walked through its Nim body (K4b:
##     admitted at `msBodyWalk`, which no other row is).
##   * `mDeclined`, `mUnverified`: refused, intent `iModel` (open work), kind
##     `feUnsupportedOp`. An unverified row is one the research table could
##     not show modelled or declined by running it.
##   * `mNever`: compile-time-only, macro and DrNim magics a SUT's typed body
##     cannot carry: refused, intent `iNever`.
##   * `nextafter` (STY-05, HRV-27) is not a `TMagic` member but the math
##     routine the walker recognises by name and cannot model: no SMT-LIB FP
##     primitive. A `never` cell (`nrTheory`).
## K4b. A magic with a real body (not a stub) reaches `ensureProcRegistered`
## and is walked through that body only where its row is admitted at
## `msBodyWalk`, which only the `mmBody` rows are; every other bodied magic
## declines with its row's kind.
## K4a-dispatch. `dispatchMagic` checks a site's hand-written `case` against
## the table at compile time, and `varParamMagics` is gone: a routine with a
## `var` formal and a `{.magic.}` is declined at `msProcRegister` from its row.
import std/[options, macros, sequtils]
import ./admission
import ./errorkind
import ./stdlib_rows

type
  MagicModel* = enum
    mmModelled, mmPartial, mmFolded, mmBody
  MagicSite* = enum
    msArm           ## a hand-written arm elsewhere models the magic; no
                    ## dispatch reads this site (K4b and K4c settle each)
    msProcRegister  ## `ensureProcRegistered`: the call fell through every
                    ## arm; read with `admitMagic`, no row is admitted here
                    ## (a magic with a stub body or a `var` formal declines)
    msVarStmt       ## `parseVarMagicStmt`: a statement-position call of a
                    ## `var`-parameter magic (a `dispatchMagic` site)
    msCallSwitch    ## the stdlib call switch before `ensureProcRegistered`,
                    ## in `parseCallExpr` (a `dispatchMagic` site); its
                    ## arms also name the unsigned operators, which are
                    ## `system` routines with rows in `stdlibAxis`
    msInfix         ## the unsigned operators spelled infix (a
                    ## `dispatchMagic` site)
    msNewString     ## `parseNewStringExpr` (a `dispatchMagic` site)
    msDefOverflow   ## K4a-guard: the opaque-call defect scan lists
                    ## `OverflowDefect` for a call of this magic
    msDefDivZero    ## ... `DivByZeroDefect` (signed `div`/`mod` only; an
                    ## unsigned zero divisor is a C trap, no Defect)
    msDefRange      ## ... `RangeDefect` (`chr`, a step past an enum's or a
                    ## subrange's end)
    msDefFloat      ## ... the float-check Defects, where the owning routine
                    ## was compiled with `nanChecks`/`infChecks`
    msBodyWalk      ## K4b: `ensureProcRegistered`, a magic with a real Nim
                    ## body (not a stub): admitted only for the `mmBody`
                    ## rows, whose body is the semantics; any other row
                    ## declines with its kind, a magic with no row
                    ## `feUnadmitted`. Read with `admitMagic`

type MagicRow = tuple[key: string, row: Row[MagicSite, MagicModel]]

func admittedRow(key: string; model: MagicModel; note: string;
                 also: set[MagicSite]): MagicRow =
  ## Every admitted row is admitted at `msArm`; `also` adds the dispatch
  ## sites whose arm the row names.
  (key, modelled[MagicSite, MagicModel](model, {msArm} + also, note,
                                        elsewhere = some(feUnsupportedOp)))

func mModelled(key, note: string; also: set[MagicSite] = {}): MagicRow =
  admittedRow(key, mmModelled, note, also)
func mPartial(key, note: string): MagicRow = admittedRow(key, mmPartial, note, {})
func mFolded(key, note: string): MagicRow = admittedRow(key, mmFolded, note, {})
func mBody(key, note: string; also: set[MagicSite] = {}): MagicRow =
  admittedRow(key, mmBody, note, also + {msBodyWalk})

func mDeclined(key, note: string): MagicRow =
  (key, refused[MagicSite, MagicModel](some(feUnsupportedOp), note))

func mUnverified(key, note: string): MagicRow =
  (key, refused[MagicSite, MagicModel](some(feUnsupportedOp),
                                       "unverified: " & note))

func mNever(key, note: string): MagicRow =
  (key, refused[MagicSite, MagicModel](some(feUnsupportedOp), note,
                                       intent = iNever, never = nrByDesign))

const magicAxis* = axisTable[MagicSite, MagicModel](axMagic, [
  mModelled("AddI",
    "+ (system/arithmetics.nim:75): binopForInfix P:3291; lowerArith RT:8800-8910 (overflowConds S8bv; width wrap S8w)", also = {msDefOverflow}),
  mModelled("SubI",
    "- (system/arithmetics.nim:82): binopForInfix P:3291; lowerArith RT:8800-8910 (overflowConds S8bv; width wrap S8w)", also = {msDefOverflow}),
  mModelled("MulI",
    "* (system/arithmetics.nim:89): binopForInfix P:3291; lowerArith RT:8800-8910 (overflowConds S8bv; width wrap S8w)", also = {msDefOverflow}),
  mModelled("DivI",
    "div (system/arithmetics.nim:96): RT:8856-8870 divLowByMinusOne (div OverflowDefect; mod = C trap at 32/64 bits); divisorIsZero RT:8801", also = {msDefDivZero, msDefOverflow}),
  mModelled("ModI",
    "mod (system/arithmetics.nim:113): RT:8856-8870 divLowByMinusOne (div OverflowDefect; mod = C trap at 32/64 bits); divisorIsZero RT:8801", also = {msDefDivZero, msDefOverflow}),
  mModelled("UnaryMinusI",
    "- (system/arithmetics.nim:56): nnkPrefix \"-\" P:11196 (uNeg); overflowMagics P:4020", also = {msDefOverflow}),
  mModelled("UnaryMinusI64",
    "- (system/arithmetics.nim:61): nnkPrefix \"-\" P:11196 (uNeg); overflowMagics P:4020", also = {msDefOverflow}),
  mModelled("UnaryPlusI",
    "+ (system/arithmetics.nim:49): nnkPrefix \"+\" P:11194 identity"),
  mBody("AbsI",
    "abs (system.nim:1373): abs has a real body (system.nim:1373-1381); walked; uNeg overflow", also = {msDefOverflow}),
  mBody("MinI",
    "min (system/comparisons.nim:238): if-expr body (comparisons.nim:238-265) walked, P:12762"),
  mBody("MaxI",
    "max (system/comparisons.nim:257): if-expr body (comparisons.nim:238-265) walked, P:12762"),
  mModelled("Succ",
    "succ (system/arithmetics.nim:1): P:12691 (+/- step; R1-02 enum/char/range bounds)", also = {msDefOverflow, msDefRange}),
  mModelled("Pred",
    "pred (system/arithmetics.nim:10): P:12691 (+/- step; R1-02 enum/char/range bounds)", also = {msDefOverflow, msDefRange}),
  mModelled("Inc",
    "+=,inc (system/arithmetics.nim:19): varParamMagics P:4278 (R8/S8bc arms); rangeMagics P:4026", also = {msVarStmt, msDefOverflow, msDefRange}),
  mModelled("Dec",
    "-=,dec (system/arithmetics.nim:31): varParamMagics P:4278 (R8/S8bc arms); rangeMagics P:4026", also = {msVarStmt, msDefOverflow, msDefRange}),
  mModelled("BitnotI",
    "bitnot,not (system/arithmetics.nim:63): nnkPrefix \"not\" on an int operand P:11186 (uNot; runtime picks bitnot by kind)"),
  mModelled("BitandI",
    "and,internalBitand (system/arithmetics.nim:196): infix and/or/xor bitwise branch (A2b) P:10620-10640 binBV"),
  mModelled("BitorI",
    "internalBitor,or (system/arithmetics.nim:206): infix and/or/xor bitwise branch (A2b) P:10620-10640 binBV"),
  mModelled("BitxorI",
    "internalBitxor,xor (system/arithmetics.nim:216): infix and/or/xor bitwise branch (A2b) P:10620-10640 binBV"),
  mModelled("ShlI",
    "shl (system/arithmetics.nim:161): RT:10641-10683 (S8ac count mask, S8w stamping); AshrI by name P:11869"),
  mModelled("ShrI",
    "shr (system/arithmetics.nim:129): RT:10641-10683 (S8ac count mask, S8w stamping); AshrI by name P:11869"),
  mModelled("AshrI",
    "ashr,shr (system/arithmetics.nim:135): RT:10641-10683 (S8ac count mask, S8w stamping); AshrI by name P:11869", also = {msCallSwitch}),
  mModelled("AddU",
    "+ (system/arithmetics.nim:269): uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero"),
  mModelled("SubU",
    "- (system/arithmetics.nim:276): uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero"),
  mModelled("MulU",
    "* (system/arithmetics.nim:283): uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero"),
  mModelled("DivU",
    "div (system/arithmetics.nim:290): uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero"),
  mModelled("ModU",
    "mod (system/arithmetics.nim:298): uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero"),
  mModelled("AddF64",
    "+ (system/arithmetics.nim:322): arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks)", also = {msDefFloat}),
  mModelled("SubF64",
    "- (system/arithmetics.nim:323): arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks)", also = {msDefFloat}),
  mModelled("MulF64",
    "* (system/arithmetics.nim:324): arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks)", also = {msDefFloat}),
  mModelled("DivF64",
    "/ (system/arithmetics.nim:325): arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks)", also = {msDefFloat}),
  mModelled("UnaryMinusF64",
    "- (system/arithmetics.nim:321): arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks)"),
  mModelled("UnaryPlusF64",
    "+ (system/arithmetics.nim:320): nnkPrefix \"+\" P:11194 identity"),
  mModelled("EqI",
    "== (system/comparisons.nim:159): lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned)"),
  mModelled("LeI",
    "<= (system/comparisons.nim:166): lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned)"),
  mModelled("LtI",
    "< (system/comparisons.nim:173): lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned)"),
  mModelled("LeU",
    "<= (system/comparisons.nim:180): lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned)"),
  mModelled("LtU",
    "< (system/comparisons.nim:187): lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned)"),
  mModelled("EqF64",
    "== (system/comparisons.nim:233): cmpFloat RT:8928 (IEEE: NaN != NaN)"),
  mModelled("LeF64",
    "<= (system/comparisons.nim:227): cmpFloat RT:8928 (IEEE: NaN != NaN)"),
  mModelled("LtF64",
    "< (system/comparisons.nim:230): cmpFloat RT:8928 (IEEE: NaN != NaN)"),
  mModelled("EqB",
    "== (system/comparisons.nim:27): lowerCmp bool branch RT:8915-8926"),
  mModelled("LeB",
    "<= (system/comparisons.nim:95): lowerCmp bool branch RT:8915-8926"),
  mModelled("LtB",
    "< (system/comparisons.nim:138): lowerCmp bool branch RT:8915-8926"),
  mModelled("EqCh",
    "== (system/comparisons.nim:25): char = itInt width 8 unsigned; cmpBV bvult"),
  mModelled("LeCh",
    "<= (system/comparisons.nim:69): char = itInt width 8 unsigned; cmpBV bvult"),
  mModelled("LtCh",
    "< (system/comparisons.nim:112): char = itInt width 8 unsigned; cmpBV bvult"),
  mModelled("EqEnum",
    "== (system/comparisons.nim:2): enum = itInt ordinal; cmpInt"),
  mModelled("LeEnum",
    "<= (system/comparisons.nim:56): enum = itInt ordinal; cmpInt"),
  mModelled("LtEnum",
    "< (system/comparisons.nim:99): enum = itInt ordinal; cmpInt"),
  mModelled("EqStr",
    "== (system/comparisons.nim:22): cmpString (runtime_strings) Z3 str.< on the byte model"),
  mModelled("LeStr",
    "<= (system/comparisons.nim:57): cmpString (runtime_strings) Z3 str.< on the byte model"),
  mModelled("LtStr",
    "< (system/comparisons.nim:100): cmpString (runtime_strings) Z3 str.< on the byte model"),
  mModelled("EqSet",
    "== (system/comparisons.nim:29): bitset infix P:10981-10996 (S8bq item 2) mkBitSet"),
  mModelled("LeSet",
    "<= (system/comparisons.nim:81): bitset infix P:10981-10996 (S8bq item 2) mkBitSet"),
  mModelled("LtSet",
    "< (system/comparisons.nim:124): bitset infix P:10981-10996 (S8bq item 2) mkBitSet"),
  mModelled("EqRef",
    "== (system/comparisons.nim:15): refEq (R5) via parseNilCompare P:11050 and lowerCmp"),
  mModelled("EqProc",
    "== (system/comparisons.nim:38): closureEq in lowerCmp for walker-built lambdas (pinned exact, K4b); a proc value with no lambda declines (ceUnsupportedHof)"),
  mUnverified("LePtr",
    "<= (system/comparisons.nim:96): ptr </<=: no arm by name; falls to lowerCmp else-branch cmpBV on svPtr -> expected feUnsupportedOp/eqBV ..."),
  mUnverified("LtPtr",
    "< (system/comparisons.nim:139): ptr </<=: no arm by name; falls to lowerCmp else-branch cmpBV on svPtr -> expected feUnsupportedOp/eqBV ..."),
  mModelled("EqCString",
    "== (system.nim:2796): the cstring operands cross as strings (nnkCStringToString) and compare on the byte model; the importc cmpStrings body is never walked (pinned exact, K4b)"),
  mModelled("Not",
    "not (system/basic_types.nim:76): P:11080-11180 (D1c short-circuit; A2b)"),
  mModelled("And",
    "and (system/basic_types.nim:79): P:11080-11180 (D1c short-circuit; A2b)"),
  mModelled("Or",
    "or (system/basic_types.nim:84): P:11080-11180 (D1c short-circuit; A2b)"),
  mModelled("Xor",
    "xor (system/basic_types.nim:89): P:11080-11180 (D1c short-circuit; A2b)"),
  mModelled("Chr",
    "chr (system.nim:728): P:11879 (RangeDefect via hidden range conv)", also = {msCallSwitch, msDefRange}),
  mModelled("Ord",
    "ord (system.nim:717): P:11874 (bool); other ordinals: identity through the conv arm P:12629", also = {msCallSwitch}),
  mModelled("High",
    "high (system.nim:205): types: lowHighIntLit P:5407 (int family) + ordinal fold; values: s.high S3 arm P:11642+"),
  mModelled("Low",
    "low (system.nim:283): types: lowHighIntLit P:5407 (int family) + ordinal fold; values: s.high S3 arm P:11642+"),
  mModelled("Default",
    "default (system.nim:916): P:11720 zeroValueForType"),
  mModelled("ZeroDefault",
    "zeroDefault (system.nim:27): P:11720 zeroValueForType"),
  mModelled("LengthStr",
    "len (system.nim:672): len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models)"),
  mModelled("LengthSeq",
    "len (system.nim:707): len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models)"),
  mModelled("LengthArray",
    "len (system.nim:698): len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models)"),
  mModelled("LengthOpenArray",
    "len,varargsLenImpl (system.nim:665): len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models)"),
  mModelled("Card",
    "card,len (system/setops.nim:42): P:12460 len/card on a bitset"),
  mModelled("SetLengthSeq",
    "setLen (system.nim:943): parseSetLen P:17705 (grow of Uninit declines)", also = {msVarStmt}),
  mModelled("SetLengthStr",
    "setLen (system.nim:974): parseSetLen P:17705 (grow of Uninit declines)", also = {msVarStmt}),
  mModelled("SetLengthSeqUninit",
    "setLenUninit (system.nim:959): parseSetLen P:17705 (grow of Uninit declines)", also = {msVarStmt}),
  mModelled("NewSeq",
    "newSeq (system.nim:614): P:9372-9389 (iekSeqNew)"),
  mModelled("NewSeqOfCap",
    "newSeqOfCap (system.nim:653): P:9372-9389 (iekSeqNew)"),
  mModelled("NewString",
    "newStringUninit,newString (system.nim:986): P:17880 (parseNewString)", also = {msNewString}),
  mModelled("NewStringOfCap",
    "newStringOfCap (system.nim:995): P:17880 (parseNewString)", also = {msNewString}),
  mModelled("ConStrStr",
    "& (system.nim:1002): & infix P:11000 iekStrConcat (itString both sides)"),
  mModelled("AppendStrCh",
    "add (system.nim:1030): varParamMagics P:4274-4277 (#145 arms, &=)"),
  mModelled("AppendStrStr",
    "&=,add (system.nim:1039): varParamMagics P:4274-4277 (#145 arms, &=)"),
  mModelled("AppendSeqElem",
    "add (system.nim:1156): varParamMagics P:4274-4277 (#145 arms, &=)"),
  mModelled("ArrGet",
    "[],arrGet (system.nim:371): index arms P:1894/16843 + IndexDefect fork"),
  mModelled("ArrPut",
    "[]=,arrPut (system.nim:373): index arms P:1894/16843 + IndexDefect fork"),
  mModelled("ArrToSeq",
    "@ (system.nim:900): nnkPrefix \"@\" P:11201 (bracket -> mkSeqLit; else openArrayView); EMPTY @[] of a non-seq class is a ..."),
  mModelled("OpenArrayToSeq",
    "@ (system.nim:1468): nnkPrefix \"@\" P:11201 (bracket -> mkSeqLit; else openArrayView); EMPTY @[] of a non-seq class is a ..."),
  mModelled("Slice",
    "toOpenArrayByte,toOpenArrayChar,toOpenArray (system.nim:2975): toOpenArray P:7278/7327/7949 (view arms; pinned exact, K4b)"),
  mModelled("DotDot",
    ".. (system.nim:426): ../..< in for/slice heads P:2862,12258; as a VALUE in call position: unsupported-infix decline P:11070"),
  mModelled("InSet",
    "contains (system/setops.nim:70): in/contains on a builtin set: parseBitSet* P:9697-9760 (S8bq)"),
  mModelled("Incl",
    "incl (system/setops.nim:1): varParamMagics P:4285; parseBitSetInclExcl P:9754"),
  mModelled("Excl",
    "excl (system/setops.nim:24): varParamMagics P:4285; parseBitSetInclExcl P:9754"),
  mModelled("PlusSet",
    "+ (system/setops.nim:60): bitset infix P:10981-10996 (S8bq item 2) mkBitSet"),
  mModelled("MinusSet",
    "- (system/setops.nim:65): bitset infix P:10981-10996 (S8bq item 2) mkBitSet"),
  mModelled("MulSet",
    "* (system/setops.nim:55): bitset infix P:10981-10996 (S8bq item 2) mkBitSet"),
  mDeclined("XorSet",
    "symmetricDifference (std/setutils.nim:80): symmetricDifference (std/setutils) is a bodiless magic -> stubBody decline P:21225 (\"has no symbolic model\")"),
  mModelled("BoolToStr",
    "$,repr (system/dollars.nim:47): parseToStr P:7444 (enum hole declines)"),
  mModelled("IntToStr",
    "$,repr (system/dollars.nim:11): parseToStr P:7444 (iekIntToStr)"),
  mModelled("Int64ToStr",
    "$,repr (system/dollars.nim:15): parseToStr P:7444 (iekIntToStr)"),
  mModelled("EnumToStr",
    "$,repr (system/dollars.nim:67): parseToStr P:7444 (enum hole declines)"),
  mModelled("CharToStr",
    "$ (system/dollars.nim:51): parseToStr P:7444 (enum hole declines)"),
  mModelled("StrToStr",
    "$ (system/dollars.nim:62): parseToStr P:7444 (enum hole declines)"),
  mDeclined("CStrToStr",
    "$,cstrToStrBuiltin (system/dollars.nim:58): parseToStr fall-through: \"$ of a <kind> operand is not modelled\""),
  mPartial("Repr",
    "repr (system.nim:1266): bool/enum/int via parseToStr; any other repr declines P:11850"),
  mModelled("New",
    "new,unsafeNew (system.nim:567): parseNew/parseUnsafeNew P:17756; new(p, finalizer) is NewFinalize", also = {msVarStmt}),
  mDeclined("NewFinalize",
    "new (system.nim:131): hasVarFormal decline in ensureProcRegistered P:21205; NOT listed in varParamMagics (generic reason text)"),
  mModelled("Swap",
    "swap (system.nim:1404): parseVarMagicStmt P:17813 (both read, then both written); other shapes decline", also = {msVarStmt}),
  mModelled("WasMoved",
    "=wasMoved,wasMoved (system.nim:161): P:17825 / parseMoveExpr P:17859 / P:11888", also = {msVarStmt}),
  mModelled("Move",
    "move (system.nim:169): P:17825 / parseMoveExpr P:17859 / P:11888"),
  mModelled("EnsureMove",
    "ensureMove (system.nim:175): P:17825 / parseMoveExpr P:17859 / P:11888", also = {msCallSwitch}),
  mModelled("Asgn",
    "=,=copy,=sink (system.nim:375): =/=copy/=sink as assignment P:17830; a user hook declines (S8cs)", also = {msVarStmt}),
  mNever("Destroy",
    "=destroy (system.nim:385): varParamMagics vmDeclined P:4289-4293"),
  mNever("Trace",
    "=trace (system.nim:416): varParamMagics vmDeclined P:4289-4293"),
  mNever("ShallowCopy",
    "shallowCopy (system.nim:360): varParamMagics vmDeclined P:4289-4293"),
  mModelled("Dup",
    "=dup (system.nim:404): =dup of a plain value type = copy P:11857 (pinned exact, K4b); a user-hooked object keeps the hook's own decline"),
  mModelled("IsNil",
    "isNil (system.nim:1455): P:11629 (S8bo)"),
  mModelled("Addr",
    "addr,unsafeAddr (system.nim:99): addr/unsafeAddr arms P:7706,8008,8404 (cluster R, S8ch); global in a walked callee declines (heUnsafeCast)"),
  mDeclined("DeepCopy",
    "deepCopy (system.nim:2768): stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen"),
  mDeclined("GCref",
    "GC_ref (system/gc_interface.nim:42): stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen"),
  mDeclined("GCunref",
    "GC_unref (system/gc_interface.nim:50): stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen"),
  mFolded("SizeOf",
    "sizeof (system.nim:578): semfold folds sizeof(T)/sizeof(x) to an nnkIntLit before getImpl; a size the compiler cannot fold (an ..."),
  mFolded("AlignOf",
    "alignof (system.nim:597): semfold folds sizeof(T)/sizeof(x) to an nnkIntLit before getImpl; a size the compiler cannot fold (an ..."),
  mFolded("OffsetOf",
    "offsetOfDotExpr (system.nim:600): semfold folds sizeof(T)/sizeof(x) to an nnkIntLit before getImpl; a size the compiler cannot fold (an ..."),
  mDeclined("GetTypeInfo",
    "getTypeInfo (system.nim:2033): stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen"),
  mDeclined("GetTypeInfoV2",
    "getDynamicTypeInfo (system/cyclebreaker.nim:152): stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen"),
  mModelled("Echo",
    "debugEcho,echo (system.nim:1743): OpaqueEffectfulProcs (stdlib_models.nim:86): body skipped, fresh result, path uncertain"),
  mModelled("Exit",
    "quit,rawQuit (system.nim:2474): isExitCall/parseExitCall P:7509 (path ends)"),
  mDeclined("ProcCall",
    "procCall (system.nim:2784): P:10019 (empty-body decline on its key)"),
  mUnverified("Finished",
    "finished (system.nim:2449): closure-iterator finished(it): has a body (discard); closure iterators themselves are outside the fragment -> ..."),
  mModelled("Of",
    "of (system.nim:850): parseOfTest P:10024 (S8bn item 7)"),
  mModelled("Fields",
    "fields (system/iterators.nim:284): a for over fields(o): the compiler unrolls it at semcheck (nnkStmtList per field) so the walker sees plain ..."),
  mModelled("FieldPairs",
    "fieldPairs (system/iterators.nim:309): a for over fields(o): the compiler unrolls it at semcheck (nnkStmtList per field) so the walker sees plain ..."),
  mDeclined("ParseBiggestFloat",
    "parseBiggestFloat (pure/parseutils.nim:587): var-formal magic in pure/parseutils -> hasVarFormal decline P:21205 (outside the system-only magicscan); ..."),
  mFolded("Is",
    "is (system.nim:770): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("TypeOf",
    "typeof (system.nim:57): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("TypeTrait",
    "$,and,arity,distinctBase,genericHead,hasDefaultValue,isNamedTuple,name,not,or,rangeBase,stripGenericParams,supportsCopyMem,tupleLen (system.nim:79): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("Defined",
    "defined (system/compilation.nim:36): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("Declared",
    "declared (system/compilation.nim:54): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("DeclaredInScope",
    "declaredInScope (system/compilation.nim:69): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("Compiles",
    "compiles (system/compilation.nim:73): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("AstToStr",
    "astToStr (system/compilation.nim:83): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("CompileOption",
    "compileOption (system/compilation.nim:116): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("CompileOptionArg",
    "compileOption (system/compilation.nim:131): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("Slurp",
    "slurp,staticRead (system/compilation.nim:159): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("StaticExec",
    "gorge,staticExec (system/compilation.nim:174): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("RunnableExamples",
    "runnableExamples (system/compilation.nim:87): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mFolded("InstantiationInfo",
    "instantiationInfo (system.nim:1585): compile-time only: semcheck folds them; never a call node in the typed body getImpl returns"),
  mNever("Spawn",
    "pinnedSpawn,spawn (pure/concurrency/threadpool.nim:457): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("Parallel",
    "parallel (pure/concurrency/threadpool.nim:484): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("OmpParFor",
    "|| (system/iterators_1.nim:147): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("Isolate",
    "isolate (std/isolation.nim:31): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("Unown",
    "unown (system.nim:818): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("PrivateAccess",
    "privateAccess (std/importutils.nim:23): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("Plugin",
    "iterToProc,locals (system.nim:2739): threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined ..."),
  mNever("Implies",
    "-> (std/logic.nim:4): DrNim contract magics; not valid in ordinary code"),
  mNever("Iff",
    "<-> (std/logic.nim:5): DrNim contract magics; not valid in ordinary code"),
  mNever("Forall",
    "forall (std/logic.nim:7): DrNim contract magics; not valid in ordinary code"),
  mNever("Exists",
    "exists (std/logic.nim:8): DrNim contract magics; not valid in ordinary code"),
  mNever("Old",
    "old (std/logic.nim:10): DrNim contract magics; not valid in ordinary code"),
  mNever("StrToIdent",
    "ident,newIdentNode,toNimIdent (core/macros.nim:157): std/macros NimNode API: compile-time only"),
  mNever("EqIdent",
    "==,eqIdent (core/macros.nim:161): std/macros NimNode API: compile-time only"),
  mNever("EqNimrodNode",
    "== (core/macros.nim:165): std/macros NimNode API: compile-time only"),
  mNever("SameNodeType",
    "sameType (core/macros.nim:175): std/macros NimNode API: compile-time only"),
  mNever("NLen",
    "len (core/macros.nim:180): std/macros NimNode API: compile-time only"),
  mNever("NChild",
    "[] (core/macros.nim:183): std/macros NimNode API: compile-time only"),
  mNever("NSetChild",
    "[]= (core/macros.nim:201): std/macros NimNode API: compile-time only"),
  mNever("NAdd",
    "add (core/macros.nim:223): std/macros NimNode API: compile-time only"),
  mNever("NAddMultiple",
    "add (core/macros.nim:228): std/macros NimNode API: compile-time only"),
  mNever("NDel",
    "del (core/macros.nim:233): std/macros NimNode API: compile-time only"),
  mNever("NKind",
    "kind (core/macros.nim:236): std/macros NimNode API: compile-time only"),
  mNever("NIntVal",
    "intVal (core/macros.nim:239): std/macros NimNode API: compile-time only"),
  mNever("NFloatVal",
    "floatVal (core/macros.nim:242): std/macros NimNode API: compile-time only"),
  mNever("NSymKind",
    "symKind (core/macros.nim:246): std/macros NimNode API: compile-time only"),
  mNever("GetImpl",
    "getImpl (core/macros.nim:247): std/macros NimNode API: compile-time only"),
  mNever("NStrVal",
    "$,strVal (core/macros.nim:249): std/macros NimNode API: compile-time only"),
  mNever("NIdent",
    "ident (core/macros.nim:257): std/macros NimNode API: compile-time only"),
  mNever("NSymbol",
    "symbol (core/macros.nim:260): std/macros NimNode API: compile-time only"),
  mNever("GetImplTransf",
    "getImplTransformed (core/macros.nim:276): std/macros NimNode API: compile-time only"),
  mNever("SymOwner",
    "owner (core/macros.nim:282): std/macros NimNode API: compile-time only"),
  mNever("SymIsInstantiationOf",
    "isInstantiationOf (core/macros.nim:293): std/macros NimNode API: compile-time only"),
  mNever("NGetType",
    "getTypeImpl,getTypeInstSkipAlias,getTypeInst,getType,typeKind (core/macros.nim:298): std/macros NimNode API: compile-time only"),
  mNever("NSigHash",
    "signatureHash (core/macros.nim:357): std/macros NimNode API: compile-time only"),
  mNever("NSetIntVal",
    "intVal= (core/macros.nim:373): std/macros NimNode API: compile-time only"),
  mNever("NSetFloatVal",
    "floatVal= (core/macros.nim:374): std/macros NimNode API: compile-time only"),
  mNever("NSetSymbol",
    "symbol= (core/macros.nim:378): std/macros NimNode API: compile-time only"),
  mNever("NSetIdent",
    "ident= (core/macros.nim:381): std/macros NimNode API: compile-time only"),
  mNever("NSetStrVal",
    "strVal= (core/macros.nim:386): std/macros NimNode API: compile-time only"),
  mNever("NNewNimNode",
    "newNimNode (core/macros.nim:396): std/macros NimNode API: compile-time only"),
  mNever("NCopyNimNode",
    "copyNimNode (core/macros.nim:405): std/macros NimNode API: compile-time only"),
  mNever("NCopyNimTree",
    "copyNimTree (core/macros.nim:418): std/macros NimNode API: compile-time only"),
  mNever("NError",
    "error,internalErrorFlag (core/macros.nim:436): std/macros NimNode API: compile-time only"),
  mNever("NWarning",
    "warning (core/macros.nim:441): std/macros NimNode API: compile-time only"),
  mNever("NHint",
    "hint (core/macros.nim:444): std/macros NimNode API: compile-time only"),
  mNever("NBindSym",
    "bindSym (core/macros.nim:495): std/macros NimNode API: compile-time only"),
  mNever("NGenSym",
    "genSym (core/macros.nim:509): std/macros NimNode API: compile-time only"),
  mNever("NCallSite",
    "callsite (core/macros.nim:514): std/macros NimNode API: compile-time only"),
  mNever("NLineInfo",
    "copyLineInfo,getColumn,getFile,getLine,setColumn,setFile,setLine (core/macros.nim:538): std/macros NimNode API: compile-time only"),
  mNever("ParseExprToAst",
    "internalParseExpr (core/macros.nim:569): std/macros NimNode API: compile-time only"),
  mNever("ParseStmtToAst",
    "internalParseStmt (core/macros.nim:572): std/macros NimNode API: compile-time only"),
  mNever("ExpandToAst",
    "getAst (core/macros.nim:595): std/macros NimNode API: compile-time only"),
  mNever("QuoteAst",
    "quote (core/macros.nim:604): std/macros NimNode API: compile-time only"),
  mNever("NodeId",
    "nodeID (core/macros.nim:1534): std/macros NimNode API: compile-time only"),
  mNever("NSizeOf",
    "getAlign,getOffset,getSize (core/macros.nim:1763): std/macros NimNode API: compile-time only"),
  mNever("NccValue",
    "value (core/macrocache.nim:60): std/macrocache: compile-time only"),
  mNever("NccInc",
    "inc (core/macrocache.nim:71): std/macrocache: compile-time only"),
  mNever("NcsAdd",
    "add (core/macrocache.nim:81): std/macrocache: compile-time only"),
  mNever("NcsIncl",
    "incl (core/macrocache.nim:94): std/macrocache: compile-time only"),
  mNever("NcsLen",
    "len (core/macrocache.nim:109): std/macrocache: compile-time only"),
  mNever("NcsAt",
    "[] (core/macrocache.nim:123): std/macrocache: compile-time only"),
  mNever("NctPut",
    "[]= (core/macrocache.nim:162): std/macrocache: compile-time only"),
  mNever("NctLen",
    "len (core/macrocache.nim:178): std/macrocache: compile-time only"),
  mNever("NctGet",
    "[] (core/macrocache.nim:188): std/macrocache: compile-time only"),
  mNever("NctHasNext",
    "hasNext (core/macrocache.nim:226): std/macrocache: compile-time only"),
  mNever("NctNext",
    "next (core/macrocache.nim:227): std/macrocache: compile-time only"),
  # Magics the research table (routines only) lacks, found by the lib-wide
  # guard: a type's magic is classified by the type-class axis and is never
  # a callee; a compile-time constant is folded before the walker sees it.
  mNever("OpenArray",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Type",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Array",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Range",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Set",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("UncheckedArray",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Seq",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Varargs",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Static",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("VoidType",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("BuiltinType",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Bool",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Exception",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("PNimrodNode",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mNever("Nil",
    "a type's magic pragma (system.nim, basic_types.nim): a type, never a callee; the type-class axis classifies it"),
  mFolded("HostCPU",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("CpuEndian",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("BuildCPU",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("HostOS",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("AppType",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("BuildOS",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("IsMainModule",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("CompileDate",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("Nimvm",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),
  mFolded("CompileTime",
    "a compile-time constant or switch (system/compilation.nim, system.nim): the compiler folds it before getImpl"),

  # STY-05 (HRV-27): a math routine recognised by name, not a TMagic member.
  (key: "nextafter", row: refused[MagicSite, MagicModel](some(feUnsupportedOp),
    "`nextafter` (std/math): no SMT-LIB FP-theory primitive, a documented " &
    "Z3 bound (`mathFpDeferredOps`)", intent = iNever, never = nrTheory))])

proc admitMagic*(magic: string; site: MagicSite): Admit[MagicModel] =
  ## The magic axis, for every magic. The `var`-parameter subset is
  ## `dsl_parser.admitVarMagic`, which agrees.
  magicAxis.admit(magic, site)

const magicDefectSites* = {msDefOverflow, msDefDivZero, msDefRange, msDefFloat}
  ## K4a-guard. The sites that are a defect property of a row, read by the
  ## opaque-call defect scan with `admitMagic`; no `case` dispatches on them.

const magicDispatchSites* = {msVarStmt, msCallSwitch, msInfix, msNewString}
  ## The sites whose `case` goes through `dispatchMagic`. `msArm` names no
  ## place and `msProcRegister` is a single decision read with `admitMagic`.

var dispatchedSites {.compileTime.}: set[MagicSite]
  ## The sites a `dispatchMagic` expansion has covered, in this compilation.

proc dispatchedMagicSites*(): set[MagicSite] {.compileTime.} = dispatchedSites

template lowerMagic*(proof: Admit[MagicModel] | Admit[StdlibBody];
                     body: untyped): untyped =
  ## RFC-0016 ADM-IR (section 8.1). The one place a magic arm's lowering runs:
  ## `dispatchMagic` wraps every `of` arm's body in it, with the proof the
  ## arm's row gives at the site (`admitMagic`, or `admitStdlibBody` for an
  ## unsigned operator). The lowering does not run on a declined proof, so a
  ## magic's node is built only for a magic the table admits; another axis's
  ## proof is a type error. The census in `tests/tsymex_0016_admir.nim`
  ## counts the magic arms outside a dispatch.
  doAssert proof.admitted, "lowerMagic: " & proof.decline[1]
  body

template magicIs*(magic: string; name: static string): bool =
  ## ADM-IR. An expression-form read of a magic's name: `magic == name`, with
  ## `name` checked against the table at compile time (a name with no row does
  ## not compile), so no site spells a magic the table does not know.
  static: doAssert magicAxis.hasRow(name), "magicIs: no row for " & name
  magic == name

template magicIn*(magic: string; names: static seq[string]): bool =
  ## `magicIs` over a group.
  static:
    for nm in names: doAssert magicAxis.hasRow(nm), "magicIn: no row for " & nm
  magic in names

template whenMagic*(magic: string; name: static string; body: untyped) =
  ## ADM-IR. The expression-form twin of a `dispatchMagic` arm: `body` runs
  ## when `magic` is `name`, under that row's proof at `msArm`
  ## (`lowerMagic`), so a node is built only for a magic the table admits.
  if magicIs(magic, name):
    lowerMagic(admitMagic(magic, msArm), body)

template whenMagicIn*(magic: string; names: static seq[string];
                      body: untyped) =
  ## `whenMagic` over a group of magics that share one lowering.
  if magicIn(magic, names):
    lowerMagic(admitMagic(magic, msArm), body)

template declinedMagic*(proof: Admit[MagicModel]; body: untyped) =
  ## ADM-IR. A site that stands for a magic's DECLINE, not its model: `body`
  ## builds the carrier of the decline the callee's registration recorded.
  ## It runs only under a proof that is not admitted, so a magic that later
  ## gains a model cannot keep a stale marker.
  doAssert not proof.admitted, "declinedMagic: the row is admitted"
  body

macro dispatchMagic*(site: static MagicSite; body: untyped): untyped =
  ## RFC-0016 K4a-dispatch (section 8.1). `body` is the site's `case` over a
  ## magic's name. The expansion is that `case`, after the table has been
  ## read at compile time:
  ##   * every `of` string must have a row in `magicAxis` admitted at `site`;
  ##   * every row admitted at `site` must have an `of` arm;
  ##   * the `else` is the decline (the name is refused, absent, or admitted
  ##     elsewhere), and must exist;
  ##   * a site is expanded once: a second expansion is an error, so
  ##     `dispatchedMagicSites()` is a registry of covered sites.
  if site notin magicDispatchSites:
    error("dispatchMagic: " & $site & " is not a dispatched site", body)
  if site in dispatchedSites:
    error("dispatchMagic: " & $site & " is dispatched twice", body)
  let hasStd = site in {msInfix, msCallSwitch}
  let stdlibSite = if site == msInfix: ssInfix else: ssCallSwitch
  var cs = body
  while cs.kind in {nnkStmtList, nnkStmtListExpr} and cs.len == 1: cs = cs[0]
  if cs.kind != nnkCaseStmt:
    error("dispatchMagic: the body is a `case` over the magic's name", body)
  var arms: seq[string]
  var hasElse = false
  for i in 1 ..< cs.len:
    let br = cs[i]
    if br.kind == nnkElse: hasElse = true
    else:
      for j in 0 ..< br.len - 1:
        if br[j].kind notin {nnkStrLit .. nnkTripleStrLit}:
          error("dispatchMagic: an arm names a magic by a string literal", br[j])
        let a = br[j].strVal
        if a in arms:
          error("dispatchMagic: duplicate arm `" & a & "`", br[j])
        arms.add a
        if hasStd and stdlibAxis.hasRow(unsignedOpKey(a)):
          # K4c: a `system` routine (the unsigned operators), not a magic.
          if not stdlibAxis.admit(unsignedOpKey(a), stdlibSite).admitted:
            error("dispatchMagic: arm `" & a & "` has a stdlib row that is " &
                  "not admitted at " & $stdlibSite, br[j])
        elif not magicAxis.hasRow(a):
          error("dispatchMagic: arm `" & a & "` has no row in magicAxis or " &
                "stdlibAxis", br[j])
        elif not magicAxis.admit(a, site).admitted:
          error("dispatchMagic: arm `" & a & "` has a row that is not " &
                "admitted at " & $site, br[j])
  if not hasElse:
    error("dispatchMagic: the case needs an `else`, the decline", body)
  for k in magicAxis.keysAt(site):
    if k notin arms:
      error("dispatchMagic: the row `" & k & "` is admitted at " & $site &
            " and has no arm", body)
  for k in (if hasStd: toSeq(stdlibAxis.keysAt(stdlibSite)) else: @[]):
    if k notin arms.mapIt(unsignedOpKey(it)):
      error("dispatchMagic: the stdlib row `" & k & "` is admitted at " &
            $stdlibSite & " and has no arm", body)
  # ADM-IR: each arm's lowering runs under the proof of its row at the site.
  for i in 1 ..< cs.len:
    let br = cs[i]
    if br.kind == nnkElse: continue
    var arm = br[^1]
    for j in countdown(br.len - 2, 0):
      let nm = br[j].strVal
      let proof =
        if hasStd and stdlibAxis.hasRow(unsignedOpKey(nm)):
          newCall(bindSym"admitStdlibBody", newLit(unsignedOpKey(nm)),
                  newLit(stdlibSite))
        else:
          newCall(bindSym"admitMagic", newLit(nm), newLit(site))
      arm = newCall(bindSym"lowerMagic", proof, arm)
    br[^1] = arm
  dispatchedSites.incl site
  result = cs
