
#### Integer arithmetic

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| AddI | `+` | system/arithmetics.nim:75 | modelled | binopForInfix P:3291; lowerArith RT:8800-8910 (overflowConds S8bv; width wrap S8w) | s8cb_magics, s8g_models, s8ac_remainder; p_c1 (ran) |  |
| SubI | `-` | system/arithmetics.nim:82 | modelled | binopForInfix P:3291; lowerArith RT:8800-8910 (overflowConds S8bv; width wrap S8w) | s8cb_magics, s8g_models, s8ac_remainder; p_c1 (ran) |  |
| MulI | `*` | system/arithmetics.nim:89 | modelled | binopForInfix P:3291; lowerArith RT:8800-8910 (overflowConds S8bv; width wrap S8w) | s8cb_magics, s8g_models, s8ac_remainder; p_c1 (ran) |  |
| DivI | `div` | system/arithmetics.nim:96 | modelled | RT:8856-8870 divLowByMinusOne (div OverflowDefect; mod = C trap at 32/64 bits); divisorIsZero RT:8801 | s8i_models; p_c1/p_c1b (ran) | C-01 (mod by LITERAL -1 differs) |
| ModI | `mod` | system/arithmetics.nim:113 | modelled | RT:8856-8870 divLowByMinusOne (div OverflowDefect; mod = C trap at 32/64 bits); divisorIsZero RT:8801 | s8i_models; p_c1/p_c1b (ran) | C-01 (mod by LITERAL -1 differs) |
| UnaryMinusI | `-` | system/arithmetics.nim:56 | modelled | nnkPrefix "-" P:11196 (uNeg); overflowMagics P:4020 | s8g_models (-low(int)) |  |
| UnaryMinusI64 | `-` | system/arithmetics.nim:61 | modelled | nnkPrefix "-" P:11196 (uNeg); overflowMagics P:4020 | s8g_models (-low(int)) |  |
| UnaryPlusI | `+` | system/arithmetics.nim:49 | modelled | nnkPrefix "+" P:11194 identity | none |  |
| AbsI | `abs` | system.nim:1373 | body | `abs` has a real body (system.nim:1373-1381); walked; uNeg overflow | s8g_models (abs(low)) |  |
| MinI | `min` | system/comparisons.nim:238 | body | if-expr body (comparisons.nim:238-265) walked, P:12762 | p_c4 (ran, minmax) |  |
| MaxI | `max` | system/comparisons.nim:257 | body | if-expr body (comparisons.nim:238-265) walked, P:12762 | p_c4 (ran, minmax) |  |
| Succ | `succ` | system/arithmetics.nim:1 | modelled | P:12691 (+/- step; R1-02 enum/char/range bounds) | s8cb_magics; p_c1 su/suc (ran, uint8); p_c5 (ran, holey enum) |  |
| Pred | `pred` | system/arithmetics.nim:10 | modelled | P:12691 (+/- step; R1-02 enum/char/range bounds) | s8cb_magics; p_c1 su/suc (ran, uint8); p_c5 (ran, holey enum) |  |
| Inc | `+=`,`inc` | system/arithmetics.nim:19 | modelled | varParamMagics P:4278 (R8/S8bc arms); rangeMagics P:4026 | s8bl_magics; p_c1 incu8 (ran) |  |
| Dec | `-=`,`dec` | system/arithmetics.nim:31 | modelled | varParamMagics P:4278 (R8/S8bc arms); rangeMagics P:4026 | s8bl_magics; p_c1 incu8 (ran) |  |
| BitnotI | `bitnot`,`not` | system/arithmetics.nim:63 | modelled | nnkPrefix "not" on an int operand P:11186 (uNot; runtime picks bitnot by kind) | p_c1 bn/bnu (ran) |  |
| BitandI | `and`,`internalBitand` | system/arithmetics.nim:196 | modelled | infix and/or/xor bitwise branch (A2b) P:10620-10640 binBV | phase16 A2b tests |  |
| BitorI | `internalBitor`,`or` | system/arithmetics.nim:206 | modelled | infix and/or/xor bitwise branch (A2b) P:10620-10640 binBV | phase16 A2b tests |  |
| BitxorI | `internalBitxor`,`xor` | system/arithmetics.nim:216 | modelled | infix and/or/xor bitwise branch (A2b) P:10620-10640 binBV | phase16 A2b tests |  |
| ShlI | `shl` | system/arithmetics.nim:161 | modelled | RT:10641-10683 (S8ac count mask, S8w stamping); AshrI by name P:11869 | s8ac_remainder, s8cb_magics |  |
| ShrI | `shr` | system/arithmetics.nim:129 | modelled | RT:10641-10683 (S8ac count mask, S8w stamping); AshrI by name P:11869 | s8ac_remainder, s8cb_magics |  |
| AshrI | `ashr`,`shr` | system/arithmetics.nim:135 | modelled | RT:10641-10683 (S8ac count mask, S8w stamping); AshrI by name P:11869 | s8ac_remainder, s8cb_magics |  |

#### Unsigned arithmetic

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| AddU | `+` | system/arithmetics.nim:269 | modelled | uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero | p_c1 incu8/u64div (ran); s8cb (+% family) |  |
| SubU | `-` | system/arithmetics.nim:276 | modelled | uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero | p_c1 incu8/u64div (ran); s8cb (+% family) |  |
| MulU | `*` | system/arithmetics.nim:283 | modelled | uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero | p_c1 incu8/u64div (ran); s8cb (+% family) |  |
| DivU | `div` | system/arithmetics.nim:290 | modelled | uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero | p_c1 incu8/u64div (ran); s8cb (+% family) |  |
| ModU | `mod` | system/arithmetics.nim:298 | modelled | uint operands: lowerArith wrapIntToWidth RT:8890 (unsigned always wraps); divisorIsZero | p_c1 incu8/u64div (ran); s8cb (+% family) |  |

#### Float arithmetic

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| AddF64 | `+` | system/arithmetics.nim:322 | modelled | arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks) | phase15 F3; s8be_remainder |  |
| SubF64 | `-` | system/arithmetics.nim:323 | modelled | arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks) | phase15 F3; s8be_remainder |  |
| MulF64 | `*` | system/arithmetics.nim:324 | modelled | arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks) | phase15 F3; s8be_remainder |  |
| DivF64 | `/` | system/arithmetics.nim:325 | modelled | arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks) | phase15 F3; s8be_remainder |  |
| UnaryMinusF64 | `-` | system/arithmetics.nim:321 | modelled | arithFloat RT:8905 (Z3 FP); floatArithMagics P:4029 (S8be float checks) | phase15 F3; s8be_remainder |  |
| UnaryPlusF64 | `+` | system/arithmetics.nim:320 | modelled | nnkPrefix "+" P:11194 identity | none |  |

#### Comparisons

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| EqI | `==` | system/comparisons.nim:159 | modelled | lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned) | p_c1 u64cmp (ran) |  |
| LeI | `<=` | system/comparisons.nim:166 | modelled | lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned) | p_c1 u64cmp (ran) |  |
| LtI | `<` | system/comparisons.nim:173 | modelled | lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned) | p_c1 u64cmp (ran) |  |
| LeU | `<=` | system/comparisons.nim:180 | modelled | lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned) | p_c1 u64cmp (ran) |  |
| LtU | `<` | system/comparisons.nim:187 | modelled | lowerCmp RT:8911 (cmpInt / cmpBV signed-vs-unsigned) | p_c1 u64cmp (ran) |  |
| EqF64 | `==` | system/comparisons.nim:233 | modelled | cmpFloat RT:8928 (IEEE: NaN != NaN) | phase15 F2/F4 |  |
| LeF64 | `<=` | system/comparisons.nim:227 | modelled | cmpFloat RT:8928 (IEEE: NaN != NaN) | phase15 F2/F4 |  |
| LtF64 | `<` | system/comparisons.nim:230 | modelled | cmpFloat RT:8928 (IEEE: NaN != NaN) | phase15 F2/F4 |  |
| EqB | `==` | system/comparisons.nim:27 | modelled | lowerCmp bool branch RT:8915-8926 | none (read) |  |
| LeB | `<=` | system/comparisons.nim:95 | modelled | lowerCmp bool branch RT:8915-8926 | none (read) |  |
| LtB | `<` | system/comparisons.nim:138 | modelled | lowerCmp bool branch RT:8915-8926 | none (read) |  |
| EqCh | `==` | system/comparisons.nim:25 | modelled | char = itInt width 8 unsigned; cmpBV bvult | p_c1 chhi/chhi2 (ran) |  |
| LeCh | `<=` | system/comparisons.nim:69 | modelled | char = itInt width 8 unsigned; cmpBV bvult | p_c1 chhi/chhi2 (ran) |  |
| LtCh | `<` | system/comparisons.nim:112 | modelled | char = itInt width 8 unsigned; cmpBV bvult | p_c1 chhi/chhi2 (ran) |  |
| EqEnum | `==` | system/comparisons.nim:2 | modelled | enum = itInt ordinal; cmpInt | s8cb_tostr (enum eq); p_c5 (ran) |  |
| LeEnum | `<=` | system/comparisons.nim:56 | modelled | enum = itInt ordinal; cmpInt | s8cb_tostr (enum eq); p_c5 (ran) |  |
| LtEnum | `<` | system/comparisons.nim:99 | modelled | enum = itInt ordinal; cmpInt | s8cb_tostr (enum eq); p_c5 (ran) |  |
| EqStr | `==` | system/comparisons.nim:22 | modelled | cmpString (runtime_strings) Z3 str.< on the byte model | p_c3 strcmp (ran) |  |
| LeStr | `<=` | system/comparisons.nim:57 | modelled | cmpString (runtime_strings) Z3 str.< on the byte model | p_c3 strcmp (ran) |  |
| LtStr | `<` | system/comparisons.nim:100 | modelled | cmpString (runtime_strings) Z3 str.< on the byte model | p_c3 strcmp (ran) |  |
| EqSet | `==` | system/comparisons.nim:29 | modelled | bitset infix P:10981-10996 (S8bq item 2) mkBitSet | s8bq tests; s8cd |  |
| LeSet | `<=` | system/comparisons.nim:81 | modelled | bitset infix P:10981-10996 (S8bq item 2) mkBitSet | s8bq tests; s8cd |  |
| LtSet | `<` | system/comparisons.nim:124 | modelled | bitset infix P:10981-10996 (S8bq item 2) mkBitSet | s8bq tests; s8cd |  |
| EqRef | `==` | system/comparisons.nim:15 | modelled | refEq (R5) via parseNilCompare P:11050 and lowerCmp | phase15 R5; s8bo_nil |  |
| EqProc | `==` | system/comparisons.nim:38 | partial | closureEq in lowerCmp for walker-built lambdas; a proc value with no lambda declines (ceUnsupportedHof) | none | PRC-13 |
| LePtr | `<=` | system/comparisons.nim:96 | unverified | ptr `<`/`<=`: no arm by name; falls to lowerCmp else-branch cmpBV on svPtr -> expected feUnsupportedOp/eqBV fault; NOT probed | none | C-10 (suspected crash) |
| LtPtr | `<` | system/comparisons.nim:139 | unverified | ptr `<`/`<=`: no arm by name; falls to lowerCmp else-branch cmpBV on svPtr -> expected feUnsupportedOp/eqBV fault; NOT probed | none | C-10 (suspected crash) |
| EqCString | `==` | system.nim:2796 | body | `==`(cstring) body calls cmpStrings (importc) -> isBodilessForeign decline (S8b) | none (read) |  |

#### Boolean

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| Not | `not` | system/basic_types.nim:76 | modelled | P:11080-11180 (D1c short-circuit; A2b) | phase16 D1c |  |
| And | `and` | system/basic_types.nim:79 | modelled | P:11080-11180 (D1c short-circuit; A2b) | phase16 D1c |  |
| Or | `or` | system/basic_types.nim:84 | modelled | P:11080-11180 (D1c short-circuit; A2b) | phase16 D1c |  |
| Xor | `xor` | system/basic_types.nim:89 | modelled | P:11080-11180 (D1c short-circuit; A2b) | phase16 D1c |  |

#### Conversions / ordinals

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| Chr | `chr` | system.nim:728 | modelled | P:11879 (RangeDefect via hidden range conv) | s8cb_magics |  |
| Ord | `ord` | system.nim:717 | modelled | P:11874 (bool); other ordinals: identity through the conv arm P:12629 | s8cb_magics |  |
| High | `high` | system.nim:205 | modelled | types: lowHighIntLit P:5407 (int family) + ordinal fold; values: `s.high` S3 arm P:11642+ | p_c1 hl (ran: char/uint8/int8/enum) |  |
| Low | `low` | system.nim:283 | modelled | types: lowHighIntLit P:5407 (int family) + ordinal fold; values: `s.high` S3 arm P:11642+ | p_c1 hl (ran: char/uint8/int8/enum) |  |
| Default | `default` | system.nim:916 | modelled | P:11720 zeroValueForType | p_c6 dflt (ran) |  |
| ZeroDefault | `zeroDefault` | system.nim:27 | modelled | P:11720 zeroValueForType | p_c6 dflt (ran) |  |

#### Length / containers

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| LengthStr | `len` | system.nim:672 | modelled | len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models) | phase5/S3 suites |  |
| LengthSeq | `len` | system.nim:707 | modelled | len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models) | phase5/S3 suites |  |
| LengthArray | `len` | system.nim:698 | modelled | len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models) | phase5/S3 suites |  |
| LengthOpenArray | `len`,`varargsLenImpl` | system.nim:665 | modelled | len arms P:12460 and smkSeqLen/smkStrLen (stdlib_models) | phase5/S3 suites |  |
| Card | `card`,`len` | system/setops.nim:42 | modelled | P:12460 `len`/`card` on a bitset | p_c1 card3/card2 (ran) |  |
| SetLengthSeq | `setLen` | system.nim:943 | modelled | parseSetLen P:17705 (grow of Uninit declines) | s8bl_setlen |  |
| SetLengthStr | `setLen` | system.nim:974 | modelled | parseSetLen P:17705 (grow of Uninit declines) | s8bl_setlen |  |
| SetLengthSeqUninit | `setLenUninit` | system.nim:959 | modelled | parseSetLen P:17705 (grow of Uninit declines) | s8bl_setlen |  |
| NewSeq | `newSeq` | system.nim:614 | modelled | P:9372-9389 (iekSeqNew) | s8bc |  |
| NewSeqOfCap | `newSeqOfCap` | system.nim:653 | modelled | P:9372-9389 (iekSeqNew) | s8bc |  |
| NewString | `newStringUninit`,`newString` | system.nim:986 | modelled | P:17880 (parseNewString) | s8cl_strings |  |
| NewStringOfCap | `newStringOfCap` | system.nim:995 | modelled | P:17880 (parseNewString) | s8cl_strings |  |
| ConStrStr | `&` | system.nim:1002 | modelled | `&` infix P:11000 iekStrConcat (itString both sides) | cluster S |  |
| AppendStrCh | `add` | system.nim:1030 | modelled | varParamMagics P:4274-4277 (#145 arms, `&=`) | s8bl_seqops |  |
| AppendStrStr | `&=`,`add` | system.nim:1039 | modelled | varParamMagics P:4274-4277 (#145 arms, `&=`) | s8bl_seqops |  |
| AppendSeqElem | `add` | system.nim:1156 | modelled | varParamMagics P:4274-4277 (#145 arms, `&=`) | s8bl_seqops |  |
| ArrGet | `[]`,`arrGet` | system.nim:371 | modelled | index arms P:1894/16843 + IndexDefect fork | phase4; s8bz |  |
| ArrPut | `[]=`,`arrPut` | system.nim:373 | modelled | index arms P:1894/16843 + IndexDefect fork | phase4; s8bz |  |
| ArrToSeq | `@` | system.nim:900 | modelled | nnkPrefix "@" P:11201 (bracket -> mkSeqLit; else openArrayView); EMPTY `@[]` of a non-seq class is a compile-time error() P:11206 | none | C-12 (crash, suspected) |
| OpenArrayToSeq | `@` | system.nim:1468 | modelled | nnkPrefix "@" P:11201 (bracket -> mkSeqLit; else openArrayView); EMPTY `@[]` of a non-seq class is a compile-time error() P:11206 | none | C-12 (crash, suspected) |
| Slice | `toOpenArrayByte`,`toOpenArrayChar`,`toOpenArray` | system.nim:2975 | partial | toOpenArray P:7278/7327/7949 (view arms); other shapes decline | s8cg | PRC-29 |
| DotDot | `..` | system.nim:426 | modelled | `..`/`..<` in for/slice heads P:2862,12258; as a VALUE in call position: unsupported-infix decline P:11070 | v64 |  |

#### Builtin set

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| InSet | `contains` | system/setops.nim:70 | modelled | `in`/`contains` on a builtin set: parseBitSet* P:9697-9760 (S8bq) | s8bq |  |
| Incl | `incl` | system/setops.nim:1 | modelled | varParamMagics P:4285; parseBitSetInclExcl P:9754 | p_c1 cardc (ran) |  |
| Excl | `excl` | system/setops.nim:24 | modelled | varParamMagics P:4285; parseBitSetInclExcl P:9754 | p_c1 cardc (ran) |  |
| PlusSet | `+` | system/setops.nim:60 | modelled | bitset infix P:10981-10996 (S8bq item 2) mkBitSet | s8bq tests; s8cd |  |
| MinusSet | `-` | system/setops.nim:65 | modelled | bitset infix P:10981-10996 (S8bq item 2) mkBitSet | s8bq tests; s8cd |  |
| MulSet | `*` | system/setops.nim:55 | modelled | bitset infix P:10981-10996 (S8bq item 2) mkBitSet | s8bq tests; s8cd |  |
| XorSet | `symmetricDifference` | std/setutils.nim:80 | declined | `symmetricDifference` (std/setutils) is a bodiless magic -> stubBody decline P:21225 ("has no symbolic model") | none | PRC-04 family |

#### Strings: $ and repr

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| BoolToStr | `$`,`repr` | system/dollars.nim:47 | modelled | parseToStr P:7444 (enum hole declines) | s8cb_tostr (SND-02..04); p_c5 (ran) | SND-03/04 |
| EnumToStr | `$`,`repr` | system/dollars.nim:67 | modelled | parseToStr P:7444 (enum hole declines) | s8cb_tostr (SND-02..04); p_c5 (ran) | SND-03/04 |
| CharToStr | `$` | system/dollars.nim:51 | modelled | parseToStr P:7444 (enum hole declines) | s8cb_tostr (SND-02..04); p_c5 (ran) | SND-03/04 |
| StrToStr | `$` | system/dollars.nim:62 | modelled | parseToStr P:7444 (enum hole declines) | s8cb_tostr (SND-02..04); p_c5 (ran) | SND-03/04 |
| CStrToStr | `$`,`cstrToStrBuiltin` | system/dollars.nim:58 | declined | parseToStr fall-through: "`$` of a <kind> operand is not modelled" | p_c6 dcs (ran) |  |
| Repr | `repr` | system.nim:1266 | partial | bool/enum/int via parseToStr; any other `repr` declines P:11850 | s8cb_tostr | PRC-35 |

#### Memory / lifetime

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| New | `new`,`unsafeNew` | system.nim:567 | modelled | parseNew/parseUnsafeNew P:17756; `new(p, finalizer)` is NewFinalize | s8cl_magics |  |
| NewFinalize | `new` | system.nim:131 | declined | hasVarFormal decline in ensureProcRegistered P:21205; NOT listed in varParamMagics (generic reason text) | s8bl_magicscan (new_finalizer) | PRC-19; C-11 |
| Swap | `swap` | system.nim:1404 | modelled | parseVarMagicStmt P:17813 (both read, then both written); other shapes decline | s8bl_magics (swap_impure) |  |
| WasMoved | `=wasMoved`,`wasMoved` | system.nim:161 | modelled | P:17825 / parseMoveExpr P:17859 / P:11888 | s8cb_magics (SND-05) | SND-05 |
| Move | `move` | system.nim:169 | modelled | P:17825 / parseMoveExpr P:17859 / P:11888 | s8cb_magics (SND-05) | SND-05 |
| EnsureMove | `ensureMove` | system.nim:175 | modelled | P:17825 / parseMoveExpr P:17859 / P:11888 | s8cb_magics (SND-05) | SND-05 |
| Asgn | `=`,`=copy`,`=sink` | system.nim:375 | modelled | `=`/`=copy`/`=sink` as assignment P:17830; a user hook declines (S8cs) | s8cs_routes |  |
| Destroy | `=destroy` | system.nim:385 | declined | varParamMagics vmDeclined P:4289-4293 | s8bl_magics | INT-11 (=trace fault) |
| Trace | `=trace` | system.nim:416 | declined | varParamMagics vmDeclined P:4289-4293 | s8bl_magics | INT-11 (=trace fault) |
| ShallowCopy | `shallowCopy` | system.nim:360 | declined | varParamMagics vmDeclined P:4289-4293 | s8bl_magics | INT-11 (=trace fault) |
| Dup | `=dup` | system.nim:404 | partial | `=dup` of a plain value type = copy P:11857; object/tuple through a hook declines | s8cb_magics | PRC-35 |
| IsNil | `isNil` | system.nim:1455 | modelled | P:11629 (S8bo) | s8bo_nil |  |
| Addr | `addr`,`unsafeAddr` | system.nim:99 | modelled | addr/unsafeAddr arms P:7706,8008,8404 (cluster R, S8ch); global in a walked callee declines (heUnsafeCast) | s8ch | PRC-28/30 |
| DeepCopy | `deepCopy` | system.nim:2768 | declined | stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen | s8cl_magics (GC_ref) | PRC-20 |
| GCref | `GC_ref` | system/gc_interface.nim:42 | declined | stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen | s8cl_magics (GC_ref) | PRC-20 |
| GCunref | `GC_unref` | system/gc_interface.nim:50 | declined | stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen | s8cl_magics (GC_ref) | PRC-20 |
| SizeOf | `sizeof` | system.nim:578 | fold | semfold folds `sizeof(T)`/`sizeof(x)` to an nnkIntLit before getImpl; a size the compiler cannot fold (an incomplete/importc type) would reach the parser as a bodiless magic -> stub decline | p_c1 sz / p_c6 sizeofObj (ran) |  |
| AlignOf | `alignof` | system.nim:597 | fold | semfold folds `sizeof(T)`/`sizeof(x)` to an nnkIntLit before getImpl; a size the compiler cannot fold (an incomplete/importc type) would reach the parser as a bodiless magic -> stub decline | p_c1 sz / p_c6 sizeofObj (ran) |  |
| OffsetOf | `offsetOfDotExpr` | system.nim:600 | fold | semfold folds `sizeof(T)`/`sizeof(x)` to an nnkIntLit before getImpl; a size the compiler cannot fold (an incomplete/importc type) would reach the parser as a bodiless magic -> stub decline | p_c1 sz / p_c6 sizeofObj (ran) |  |
| GetTypeInfo | `getTypeInfo` | system.nim:2033 | declined | stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen | s8cl_magics (GC_ref) | PRC-20 |
| GetTypeInfoV2 | `getDynamicTypeInfo` | system/cyclebreaker.nim:152 | declined | stubBody magic decline P:21225 (S8bo); GC_ref also via the type bridge nnkRecWhen | s8cl_magics (GC_ref) | PRC-20 |

#### Control / misc runtime

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| Echo | `debugEcho`,`echo` | system.nim:1743 | modelled | OpaqueEffectfulProcs (stdlib_models.nim:86): body skipped, fresh result, path uncertain | #137 |  |
| Exit | `quit`,`rawQuit` | system.nim:2474 | modelled | isExitCall/parseExitCall P:7509 (path ends) | s8cb_cells |  |
| ProcCall | `procCall` | system.nim:2784 | declined | P:10019 (empty-body decline on its key) | s8cl_magics (SND-06) | PRC-21 |
| Finished | `finished` | system.nim:2449 | unverified | closure-iterator `finished(it)`: has a body (`discard`); closure iterators themselves are outside the fragment -> expected decline; NOT probed | none | C-13 |
| Of | `of` | system.nim:850 | modelled | parseOfTest P:10024 (S8bn item 7) | s8bn; p_c5 ofop (ran) |  |
| Fields | `fields` | system/iterators.nim:284 | unverified | a `for` over `fields(o)`: the compiler unrolls it at semcheck (nnkStmtList per field) so the walker sees plain field statements; NOT probed | none | C-14 |
| FieldPairs | `fieldPairs` | system/iterators.nim:309 | unverified | a `for` over `fields(o)`: the compiler unrolls it at semcheck (nnkStmtList per field) so the walker sees plain field statements; NOT probed | none | C-14 |
| ParseBiggestFloat | `parseBiggestFloat` | pure/parseutils.nim:587 | declined | var-formal magic in pure/parseutils -> hasVarFormal decline P:21205 (outside the system-only magicscan); parseFloat by name -> iekStrUnsupported P:11912 | p_c3 pfl (ran) | C-11 |

#### Compile-time only

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| Is | `is` | system.nim:770 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| TypeOf | `typeof` | system.nim:57 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| TypeTrait | `$`,`and`,`arity`,`distinctBase`,`genericHead`,`hasDefaultValue`,`isNamedTuple`,`name`,`not`,`or`,`rangeBase`,`stripGenericParams`,`supportsCopyMem`,`tupleLen` | system.nim:79 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| Defined | `defined` | system/compilation.nim:36 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| Declared | `declared` | system/compilation.nim:54 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| DeclaredInScope | `declaredInScope` | system/compilation.nim:69 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| Compiles | `compiles` | system/compilation.nim:73 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| AstToStr | `astToStr` | system/compilation.nim:83 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| CompileOption | `compileOption` | system/compilation.nim:116 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| CompileOptionArg | `compileOption` | system/compilation.nim:131 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| Slurp | `slurp`,`staticRead` | system/compilation.nim:159 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| StaticExec | `gorge`,`staticExec` | system/compilation.nim:174 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| RunnableExamples | `runnableExamples` | system/compilation.nim:87 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |
| InstantiationInfo | `instantiationInfo` | system.nim:1585 | fold | compile-time only: semcheck folds them; never a call node in the typed body getImpl returns | none (read) |  |

#### Experimental / threads / DrNim

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| Spawn | `pinnedSpawn`,`spawn` | pure/concurrency/threadpool.nim:457 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| Parallel | `parallel` | pure/concurrency/threadpool.nim:484 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| OmpParFor | `||` | system/iterators_1.nim:147 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| Isolate | `isolate` | std/isolation.nim:31 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| Unown | `unown` | system.nim:818 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| PrivateAccess | `privateAccess` | std/importutils.nim:23 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| Plugin | `iterToProc`,`locals` | system.nim:2739 | n/a | threadpool/experimental; a call reaches ensureProcRegistered: Spawn/Isolate have bodies (walked or declined on shape), the rest stub-decline; none pinned | none |  |
| Implies | `->` | std/logic.nim:4 | n/a | DrNim contract magics; not valid in ordinary code | none |  |
| Iff | `<->` | std/logic.nim:5 | n/a | DrNim contract magics; not valid in ordinary code | none |  |
| Forall | `forall` | std/logic.nim:7 | n/a | DrNim contract magics; not valid in ordinary code | none |  |
| Exists | `exists` | std/logic.nim:8 | n/a | DrNim contract magics; not valid in ordinary code | none |  |
| Old | `old` | std/logic.nim:10 | n/a | DrNim contract magics; not valid in ordinary code | none |  |

#### Macro-time (std/macros, macrocache)

| magic | declared as | decl (lib) | status | evidence | native pin | 0016 row |
|---|---|---|---|---|---|---|
| StrToIdent | `ident`,`newIdentNode`,`toNimIdent` | core/macros.nim:157 | n/a | std/macros NimNode API: compile-time only | none |  |
| EqIdent | `==`,`eqIdent` | core/macros.nim:161 | n/a | std/macros NimNode API: compile-time only | none |  |
| EqNimrodNode | `==` | core/macros.nim:165 | n/a | std/macros NimNode API: compile-time only | none |  |
| SameNodeType | `sameType` | core/macros.nim:175 | n/a | std/macros NimNode API: compile-time only | none |  |
| NLen | `len` | core/macros.nim:180 | n/a | std/macros NimNode API: compile-time only | none |  |
| NChild | `[]` | core/macros.nim:183 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSetChild | `[]=` | core/macros.nim:201 | n/a | std/macros NimNode API: compile-time only | none |  |
| NAdd | `add` | core/macros.nim:223 | n/a | std/macros NimNode API: compile-time only | none |  |
| NAddMultiple | `add` | core/macros.nim:228 | n/a | std/macros NimNode API: compile-time only | none |  |
| NDel | `del` | core/macros.nim:233 | n/a | std/macros NimNode API: compile-time only | none |  |
| NKind | `kind` | core/macros.nim:236 | n/a | std/macros NimNode API: compile-time only | none |  |
| NIntVal | `intVal` | core/macros.nim:239 | n/a | std/macros NimNode API: compile-time only | none |  |
| NFloatVal | `floatVal` | core/macros.nim:242 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSymKind | `symKind` | core/macros.nim:246 | n/a | std/macros NimNode API: compile-time only | none |  |
| GetImpl | `getImpl` | core/macros.nim:247 | n/a | std/macros NimNode API: compile-time only | none |  |
| NStrVal | `$`,`strVal` | core/macros.nim:249 | n/a | std/macros NimNode API: compile-time only | none |  |
| NIdent | `ident` | core/macros.nim:257 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSymbol | `symbol` | core/macros.nim:260 | n/a | std/macros NimNode API: compile-time only | none |  |
| GetImplTransf | `getImplTransformed` | core/macros.nim:276 | n/a | std/macros NimNode API: compile-time only | none |  |
| SymOwner | `owner` | core/macros.nim:282 | n/a | std/macros NimNode API: compile-time only | none |  |
| SymIsInstantiationOf | `isInstantiationOf` | core/macros.nim:293 | n/a | std/macros NimNode API: compile-time only | none |  |
| NGetType | `getTypeImpl`,`getTypeInstSkipAlias`,`getTypeInst`,`getType`,`typeKind` | core/macros.nim:298 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSigHash | `signatureHash` | core/macros.nim:357 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSetIntVal | `intVal=` | core/macros.nim:373 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSetFloatVal | `floatVal=` | core/macros.nim:374 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSetSymbol | `symbol=` | core/macros.nim:378 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSetIdent | `ident=` | core/macros.nim:381 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSetStrVal | `strVal=` | core/macros.nim:386 | n/a | std/macros NimNode API: compile-time only | none |  |
| NNewNimNode | `newNimNode` | core/macros.nim:396 | n/a | std/macros NimNode API: compile-time only | none |  |
| NCopyNimNode | `copyNimNode` | core/macros.nim:405 | n/a | std/macros NimNode API: compile-time only | none |  |
| NCopyNimTree | `copyNimTree` | core/macros.nim:418 | n/a | std/macros NimNode API: compile-time only | none |  |
| NError | `error`,`internalErrorFlag` | core/macros.nim:436 | n/a | std/macros NimNode API: compile-time only | none |  |
| NWarning | `warning` | core/macros.nim:441 | n/a | std/macros NimNode API: compile-time only | none |  |
| NHint | `hint` | core/macros.nim:444 | n/a | std/macros NimNode API: compile-time only | none |  |
| NBindSym | `bindSym` | core/macros.nim:495 | n/a | std/macros NimNode API: compile-time only | none |  |
| NGenSym | `genSym` | core/macros.nim:509 | n/a | std/macros NimNode API: compile-time only | none |  |
| NCallSite | `callsite` | core/macros.nim:514 | n/a | std/macros NimNode API: compile-time only | none |  |
| NLineInfo | `copyLineInfo`,`getColumn`,`getFile`,`getLine`,`setColumn`,`setFile`,`setLine` | core/macros.nim:538 | n/a | std/macros NimNode API: compile-time only | none |  |
| ParseExprToAst | `internalParseExpr` | core/macros.nim:569 | n/a | std/macros NimNode API: compile-time only | none |  |
| ParseStmtToAst | `internalParseStmt` | core/macros.nim:572 | n/a | std/macros NimNode API: compile-time only | none |  |
| ExpandToAst | `getAst` | core/macros.nim:595 | n/a | std/macros NimNode API: compile-time only | none |  |
| QuoteAst | `quote` | core/macros.nim:604 | n/a | std/macros NimNode API: compile-time only | none |  |
| NodeId | `nodeID` | core/macros.nim:1534 | n/a | std/macros NimNode API: compile-time only | none |  |
| NSizeOf | `getAlign`,`getOffset`,`getSize` | core/macros.nim:1763 | n/a | std/macros NimNode API: compile-time only | none |  |
| NccValue | `value` | core/macrocache.nim:60 | n/a | std/macrocache: compile-time only | none |  |
| NccInc | `inc` | core/macrocache.nim:71 | n/a | std/macrocache: compile-time only | none |  |
| NcsAdd | `add` | core/macrocache.nim:81 | n/a | std/macrocache: compile-time only | none |  |
| NcsIncl | `incl` | core/macrocache.nim:94 | n/a | std/macrocache: compile-time only | none |  |
| NcsLen | `len` | core/macrocache.nim:109 | n/a | std/macrocache: compile-time only | none |  |
| NcsAt | `[]` | core/macrocache.nim:123 | n/a | std/macrocache: compile-time only | none |  |
| NctPut | `[]=` | core/macrocache.nim:162 | n/a | std/macrocache: compile-time only | none |  |
| NctLen | `len` | core/macrocache.nim:178 | n/a | std/macrocache: compile-time only | none |  |
| NctGet | `[]` | core/macrocache.nim:188 | n/a | std/macrocache: compile-time only | none |  |
| NctHasNext | `hasNext` | core/macrocache.nim:226 | n/a | std/macrocache: compile-time only | none |  |
| NctNext | `next` | core/macrocache.nim:227 | n/a | std/macrocache: compile-time only | none |  |
