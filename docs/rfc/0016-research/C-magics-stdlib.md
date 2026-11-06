# Lens C — compiler magics and stdlib models (RFC-0016 work-list input)

Snapshot: `83c1d304` (read-only). Native probes: eos `~/nelli/wt-rsC` (same sha), `scripts/dt-bounded.sh c probes/p_c*.nim`, i.e. the dev image's patched Nim 2.2.10, gcc, c backend, debug build, checks on, `--threads:on`, Z3 as wired in that worktree. Every claim is tagged `read` (from source) or `ran` (a probe on eos). Probe sources are in `~/nelli/wt-rsC/probes/p_c1_ints.nim`, `p_c1b_mod.nim`, `p_c2_coll.nim`, `p_c3_str.nim` (killed), `p_c3b_cmp.nim`, `p_c3c_rest.nim`, `p_c3d_parsebool.nim`, `p_c4_sort.nim`, `p_c5_enum.nim`, `p_c6_dollar.nim`, with a shared header `p_hdr.nim`.


**Summary.** 216 magics enumerated from the image's `lib/` (505 declarations): 106 modelled, 4 walked by body, 4 partial, 13 declined, 17 compile-time folds, 67 not reachable at runtime, 5 unverified. 7 probe files, 11 probe runs, 118 walker verdicts against native: 1 soundness mismatch confirmed (C-01, `low(int) mod -1` with a literal divisor: false `sxUnsat`), 1 hang confirmed (C-03, `parseBool`), 1 walker fault (C-02, `filterIt`), 2 suspected crashes unprobed (C-10 ptr ordering, C-12 empty `@[]`), the rest precision declines, all sound. CRH-01's compile stop on `sort` is a decline at this sha.

## 0. How the magic universe was enumerated (`ran`)

The dev image ships Nim alone (`/opt/nim/2.2.10-patched/{bin,config,lib}`), no `compiler/ast.nim`, so `TMagic` cannot be read from the toolchain. The universe below is every `{.magic: "X".}` pragma declared in `lib/system.nim`, `lib/system/*`, `lib/pure/**`, `lib/std/**`, `lib/core/**`, `lib/impure/**` of that image (copied to the scratchpad and scanned with `extract_magics.py`): **505 declarations, 216 distinct magic names**, 33 declarations with a `var` formal, 28 with a real body. A `TMagic` member that no lib routine declares (compiler-internal members such as `mArray`, `mOpenArray`, `mNone`, the type-class magics `mInt`..`mOrdinal`, `mExpandToAst` is declared as `getAst`) cannot appear as a call in a typed body and is out of scope for the walker by construction.

How the parser meets a magic (`read`, `dsl_parser.nim`):

1. A name-keyed arm fires first — the infix/prefix tables (`binopForInfix` :3291, `nnkInfix` :10969, `nnkPrefix` :11182), the builtin-by-name call arms (`isBuiltinNamed`, :4500), the stdlib string/seq/table models (`stdlib_models.nim`), `parseToStr` (:7444), the `routineMagic` switch at :11868 (`AshrI`, `Ord`, `Chr`, `EnsureMove`), `parseVarMagicStmt` (:17778). These are keyed by the operator spelling plus the operand's IR class, not by the magic name, except the handful at :11868 and `varParamMagics` (:4254).
2. Anything else reaches `ensureProcRegistered` (:21164), which has three magic gates in order: a magic with a `var` formal declines (`varMagicDecline`, S8bl); a routine whose formals are not `IdentDefs` declines (`#hook`, S8cl); a magic whose body is a stub (`stubBody` :21146: empty, doc comment, `discard`, `runnableExamples`) declines (S8bo). A magic with a real body (`abs`, `min`, `max`, `move`, `@`(openArray), `add`(seq, seqs_v2), `=sink`, `..`) is **walked as that body**.
3. Compile-time magics (`defined`, `compiles`, `sizeof`, `is`, `typeof`, `instantiationInfo`, the `NimNode` API) are folded by semcheck before `getImpl` and never appear as calls in a typed body.

So the universe is already closed in the sense that **no magic is walked as a silent no-op** at this sha: a magic either has a name arm, or has a body, or declines. What is *not* closed is (a) whether each name arm agrees with the compiled program on every operand class it accepts, and (b) the four magics whose real body is walked under a model that is not the compiler's (findings C-01, C-06, C-10).

## 1. Magic coverage table

Status vocabulary: `modelled` (a named arm lowers it), `body` (its Nim body is walked), `partial` (modelled for some operand shapes, declines the rest), `declined` (a named decline, sound), `fold` (compile-time only, never reaches the walker), `n/a` (macro-time, DrNim, threadpool: not reachable from ordinary runtime code), `unverified` (no arm found by name and no probe run; what happens is inferred from the gates in §0). Counts: modelled 106, body 4, partial 4, declined 13, fold 17, n/a 67, unverified 5.

`P:` is `src/nelli/smt/dsl_parser.nim`, `RT:` is `src/nelli/smt/runtime.nim`. "native pin" names a `tests/tsymex_rfc0005_*` suite without the prefix, or a probe from this lens.


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


## 2. Stdlib routines: walked by body, modelled, or declined

Rule (`read`, `dsl_typebridge.nim:53-82`): a routine is "stdlib" when its declaration file is under the compiler's `lib/`; a stdlib routine is modelled by name only where an arm exists, otherwise its body is walked like a user routine, subject to the S8cu check-option scan (`check_options.nim`: any routine inside a `{.push checks/overflowChecks/... off.}` region declines with `feCheckOption`/`feOverflowCheckOption`), the foreign-body decline (`isBodilessForeign`, P:4316: importc/dynlib), the `formalsReadable` decline (`#hook`: a formal typed by its default, e.g. `sort`'s `order = Ascending`), and the generic/by-value/closure declines.

Push regions that matter (`read`, lib sources): `system.nim:1985-2539 {.push checks: off.}` (holds `cmp`, `setLenUninit`, `delete`(seq), `finished`, `getTypeInfo`, `quit`), `strutils.nim:347-365` (`cmpIgnoreStyle`), `parseutils.nim:433-463 overflowChecks: off` (`rawParseInt`), `math.nim:157-1116 checks: off` (nearly all of std/math: PRC-09), `sequtils.nim:120-122` (the `unCheckedInc` template, expanded inside `count`, `countIt`...), `times.nim` (`overflowChecks: off`), `hashes.nim` none (but `hash` bodies hit `when nimvm` and `cast`).

| module.routine | walked / modelled / declined | build-sensitive? | evidence | pin |
|---|---|---|---|---|
| system.`$`(int, int8..64, uint8..64) | modelled `iekIntToStr` (sign handled, unsigned by `signed` flag) | no | `runtime_strings.nim:1132-1157`; p_c1 `u64s_max`, `u8s_255`, `i8s_min` agree | p_c1 (ran) |
| system.`$`(float, float32) | declined `iekStrUnsupported "$float"` | yes natively (`addFloat` is dragonbox/sprintf: locale-free but C-runtime dependent) | P:7489; p_c3c `dollar_float` | PRC-35 |
| system.`$`(char/bool/enum/string) | modelled (`parseToStr`); enum hole declines | no | P:7444-7487; p_c5 `hole_dollar_b`, `named_why` | SND-02..04 |
| system.`$`(cstring) | declined (`$` of a cstring operand) | no | P:7490; p_c6 `dollar_cstring` | — |
| system.`$`(seq/array/tuple/object/set) | declined at `parseToStr`'s fall-through (`$` of a itSeq/itTuple operand is not modelled); the body (`dollars.nim:86-151`) is never reached, and `addQuoted` inside it is in system's `checks: off` region | no | p_c6 `dollar_seq`, `dollar_tup`, `dollar_obj`, `dollar_set`, `addquoted` all sxUnknown, all native hits | C-05 |
| system.repr | bool/enum/int modelled; others declined | yes (refc vs arc `repr` of refs prints addresses) | P:11842-11856 | PRC-35 |
| system.cmp(string) | declined (`cmp` is inside system's `checks: off` push, `feCheckOption`) | no | p_c3b (ran): `sxUnknown [feCheckOption: cmp (system.nim:2203) ...]` | PRC-07 |
| system.cmp(int) | body (`if x == y: 0 elif x < y: -1 else: 1`) walked | no | p_c3b `cmpi_4` sxSat, native hit | p_c3b (ran) |
| system.min/max(int) | body walked | no | P:12762; p_c4 `minmax_7` | p_c4 (ran) |
| system.min/max(openArray) | declined (`high` of a value of non-int-family type, A0) | no | p_c4 `minseq_2`: `feUnsupportedExprKind: A0: low/high on non-int-family type` | C-07 |
| system.abs | body walked; `-x` overflow modelled | no | s8g_models | s8g |
| system.toInt(float) | declined (PRC-35) | no | PRC-35 | PRC-35 |
| system.del(seq) (unordered) / delete(seq) (ordered) / pop / insert | modelled by name (`iekSeqDel` = swap-with-last; `delete` ordered) | no | P:14688, :20133, :12533, :17517; p_c2 `del_swap` sat + `del_ordered` unsat, `delete_ordered` sat — agree with native | p_c2 (ran) |
| system.`==`(seq), `==`(array), `==`(tuple) | declined (`eqBV on non-BV SymVal (kind=seq value)` / array) | no | p_c2 `seqeq_hit`, `arreq_hit` sxUnknown; native hit | PRC-34 (tuple); C-08 (seq/array) |
| system.`&`(string) | modelled | no | P:11000 | S8 |
| system.`&`(seq) | falls to `binopForInfix` with no `&` case: unsupported-infix decline | no | P:11070 (read) | — |
| system.newString/newStringOfCap/newSeq/newSeqOfCap/setLen | modelled | no | P:17880, :9372, :17705 | s8bl_setlen, s8cl_strings |
| system.reset / default / zeroDefault | modelled | no | P:11720; p_c6 `reset_3`, `default_2` | p_c6 (ran) |
| system.sizeof/alignof/offsetof | folded by the compiler | **yes** (platform/ABI; int is 64-bit on every CI leg, but `sizeof(object)` follows the C compiler's layout; folded at macro-expansion on the build host, which is the run host) | p_c1 `sz_ok`, p_c6 `sizeof_P` | p_c1/p_c6 (ran) |
| system.quit | modelled (path ends) | no | P:7509 | s8cb |
| system.echo/debugEcho, stdout.write... | opaque-effectful (skipped, path uncertain) | no | `stdlib_models.nim:86` | #137 |
| system.swap / move / wasMoved / ensureMove | modelled | no | P:17813, :17859 | s8bl_magics, s8cb |
| system.addQuoted | body walked | no | p_c6 `addquoted` | p_c6 (ran) |
| strutils.split(s, char) / split(s, string sep) | char sep modelled; string sep declines (`seZ3StringIncomplete`); a `set[char]` sep declines; `maxsplit` declines | no | p_c3 `split_set3`, `split_max`, `split_str3` all sxUnknown | precision |
| strutils.join | modelled | no | p_c3c `join_1` | — |
| strutils.strip | modelled for literal flags/chars; else declines | no | P:12342-12400 | ADR-0026 |
| strutils.replace(s, string, string) | modelled on Z3 >= 4.15.5, else declines (`seZ3VersionMissing`) | **yes: Z3 version** | p_c3 `replace_ch` sxUnknown on this worktree's Z3; `replace_empty_*` decided | S8c |
| strutils.replace(s, char, char) | routes to the same gate | no | p_c3 `replace_ch` | — |
| strutils.contains(s, set[char]) / find(s, set) | declined (needle is a set value) | no | p_c3 `contains_set` | precision |
| strutils.count(s, char/lit string) | modelled | no | P:12326 | S8cf item 11 |
| strutils.toUpperAscii/toLowerAscii | modelled (BV18 ITE seqMap) | no | P:12320 | ADR-0015 |
| unicode.toUpper/toLower | declined | no | P:12322 | — |
| strutils.parseInt/parseBiggestInt | modelled (`iekStrToInt`: sign, digits, 64-bit bound, `_` lax) | no | `runtime_strings.nim:1158-1230` | S8b |
| strutils.parseFloat / parseutils.parseBiggestFloat | declined (`iekStrUnsupported`; the magic has a `var` formal) | no | P:11912; P:21205 | — |
| strutils.parseHexInt/parseOctInt/parseBinInt | declined (`parseHex` has a defaulted formal: `#hook`; by-value may-write) | no | p_c3 `parsehex_255` | precision |
| strutils.parseBool | **walked by body (`normalize` + string `case`) and does not terminate within 280 s** | no | p_c3 killed at this verdict; p_c3d re-run | **C-03 (hang)** |
| strutils.parseEnum | body walked (macro-generated string `case` over `normalize`): decides | no | p_c5 (ran): `parseenum_default` sat (native hit); `parseenum_green` unsat (no native hit in the tried domain; exhaustiveness unconfirmed) — note it terminates where `parseBool` (C-03) does not | — |
| strutils.toHex/toBin | modelled (`iekRadixFmt`, BV operands) | no | p_c3 `tohex_255`, `tohex_m1` agree | — |
| strutils.repeat, startsWith(char), isDigit, toUpperAscii, substr, `s[a .. b]`, `s[a .. ^1]`, find/rfind | body walked or modelled; all agree with native | no | p_c3c `repeat_3`, `startswith_ch`, `isdigit`, `upper_a`, `substr_abc`, `slice_rev_empty`, `slice_oob_raise` sat, `slice_oob_range` unsat, `str_gt_7f`, `find_b1` | p_c3c (ran) |
| strutils.intToStr | declined (`'0' & result`: `&`(char, string) unmodelled) | no | p_c3c `inttostr_005` | C-04 |
| strutils.align | declined (`#hook`: `fillChar = ' '`) | no | p_c3c `align_x` | C-06 |
| system.`in`(x, a .. b) (`contains(HSlice, x)`) | declined: `unsupported infix operator ..` (an HSlice VALUE in call position) | no | p_c5 (ran): every SUT using `x in 0 .. 10` declines | C-18 |
| strutils.formatFloat | body -> `addFloat...` -> C `snprintf`/dragonbox importc: foreign decline | yes natively (C runtime) | p_c3c `formatfloat_15` | — |
| strutils.cmpIgnoreStyle | declined (push region) | no | strutils.nim:347 (read) | PRC-07 |
| strutils.splitLines (iterator) | compile stop | no | INT-09 | INT-09 |
| strformat.fmt | macro -> `formatValue` bodies (int: walked; float: `$float` decline) | no | p_c6 `fmt_007`, `fmt_f15` | see findings |
| strutils.`%` | body walked | no | p_c6 `pct_4z` | see findings |
| math.* (sqrt, floor, ceil, round, trunc, abs, min, max, classify, copySign, isNaN...) | modelled (`mathFpModeledOps`) | no | `stdlib_models.nim:66` | F6/A5 |
| math.pow/exp/log/sin... | importc: foreign decline; everything else in math is under `checks: off` (declines) | no | math.nim:157-1116 (read) | PRC-09 |
| math.nextafter | declined | no | `mathFpDeferredOps` | — |
| sequtils.map(proc) / foldl / filterIt | map(proc) and foldl walk and decide; **filterIt is a walker fault** (`AssertionDefect` RT:19688 `lowerLeafInExpr`) | no | p_c2 `map_5`, `foldl_3` sat; `filt_9` `weInternalWalkerFault` | **C-02 (crash)** |
| sequtils.mapIt / toSeq | declined (`nnkTypeSection` / `nnkBlockExpr` in the template expansion) | no | p_c2 `mapit_3`, `toseq_3` | PRC-22 |
| sequtils.count | declined (`unCheckedInc` push inside the body: `feOverflowCheckOption`) | no | p_c2 `count_4` | PRC-07 |
| algorithm.sort / sorted | declined (`#hook`: `order = Ascending` formal typed by its default) — the CRH-01 compile stop is gone at this sha | no | p_c4 `sorted_2`, `sort_9`, `sortd_9` sxUnknown; native hits | CRH-01 (update), C-09 |
| algorithm.reversed | body walked, decides | no | p_c2 `rev_7` sat | p_c2 (ran) |
| algorithm.binarySearch | declined (by-value may-write; `cmp` closure uncertain) | no | p_c2 `bs_3` | precision |
| tables.[] / []= / contains / hasKey / del / pairs / keys / values / mpairs | modelled (Z3 arrays); iteration enumerates one order and stamps `feTableIterOrder`: a label reached in that order is sat only after in-process replay, any other is sxUnknown | **yes natively: iteration order is hash order** | p_c2 `tk_first_b` sxSat (native hit), `tk_first_a` sxUnknown | PRC-05 |
| tables.clear / pop / getOrDefault / mgetOrPut | partly modelled | no | PRC-05 | PRC-05 |
| sets.HashSet incl/excl/contains/card/toHashSet | modelled | no | p_c4 `hs_card3` sat | — |
| sets.HashSet iteration (`for x in h`) | declined (`unsupported for-loop container kind: itSet`) | yes natively (hash order) | p_c2 `hs_first_*` | precision |
| hashes.hash(int) | declined (`nnkWhenStmt` in the body) | **yes: `hash(int)` differs between Nim versions and `-d:nimPreviewHashRef`; string hash differs by `nimStringHash2`** | p_c2 `hash_is3`, `hash_eq_h3` | sound as is |
| hashes.hash(string) | declined (`nnkCast` of `hashFarm(toOpenArrayByte...)`) | yes | p_c2 `hashstr_a` | sound as is |
| options.get/isSome/isNone/some/none | body walked (object with `has` field) | no | no arm by name (read); not probed | — |
| random.rand (global state) | body reads the module's `state` global: `feGlobalReadUnmodelled` decline expected; `rand(r: var Rand, ...)` walks xoroshiro over BV | yes natively (seed) | read; not probed | — |
| times.now/getTime/epochTime/cpuTime | foreign (`clock_gettime` importc) and `times.nim` has `overflowChecks: off` pushes: declines | yes | read; not probed | — |
| json.parseJson/`$`(JsonNode) | ref-object lexer/parser bodies; expected to decline on refs/globals or run out of budget | no | read; not probed | — |
| re/nre `match`/`find`/`contains`/`replace` | modelled by the PCRE model (`pcre_*.nim`) | **yes: PCRE build (JIT, version)** | S8bt/S8cf | PRC-33, PND-01/02 |
| unicode.runes/runeLen/`$`(Rune) | modelled (A7) | no | P:7454 | A7 |

## 3. Findings

Classes follow RFC-0016 §3.2. "effort" is S (hours), M (a slice), L (several slices). Every `ran` row is on the build named at the top; the native column is the same binary's own run of the SUT (`symexCaptureBegin`/`End`), so both columns are one build.

| id | item | class | minimal SUT | evidence | suggested pin | effort |
|---|---|---|---|---|---|---|
| C-01 | `low(int) mod -1` with a **literal** `-1` divisor: native 0, no trap, no raise; the walker kills the path as a SIGFPE trap, so a label after it is `sxUnsat` | **soundness-confirmed** (false `sxUnsat`); the same for `int32` | `proc f(x: int) = if x == low(int): (let q = x mod -1; if q == 0: symexTarget("t"))` | `ran` p_c1b: `WALKER modLit modlit_zero -> sxUnsat`, `modLit32 -> sxUnsat`, `NATIVE hits: modlit_zero, modlit32_zero`; with a **variable** divisor the process dies natively (SIGFPE, rc 136) and the walker agrees (`modVar -> sxUnsat`), which is the shape S8i pinned (`tsymex_rfc0005_s8i_models.nim:80 modTrap(x, y)`). Cause: `nimbase.h:587 nimModInt` is a plain C `%` and gcc folds `x % -1` to 0 for a constant divisor at every `-O`; RT:8862-8870 adds `divLowByMinusOne` to `arithTrapConds` for `mod` at widths 32/64 regardless of the divisor's shape | `tsymex_rfc0016_c01_modlit`: literal and `const` divisor decide `q == 0` sat (native hit); variable divisor stays the trap. Run on gcc, clang (mingw) and MSVC legs: the fold is the C compiler's, so this is also an INT-31 (`--cc` in the cache key) case | S: skip the trap condition when the divisor IR is a literal/const (`mod` by a constant -1 is 0); or decline on it |
| C-02 | `filterIt(@[1, x, 3], it > 2)`: walker assertion `lowerLeafInExpr: expected side-effect-free container expr` | crash (walker fault, in-band `sxUnknown`; native decides) | `proc f(x: int) = (let r = filterIt(@[1, x, 3], it > 2); if r.len == 2 and r[0] == 9: symexTarget("t"))` | `ran` p_c2: `filt_9 -> sxUnknown [weInternalWalkerFault: AssertionDefect RT:19688]`; native hit `filt_9` | pin as a named decline first, then a model (the template expands to a `for` over a temp with `add`) | S (decline) / M (model) |
| C-03 | `parseBool(s)` with `s.len == 4` never returns a verdict: killed at 240 s alone, at 280 s inside p_c3; native is instant | **hang** | `proc f(s: string) = if s.len == 4 and parseBool(s): symexTarget("t")` | `ran` p_c3d: `START parseBool` then `HUNG ... killed after 240s`; p_c3 killed at the same verdict after 12 others passed. Body is `normalize(s)` (a `while` building a string char by char, `strutils.nim`) then a string `case` of 8 arms; neither the walk's bounds nor the solver budget ended it | `tsymex_rfc0016_c03_parsebool`: decides or declines within the suite budget; find which bound (`maxSeqLen`, loop unroll, `seqQueryRLimit`) does not apply to a string `case` over a built string | M |
| C-04 | `intToStr(x, 3)` declines: `'0' & result` is `&`(char, string), only `&`(string, string) is modelled | precision | `proc f(x: int) = if x == 5 and intToStr(x, 3) == "005": symexTarget("t")` | `ran` p_c3c: `sxUnknown [feUnsupportedOp: unsupported infix operator & in '0' & result]`; native hit | pin `intToStr`, `'a' & s`, `s & 'a'` | S (P:11000: accept a char operand as a one-byte string) |
| C-05 | `$` of a seq, array, tuple, object or `set` declines at `parseToStr`'s fall-through; natively deterministic (`dollars.nim:86-151`). Even if the fall-through walked the body, `addQuoted` is inside system's `checks: off` push (declines, p_c6 `addquoted`) | precision | `proc f(x: int) = if $(@[x, 2]) == "@[1, 2]": symexTarget("t")` | `ran` p_c6: `dollar_seq/tup/obj/set/cstring -> sxUnknown`, all five native hits | pin each shape; PRC-35 lists only `$float` and `repr` | M (needs PRC-07 for `addQuoted`) |
| C-06 | `sort`, `sorted`, `align`, `formatFloat`, `parseHex` (behind `parseHexInt`) decline as `#hook`: a formal typed by its default (`order = SortOrder.Ascending`, `fillChar = ' '`) fails `formalsReadable`. CRH-01's compile stop on `s.sort(...)` is **gone at this sha**: both `s.sort()` and `s.sort(system.cmp[int], Descending)` compile and decline | precision (and CRH-01 status update) | `proc f(x: int) = (var s = @[3, x, 1]; s.sort(); if s[2] == 9: symexTarget("t"))` | `ran` p_c4: `sorted_2`, `sort_9`, `sortd_9 -> sxUnknown [... routine sort, whose formals cannot be read ...]`, native hits all three; p_c3c `align_x`, `formatfloat_15`, p_c3 `parsehex_255` same kind | update CRH-01 to "declines"; pin `sorted` once modelled | M (read the formal's type from the default expression's `getTypeInst` in `formalsReadable`) |
| C-07 | `min(openArray)`/`max(openArray)` decline: `high(x)` on an openArray VALUE hits A0's "low/high on non-int-family type" | precision | `proc f(x: int) = if min(@[4, x, 9]) == 2: symexTarget("t")` | `ran` p_c4: `minseq_2 -> sxUnknown [A0: low/high on non-int-family type user:x ... comparisons.nim:280]`; native hit | pin `high(s)`/`low(s)` for seq, array, openArray values (= `len-1`, 0, or the array's bounds) | S |
| C-08 | `==` on a seq or an array declines with a raise-text decline (`eqBV on non-BV SymVal (kind=seq value)`), not a named kind | precision (with PRC-34 for tuples) | `proc f(x: int) = if @[x, 2] == @[1, 2]: symexTarget("t")` | `ran` p_c2: `seqeq_hit`, `arreq_hit -> sxUnknown`; native hits | model: equal length and element-wise equality under the `lastIdx` cap; pin seq/array/tuple | M |
| C-09 | `split(s, set[char])`, `split(s, "ab")`, `split(s, ',', maxsplit)`, `contains(s, set[char])` decline | precision | `proc f(s: string) = if s.len == 3 and s.split({',', ';'}).len == 3: symexTarget("t")` | `ran` p_c3: four `sxUnknown` with named string-op reasons; native hits where tried | pin after modelling; `maxsplit` is a bounded rewrite of the char model | M |
| C-10 | `<`/`<=` on `ptr` (LtPtr/LePtr): no arm by name; `lowerCmp`'s else branch would call `cmpBV` on an `svPtr`. Expected a raise or fault rather than a named decline | crash (suspected; **not probed**: the probe queue was serialised behind C-03) | `proc f(p, q: ptr int) = if p < q: symexTarget("t")` | `read` RT:8911-8938 (no `svPtr` case); P:10969 has no ptr intercept for `<` | probe first; then a named decline (pointer order is allocator-dependent natively: build-sensitive, keep declined) | S |
| C-11 | `varParamMagics` (P:4254) claims every system var-magic, but `NewFinalize` (`new(p, finalizer)`, system.nim:131, a multi-line declaration the guard's one-line scanner does not read) is absent, and `ParseBiggestFloat` (pure/parseutils.nim:587) is outside the guard's system-only file list. Both still decline through `hasVarFormal` (P:21205), with the generic reason text | precision of the registry's claim (sound today) | — | `ran` extract: 33 var-formal declarations, 21 distinct magics, 2 not in the table; `tsymex_rfc0005_s8bl_magicscan.nim:27-50` scans single-line decls of system sources only | extend the guard to multi-line decls and all `lib/` dirs (see §4) | S |
| C-12 | An empty `@[]` whose classified type is not `itSeq` is a macro-time `error("cannot infer element type of empty @[]")` (P:11206): a compile stop, not a decline; `nnkPrefix`'s `else: error(...)` (P:11223) is the same shape for any prefix operator the five arms do not name (dormant: system declares no other) | crash (suspected; not probed) | `proc f(x: int) = (var s: seq[ref int] = @[]; if x == 1: symexTarget("t"))` | `read` P:11201-11223 | probe; convert both `error()`s to `declineAtSite` | S |
| C-13 | Table/HashSet iteration: native order is hash order (build-sensitive: Nim version, `-d:nimStringHash2`, `-d:nimPreviewHashRef`); the walker enumerates one order, stamps `feTableIterOrder`, and answers `sxSat` only after in-process replay (`tk_first_b` sat, native hit) and `sxUnknown` otherwise (`tk_first_a`); HashSet iteration declines outright (`unsupported for-loop container kind: itSet`); `hash(int)`/`hash(string)` decline (`nnkWhenStmt`, `nnkCast`) | precision, correctly build-gated | `for k in t.keys: (first = k; break)` | `ran` p_c2 | record under PRC-05 that the exact model is per build and stays declined/replay-gated; no action | — |
| C-14 | Declines reached by common stdlib calls, all sound: `fmt"{x:03}"` (`nnkBlockExpr`), `"$1" % [...]` (unsupported infix `%`), `cmp(string)`, `addQuoted`, `cmpIgnoreStyle` (system/strutils `checks: off` pushes), `count(seq)` (a push inside the `unCheckedInc` template, read as the whole routine), `binarySearch` (by-value may-write + `cmp` closure), `mapIt`/`toSeq` (`nnkTypeSection`/`nnkBlockExpr`), `parseFloat`, `$float32`, `$cstring` | precision | — | `ran` p_c2, p_c3, p_c3c, p_c6 | fold into PRC-07 (check-off semantics), PRC-22 (type sections), PRC-35 (`$`); `%` and `fmt` need their own rows | M each |
| C-15 | `sizeof`/`alignof`/`offsetof` are folded by the compiler on the build host; the walker never sees them. Agrees today (`sizeof(P) == 24`, `sz_ok`) because nelli is compiled and run on the same host and every CI leg is 64-bit; a cross-compiled walker would fold the host's layout | test-harness (record) | — | `ran` p_c1 `sz_ok`, p_c6 `sizeof_P` | note in §2.2: "same build" includes the C compiler's layout and constant folding (C-01) | — |
| C-16 | Magics with a real body that are walked **as that body** (13 names: AbsI, MinI, MaxI, Move, OpenArrayToSeq, AppendSeqElem, Asgn, DotDot, EqCString, Finished, StaticExec, Spawn, Isolate): the body is a VM/doc fallback, not the compiler's semantics. Today each is intercepted by a name arm before `ensureProcRegistered` or declines (EqCString via foreign `cmpStrings`); a toolchain bump that gives another magic a body would be walked silently | design (fail-closed gap) | — | `ran` extract (`body=1` rows); `read` P:21225 (only a stub body declines) | §4 item 3: allowlist the bodied magics | S |
| C-17 | `=destroy`'s explicit call (`Destroy`), `=trace`, `shallowCopy` are `vmDeclined`; `=trace` through a hook is a walker fault (INT-11) | crash (recorded) | — | `read` P:4289 | INT-11 | — |
| C-18 | `x in 0 .. 10` (system `contains(HSlice, x)`, the commonest bounding idiom in SUTs) declines: `unsupported infix operator ..` because the `HSlice` is a VALUE in call position (P:11070; v64's decline); every SUT built on it is `sxUnknown` | precision (high frequency) | `proc f(x: int) = if x in 0 .. 10 and x == 7: symexTarget("t")` | `ran` p_c5 first run: 7 of 9 verdicts `sxUnknown [unsupported infix operator .. | . on unsupported type uninterp[HSlice[int, int]]]`, all native hits; the rerun with `x >= 0 and x <= 10` decides every one | pin `in`/`notin` over an int, char and enum HSlice (lower to two comparisons) | S |
| C-19 | Enum family agrees with native at this sha (recorded so the rows are not reopened): `$` of a holey enum (hole declines in-band, member sat), `$` of a string-named enum, `Hole(x)` conversion (`RangeDefect` only outside `low..high`, not in a hole — native and walker agree), `inc` on an enum to its last member and past it (`OverflowDefect`), `x of Derived` | test-harness (pins to add) | — | `ran` p_c5 rerun: 9 of 9 verdicts match the native hits | add as `tsymex_rfc0016_c19_enums` | S |


## 4. How to make this axis closed

The universe has two halves with different closure mechanisms.

**Magics (216 names in this toolchain).** Closure means: a magic reaches the walker only through a path that is either a name arm with a native pin, or a named decline. Today the three gates in `ensureProcRegistered` (var formal, unreadable formals, stub body) already make an *unknown* magic decline — the hole is the fourth case, a magic with a real body, which is walked as that body (C-16), and the fact that nothing checks the name arms against the toolchain's list.

1. **A generated registry, checked in.** `src/nelli/smt/magic_registry.nim`: `const magicRegistry: seq[(magic: string, model: MagicModel, pin: string)]` with `MagicModel = enum mmArm, mmBody, mmDeclined, mmFold, mmNotRuntime` — the status column of §1, one entry per name (start from this report's 216 rows; `extract_magics.py` in the scratchpad produces the list). `mmArm` and `mmBody` entries name their pin test file.
2. **A guard test, `tsymex_rfc0016_magic_universe`**, that scans `querySetting(libPath)` (all of `lib/`, multi-line declarations: the s8bl scanner reads one-line `proc`s of system sources only, C-11) for every `{.magic: "X".}` and fails on a name absent from the registry, on an `mmArm`/`mmBody` entry whose pin file does not exist, and on a declaration with a real body whose entry is not `mmBody`. A toolchain bump then fails this test before anything else.
3. **Fail closed in the parser.** In `ensureProcRegistered`, after the stub-body gate: `if magic.len > 0 and registryModel(magic) != mmBody: decline("magic with a body no arm models")`. Then a newly-bodied magic declines by construction instead of being walked. `stubBody` stays as the first filter.
4. **A `case` with no `else` is not available** for the name arms — they key on operator spelling and operand class, not on `TMagic` — so the exhaustive `case` the brief suggests lives in the registry (item 1) plus the guard (item 2), not in the parser. What can be made exhaustive is the per-name switch at P:11868 (`case routineMagic(calleeSym)`): make it a `case` over a `MagicName` enum generated from the registry with `else: discard` removed, so that adding an entry forces a decision there.
5. **Operand-class coverage per arm.** For each `mmArm` entry the pin must cover every operand class the arm accepts — C-01 is a shape (literal divisor) inside a modelled magic, and C-04 is an overload (`&`(char, string)) inside one. The differential fuzzer of §4 is the right generator; until it exists, the pin file for each arm lists its operand classes (int widths, signed/unsigned, literal/const/variable operand, `range`, enum, char) as a table the test iterates.

**Stdlib routines.** Closure means every routine reachable from typical code is modelled by name (with a pin), walked by body (with a pin of the walked body against native), or declines with a named reason.

6. **A per-routine ledger generated from runs, not from memory.** Add a hint kind `feStdlibBodyWalked` recorded once per (module, routine) the walker inlines from `lib/`; a sweep over the corpus then prints the set of stdlib bodies the suite actually walks. That set, with a pin per routine, is the allowlist; a stdlib body outside it declines (`feStdlibUnpinned`). This is §2.1 applied to stdlib bodies. It costs precision on first contact (every `strutils` routine not yet pinned declines), which is why it is a ledger first and an allowlist second: promote routines as their pins land, and let the fuzzer (§4) target the ledger.
7. **Name every raise-text decline.** `eqBV on non-BV SymVal`, `A0: low/high on non-int-family type`, `unsupported infix operator`, the `#hook` text and `weInternalWalkerFault` are declines only because the message reaches the result; make each a `SymexErrorKind` (PRC-04's inventory) so the ledger of item 6 and the fuzzer can count them.
8. **Build-sensitivity is part of the registry.** Each entry carries a `buildAxes: set[BuildAxis]` (`baCCompiler` for C-01's fold and `sizeof`; `baZ3` for `replace`; `baPcre` for `re`; `baHashSeed` for table order; `baCRuntime` for `$float`/`formatFloat`; `baMemoryManager` for `repr`). An entry with a non-empty set is pinned on every CI leg that varies that axis or stays declined. INT-31 (`--cc`, `--opt` in the cache key) is the same requirement on the cache side.
9. **Liveness as a gate.** C-03 shows a stdlib body can hang the walker with no budget biting. Every body walk of a stdlib routine should run under the same bounded budget as a user routine *and* the guard test should run each ledger entry under `dt-bounded` once; a kill is a finding (RFC-0016 class `hang`), as CLAUDE.md already says for sweeps.

