# Lens A — Nim language constructs (statements, expressions, control flow)

Snapshot: `83c1d304` (read-only). Probes ran on eos `~/nelli/wt-rsA` (same sha, c backend, Z3 per the
worktree's `_deps/z3`, `scripts/dt-bounded.sh c probes/<name>.nim`). Probe sources are in
`research-out/probes/` (`common.nim` + `p_*.nim`); every `ran` claim quotes the probe's output line.

Path convention: bare `dsl_parser.nim` / `runtime.nim` / `types.nim` mean `src/nelli/smt/…`.

Status vocabulary (as asked): `modelled-exact`, `modelled-approx-tainted`, `declined:<kind>`,
`silently-approx`, `crash-or-compile-stop`, `unknown`. Every row says `read` (code read) or `ran`
(probe executed natively and under the walker).

## 0. Universe and how it was enumerated

The universe is the `NimNodeKind` enum of the dev image's `lib/core/macros.nim`
(`/opt/nim/2.2.10-patched/lib/core/macros.nim`, read via eos: 151 members, `nnkNone .. nnkOpenSym`).
Kinds that cannot appear in a `getImpl` proc body (type-section-only kinds such as `nnkObjectTy`,
`nnkRecCase`, `nnkEnumTy`; module-level `nnkImportStmt`; post-`transf` kinds such as `nnkChckRange*`,
`nnkClosure`, `nnkGotoState`, `nnkFastAsgn`, `nnkHiddenTryStmt`; and the pseudo kinds `nnkNone`,
`nnkError`, `nnkComesFrom`, `nnkReplayAction`, `nnkNilRodNode`) are listed once in §1.4 as "not
reachable, falls to the catch-all" and not expanded.

Two facts the whole matrix rests on (`read`):

- `parseStmtInner` dispatches on `n.kind` at `dsl_parser.nim:19149` and ends in
  `else: ctx.declineMarker(feUnsupportedStmtKind, …)` at `:20699`.
- `parseExpr` dispatches at `dsl_parser.nim:10187` and ends in the CR-2a catch-all
  `else:` at `:13379` (`feUnsupportedExprKind`, typed zero dummy, path tainted).

So an **unknown top-level kind already declines**. Every finding below lives one level down: inside an
arm, on a *child shape* the arm reads with `.repr`/`.strVal`, with a transparent `else:
parseExpr(operand)` fallback, or with a macro-time `error()`.

## 1. Coverage matrix

### 1.1 Statement kinds (`parseStmtInner`, `dsl_parser.nim:19122-20700`)

| construct | status | evidence | native pin exists? | 0016 row |
|---|---|---|---|---|
| `nnkStmtList`, `nnkStmtListExpr` (stmt position) | modelled-exact | `:19184` → `parseDeferList` `:16707` (`read`) | many suites | — |
| `nnkBlockStmt` incl. labelled `break L` | modelled-exact | `:19184`; label pushed in `parseStmt` `:20723-20733`; `resolveBreak` `:1646` (`read`) | `tsymex_rfc0005_s8m_exits*` (probed against compiler per its header) | — |
| `nnkDefer` (only inside a StmtList) | modelled-exact (as `try/finally`) | `parseDeferList` `:16711-16714` (`read`); defer writing `result` after `return`: `ran` p_defer `defer/wins: sxSat (2,)`, `ret_wins: sxUnsat`, native `2=>defer_wins` | **none** for the `result`-override shape → add | — |
| `nnkIfStmt` / `nnkIfExpr` (stmt) with `elif` preambles | modelled-exact | `:19187-19203`, `lowerCondChain` `:5611` (`read`) | `tsymex_rfc0005_r1_*` (R1-01) | — |
| `nnkIfStmt` unexpected arm kind | crash-or-compile-stop (unreachable in typed AST) | `error()` `:19202` (`read`) | n/a | — |
| `nnkAsgn` | modelled (lvalue shapes are the memory lens) | `:19204` → `parseAsgn` `:18576` (`read`) | S8bz/S8cq pins | PRC-34 |
| tuple assignment `(a, b) = (b, a)` | modelled-exact | `ran` p_defer `swap/swapped: sxSat (3,)`, `unswapped: sxUnsat`; native `3=>swapped` | **none** → add | — |
| `nnkSinkAsgn` | modelled-exact (as `=`) | `:19206` (`read`) | S8cb | — |
| `nnkWhileStmt` (k-unroll, guard preambles, `A and B` guards) | modelled-approx-tainted | `:19210-19258`, `mkShortCircuitWhile` `:15645-15800`; exhaustion taints `beBudgetExhausted` `runtime.nim:24014-24025` (`read`) | R14 suites, S8k | — |
| `nnkCaseStmt`, literal labels (int/char/enum/string/bool) | modelled-exact | `:19259-19306` (`read`) | phase/S8e suites | — |
| `nnkCaseStmt`, range label `of 2..4` (`nnkRange` child) | declined:feUnsupportedExprKind (tainted, sound) | label parsed by `parseExpr` `:19273` → catch-all `:13379`; `ran` p_declines `caserange/mid: sxUnknown errs=[feUnsupportedExprKind×2]`, native `2,3,4=>range_mid` | none | — (new, A-06) |
| `nnkCaseStmt` with an `elif` arm | **crash-or-compile-stop** | `error(&"unexpected case-arm kind …")` `:19300`; `ran` p_caseelif: `Error: unexpected case-arm kind nnkElifBranch` | none | — (new, A-03) |
| `nnkForStmt` over `a..b`/`a..<b` | modelled-exact for a symbol bound; modelled-approx-tainted for a non-symbol bound | `:19328-19350`: `hiIR` is inside the `while` cond, re-read each iteration (`read`). `ran` p_forbound: var bound `varbound/last3: sxUnsat`, `last0_x3: sxSat (3,)`, native `3=>last0_x3` (Nim's inline `..` aliases a plain var, walker agrees); `s.len` bound `seqbound/count2: sxSat {scIncomplete} beBudgetExhausted`, `count4: sxUnknown`, native always `count2` | none for either shape → add both | — (new, A-04) |
| `nnkForStmt` over `'a'..'c'` (char range) | modelled-exact | `ran` p_forbound `charrange/char_b: sxSat (1,)`, native `1=>char_b` | none → add | — |
| `for x in items(seq)` / `for i, x in pairs(seq)` incl. length change | modelled-exact (+ `seqIterLenChanged` → AssertionDefect/decline) | `:19462-19500`, `:18988` (`read`) | S8z, S8cn `_lentnative` | PRC-05 |
| `for x in array` / `for x in set` (unrolled) | modelled-exact | `:19425-19451`, `:19501-19540` (`read`) | S8m (`for v in [1,2,3]: break`) | — |
| `for x in string` | declined:feUnsupportedStmtKind | `:19374-19390` (`read`) | — | string lens |
| `for x in mitems/mpairs` | modelled (S8bu) | `:19351-19353` (`read`) | S8bu | — |
| `for x in <other container>` (Table via S8bc, else) | declined:feUnsupportedStmtKind | `:19543` (`read`) | — | PRC-05 |
| `for … in userInlineIterator(args)` | modelled-exact by inlining, formals substituted by name (aliasing kept), `var` formals by ref | `:19544-19731`, `bindIterArg` (`read`) | S8bs | — |
| iterator with no surface `yield` / with `return` / recursive / non-literal default / closure iterator | declined:feUnsupportedStmtKind (`ceNotImplemented` for closure iterators) | `:19613-19631`, `:19640-19653`, `:10403-10420` (`read`) | — | — (A-13, precision) |
| `break`/`continue` in a for body over a user iterator | declined:feUnsupportedStmtKind | `:19623-19626` (`read`) | — | — (A-13) |
| `yield` under `case`/`for`/`try` inside an inlined iterator | declined:feUnsupportedStmtKind | `parseIterBodyStmt` handles only yield/stmtlist/block/while/if `:15966-16082`; other kinds go to `parseStmt`, whose `nnkYieldStmt` falls to `:20699` (`read`) | — | — (A-12) |
| `nnkBreakStmt` / `nnkContinueStmt` (plain, labelled, through `finally`, in unrolled loops) | modelled-exact | `:19735-19738`, `:1615-1670`; walker `exitJump` `runtime.nim:20236` (`read`) | `tsymex_rfc0005_s8m_exits*` | — |
| `break L` naming a block that is not a modelled target | declined:feUnsupportedStmtKind | `:1657-1659` (`read`) | — | — |
| `nnkReturnStmt` (bare, `return expr`, `return` inside `try` with `finally`) | modelled-exact | `:19739-19751`; `exitReturn` parks at the innermost `finally` `runtime.nim:20223-20234`; return writes `env["result"]` before parking `runtime.nim` `of isReturn` (`read`) | S8m | — |
| `return` inside a `finally` running on a raised path | declined:eeFinallyReturnOnRaise (backends disagree: c re-raises, cpp returns) | `runtime.nim` `of isReturn` first branch (`read`) | S8m header records the c/cpp split | — (A-15: candidate "stays declined") |
| `nnkLetSection`/`nnkVarSection`, `IdentDefs` | modelled-exact (zero-init, `{.global.}` skipped, `{.noinit.}` modelled or declined, unsafe-cast RHS declined, iterator value declined) | `:19752-19917` (`read`) | S8be, S8bz | — |
| `let (a, b) = f()` (tuple unpacking) | modelled-exact (semcheck desugars to three `IdentDefs` before the macro) | note at `:14323-14331` (`read`); `tsymex_r5_tuple_return` | yes (r5) | — |
| `var a, b = f()` (one initialiser, two names) | modelled-exact | `ran` p_conv `multi/twice: sxSat (1,)`, `once: sxUnsat`, `a_one: sxSat (2,)`; native `1=>twice 2=>a_one` (Nim evaluates per name; walker agrees) | none → add | — |
| `nnkCall`/`nnkCommand` (stmt) | modelled per callee (call lens) | `:19918-20346` (`read`) | — | — |
| `nnkDiscardStmt` | modelled-exact (walked as a sink `let`) | `:20347-20383` (`read`) | v68 suites | — |
| `nnkEmpty`, `nnkCommentStmt` | modelled-exact (no-op; stale-element marker comment → `feUnsupportedOp`) | `:20384-20390` (`read`) | S8ax | — |
| `nnkConstSection`, `nnkBindStmt`, `nnkMixinStmt` | modelled-exact (no runtime footprint) | `:20391-20412` (`read`) | — | — |
| `nnkRaiseStmt` `raise newException(T, msg)`, bare `raise` | modelled-exact | `:20413-20443` (`read`) | E1/E4 suites, S8b | — |
| `raise <value>` (`raise e`, `raise getCurrentException()`, a `let`-bound exception) | declined:eeUnknownExnType (typeId is the expression's `repr`) | `:20444` `mkRaise(oc.repr, nil)`; `runtime.nim:25737` (`read`); `ran` p_declines `raisevalue/caught: sxUnknown errs=[eeUnknownExnType]`, native `2=>caught_value` | none | — (new, A-05) |
| `nnkTryStmt` with `except T:` / `except A, B:` / bare `except:` / `finally` | modelled-exact | `:20446-20473`; handler match `runtime.nim:25751-25756` (`read`) | E-suites, R3-01 pin | — |
| `nnkTryStmt` with **`except T as e:`** | **silently-approx → false verdicts** | `:20460` `canonicalExnTypeSym(arm[j])` on an `nnkInfix(as, T, e)` returns it unchanged, `:20461` `typeIds.add tnode.repr` = `"ValueError as e"`; never equal to a raised typeId. `ran` p_exceptas: `as/caught_as: sxUnsat` (clean), `as/raised: sxRaised` (clean), native `3=>after+caught_as`; control `plain/caught: sxSat (3,)`, `plain/raised: sxUnsat` | **none** (every `as e` in `tests/` is harness code, not a SUT) | — (new, A-01) |
| `try` as an expression | declined:feUnsupportedExprKind | `parseExpr` has no `nnkTryStmt` arm → `:13379`; `ran` p_declines `tryexpr/99: sxUnknown`, native `1=>tryexpr99` | none | — (A-06) |
| `nnkInfix` stmt: `+= -= *= &=` on a symbol / deref / index | modelled-exact with range-step checks; lvalue-with-call declines | `:20474-20688` (`read`) | S8bl, S8cq | — |
| `nnkPragmaBlock`: raw `assert`/`doAssert` expansion | modelled-exact (`AssertionDefect` raise) | `:19164-19168` (`read`) | E6 | — |
| `nnkPragmaBlock`: `{.cast(uncheckedAssign).}` | modelled (S8cp item 2); address of discriminator declines | `:19172-19181` (`read`) | S8cp | SND-07 |
| `nnkPragmaBlock`: any other (`{.cast(noSideEffect).}`, `gcsafe`, `raises`) | modelled-exact (transparent; these pragmas have no runtime meaning) | `:19183` (`read`) | — | — |
| routine definitions in a body (`nnkProcDef`, `FuncDef`, `IteratorDef`, `TemplateDef`, `MacroDef`, `MethodDef`, `ConverterDef`) | modelled-exact (no-op at the declaration; body reached at the call) | `:20689-20698`, `routineShapedForClosureDetect` `:81` (`read`) | S8an | — |
| `nnkWhenStmt` (only `when nimvm` survives semcheck) | declined:feUnsupportedStmtKind | `:20699`; `ran` p_declines `nimvm/rt1: sxUnknown errs=[feUnsupportedStmtKind]`, native `1=>rt1` | none | — (A-06) |
| `nnkPragma` statement (`{.emit.}`, `{.push …}` inside the body, `{.linearScanEnd.}` …) | declined:feUnsupportedStmtKind (+ S8cu's source scan for `push` check options) | `:20699` (`read`); S8cs for `emit` in callees | S8cs, S8cu | PRC-04, PRC-07 |
| `nnkAsmStmt` | declined:feUnsupportedStmtKind | `:20699` (`read`); S8cs treats it as foreign code `:3861-3876` | — | PRC-04 |
| `nnkTypeSection` in a body | declined:feUnsupportedStmtKind | `:20699` (`read`) | — | PRC-22 |
| `nnkStaticStmt` | declined:feUnsupportedStmtKind | `:20699` (`read`) | — | — |
| `nnkYieldStmt` outside an inlined iterator | declined:feUnsupportedStmtKind | `:20699` (`read`) | — | — |
| `nnkParForStmt`, `nnkUsingStmt`, import/export/include kinds | declined:feUnsupportedStmtKind (not reachable in a proc body except `using`) | `:20699` (`read`) | — | — |

### 1.2 Expression kinds (`parseExpr`, `dsl_parser.nim:10143-13432`)

| construct | status | evidence | native pin exists? | 0016 row |
|---|---|---|---|---|
| literals: `nnkNilLit`, int/uint/char/float/str kinds | modelled-exact | `:10188-10217`, `:10364` (`read`) | many | — |
| `nnkFloat32Lit` (`var g: float32 = 0.1`) | modelled-exact as a 32-bit literal, **but every conversion around it is transparent** (next rows) | `:10216-10217` (`read`); `ran` p_arith `f32lit/exact: sxSat (1,)` clean, `lit_narrow: sxUnsat`; native `1=>lit_narrow` | none | — (A-02) |
| `nnkIdent`/`nnkSym` (locals, globals with route proofs, enum fields, `result`) | modelled (global routes are the memory lens) | `:10218-10363`; `runtime.nim:9364-9400` (`read`) | S8as, S8cs | PRC-04, INT-10 |
| `nnkCaseStmt` in expression position | modelled-exact (`hoistCaseExpr`) | `:10366-10375`, `:5657` (`read`) | s1 | — |
| `nnkPar` / `nnkStmtListExpr` (statements then value) | modelled-exact (statements go to the preamble in order) | `:10376-10379` (`read`) | — | — |
| `nnkLambda`, `nnkProcDef`/`nnkFuncDef` as value | modelled (closure lens) | `:10394-10402` (`read`) | — | — |
| `nnkIteratorDef` as value (closure iterator) | declined:ceNotImplemented | `:10403-10420` (`read`) | — | — (A-13) |
| `nnkCast` same-type ref/ptr | modelled-exact; any other `cast` | declined:feUnsupportedExprKind | `:10424-10450` (`read`) | S8m (3) | PRC-14, PRC-17 |
| `nnkConv` int↔float, bool→int, int-family widths (checked narrowing, unsigned wrap, reinterpret), `range`/enum targets (RangeDefect), object hierarchy | modelled-exact | `:10461-10657` (`read`); `ran` p_conv `char/past255: sxRaised`, `char/RangeDefect: sxRaised`, native `256..260 => RangeDefect`; p_arith `i8/past: sxRaised`, native `128..135 => RangeDefect` | **none** for `char(x)`/`int8(x)` → add | — |
| **`nnkConv` any other pair → `else: parseExpr(operand)` (transparent)**: `float32(f64)`, `float(f32)`, `cstring(s)`, `string(cs)`, … | **silently-approx** | `:10658-10659` (`read`); `ran` p_conv `f32/narrowed: sxUnsat` clean vs native `1,2,3,4,6,7=>narrowed`; `f32/exact_x1: sxSat (1,)` clean vs native never | none | — (new, A-02) |
| `nnkHiddenStdConv`/`nnkHiddenSubConv`: empty `@[]`, index convs, range check (S8i), widening, hidden narrowing (declined), openArray/`toOpenArray` views | modelled-exact / declined:feUnsupportedOp | `:10660-10844` (`read`) | S8i, S8j, S8cn views | PRC-05 |
| `nnkHiddenStdConv` any other → `else: parseExpr(wrapped)` | silently-approx (same class as the `nnkConv` fallback; float32 literal→float64 param is one instance) | `:10845` (`read`) | none | — (A-02) |
| `nnkHiddenCallConv` (converters) | modelled (walked as a call) | `:10846-10888` (`read`) | — | — |
| `nnkAddr` of a local cell / seq element / arm field | modelled (S8ax/S8be cells); other `addr` | declined (`heUnsafeCast` family) | `:10889-10913` (`read`) | S8ax, S8be | PRC-14, PRC-28 |
| `nnkDerefExpr`/`nnkHiddenDeref` | modelled (heap lens) | `:10914-10964` (`read`) | — | — |
| `nnkCheckedFieldExpr` | modelled (variant lens) | `:10965-10968` (`read`) | — | — |
| `nnkInfix` arithmetic/comparison/`and`/`or`/`xor`/`shl`/`shr`, unsigned ops, string `&`, `==` on refs | modelled-exact (short-circuit operands keep their own preambles; `div`/`mod` truncate like C via `truncDivInt`; overflow/div-by-zero forks) | `:10969-11181`, `runtime.nim:8211-8230`, `:8800-8912` (`read`) | A1 arithmetic, S8i, S8bv | — |
| `nnkInfix` any other operator | declined:feUnsupportedOp | `:11070-11080` (`read`) | — | — |
| `nnkPrefix` `not` (bool), `-`, `+`, `$`, `@` | modelled-exact | `:11182-11242` (`read`) | — | — |
| `nnkPrefix` `not` on an int that is a Z3 Int (bitwise not) | declined:weInternalWalkerFault | `runtime.nim:10483-10490` (`read`); `ran` p_arith `notint/not2: sxUnknown errs=[weInternalWalkerFault]`, native `2=>not2` | none | — (A-07) |
| `nnkPrefix` any other non-user operator | crash-or-compile-stop | `error("symex: unsupported prefix operator …")` `:11243` (`read`, not probed) | — | — (A-08) |
| `nnkBracket` (array literal) | modelled-exact | `:11244-11250` (`read`) | — | — |
| `nnkBracketExpr` (index: seq/array/string/tuple/Table) | modelled (IndexDefect forks); non-literal tuple index → `error()` (Nim rejects it earlier, unreachable); unsupported receiver → declined | `:11251-11349`, `:11287`, `:11342` (`read`) | S8bz | PRC-23 |
| `nnkDotExpr` (field read) | modelled (type lens) | `:11350-11557` (`read`) | — | — |
| `nnkCurly` (set literal) | modelled (set lens) | `:11558-11573` (`read`) | — | — |
| `nnkCallStrLit` (`re"…"`) | modelled (regex lens) | `:11574-11586` (`read`) | — | — |
| `nnkCall` (magics, stdlib, user routines, markers) | modelled per callee; `parseRoutineCallExpr` fallback; markers in expression position → `error()` | `:11587-12745`, `:11589` (`read`) | — | call lens |
| `nnkCommand` in expression position (`let y = succ x`) | declined:feUnsupportedExprKind (no arm; catch-all) | `ran` p_declines `cmd/3: sxUnknown errs=[feUnsupportedExprKind×2]`, native `2=>cmd3` | none | — (A-06) |
| `nnkIfExpr` | modelled-exact (hoisted, `lowerCondChain`) | `:12746-12792` (`read`) | M5, R1-01 | — |
| `nnkTupleConstr`, `nnkObjConstr` | modelled (type/variant lens) | `:12793-13378` (`read`) | — | — |
| `nnkBlockStmt`/`nnkBlockExpr` in expression position (`let v = block: …`) | declined:feUnsupportedExprKind | `ran` p_declines `blockexpr/7: sxUnknown`, native `3=>blockexpr7` | none | — (A-06) |
| `nnkRange` (only as a case label or slice bound) | declined:feUnsupportedExprKind (as a label); slices handled by `parseStrSliceBound`/seq slice code | `:13379`; `:2800` (`read`) | — | — (A-06) |
| `nnkObjDownConv`/`nnkObjUpConv` bare, `nnkStringToCString`, `nnkCStringToString`, `nnkDo`, `nnkPostfix`, `nnkExprEqExpr` (named args: resolved by semcheck), `nnkStaticExpr` (folded), `nnkPragmaExpr`, `nnkTableConstr`, `nnkCurlyExpr`, `nnkAccQuoted`, `nnkOpenSym`, `nnkType`, `nnkWhileStmt`/`nnkForStmt` in expression position | declined:feUnsupportedExprKind (catch-all) | `:13379-13431` (`read`) | — | — |
| quit / rawQuit (`isExitCall`) | modelled-exact (`assume(false)` after evaluating the arguments) | `:7514-7520`, `:11903-11905` (`read`) | S8ax | — |
| user `{.noreturn.}` routine | modelled (walked; its own raise or `quit` ends the path) | `:3581-3600` (`read`) | — | — |
| `nnkWhileStmt`/`nnkCaseStmt`/`nnkIfStmt` nested in any of the above | same as their stmt rows | — | — | — |

### 1.3 Walker-side control-flow semantics checked (`runtime.nim`, `read`)

| semantics | status | evidence |
|---|---|---|
| `try` without `finally`: pending returns/jumps pass through (parked only at a `finally`) | modelled-exact | `exitReturn` `:20223-20234`, `claimAt` by depth `exits.nim:97-107` |
| `finally` on normal / return / jump / raise exits, innermost first | modelled-exact | `of isTry` `:24322-24380` |
| raise of a type not in the tables | modelled-approx-tainted (`eeUnknownExnType`) | `:25735-25760` |
| handler match: exact string or `isSubtypeOf` over `exnTable` + user hierarchy | modelled-exact given a correct typeId | `:25751-25756` (the typeId is where A-01 breaks) |
| `while` k-unroll exhaustion | modelled-approx-tainted (`beBudgetExhausted[AssumedBound]`) | `:24005-24030` |
| labelled `break`/`continue` through `finally` and from `except` arms | modelled-exact | `exitJump` `:20236-20260`; S8m pins |

### 1.4 Kinds not reachable in a `getImpl` body (fall to the catch-alls, `read`)

`nnkNone`, `nnkError`, `nnkComesFrom`, `nnkReplayAction`, `nnkNilRodNode`, `nnkModuleRef`,
`nnkChckRange`, `nnkChckRange64`, `nnkChckRangeF`, `nnkClosure`, `nnkGotoState`, `nnkState`,
`nnkBreakState`, `nnkFastAsgn`, `nnkHiddenTryStmt`, `nnkStmtListType`, `nnkBlockType`,
`nnkTypeClassTy`, `nnkTupleClassTy`, `nnkStaticTy`, `nnkRecList`, `nnkRecCase`, `nnkRecWhen`,
`nnkOfInherit`, `nnkGenericParams`, `nnkFormalParams`, `nnkArgList`, `nnkPattern`, `nnkWith`,
`nnkWithout`, `nnkImportAs`, `nnkTypeOfExpr`, `nnkImport*`, `nnkExport*`, `nnkFromStmt`,
`nnkIncludeStmt`, `nnkTypeDef`, `nnkConstDef`, `nnkEnumFieldDef`, `nnkIdentDefs`/`nnkVarTuple`
(only as children), `nnkElifBranch`/`nnkElifExpr`/`nnkElse`/`nnkElseExpr`/`nnkOfBranch`/
`nnkExceptBranch`/`nnkFinally` (children, handled inside their parents), `nnkBind`,
`nnkClosedSymChoice`/`nnkOpenSymChoice` (resolved before `getImpl`), `nnkVarTy`/`nnkRefTy`/… (type
nodes). The parser never crashes on them: both dispatches decline by default.

## 2. Findings

| id | construct | class | minimal SUT | evidence | suggested native pin | effort |
|---|---|---|---|---|---|---|
| **A-01** | `except T as e:` in a SUT | **soundness-confirmed** (false `sxUnsat` on the handler's label; false clean `sxRaised`) | `proc f(x: int) = try: (if x == 3: raise newException(ValueError, "")) except ValueError as e: (if e.msg.len >= 0: symexTarget("c"))` | `dsl_parser.nim:20457-20462`: the arm's child is `nnkInfix(as, T, e)`; `canonicalExnTypeSym` (`:1488`) returns a non-`nnkType`/non-`nnkSym` node unchanged, so `typeIds.add tnode.repr` stores `"ValueError as e"`; `runtime.nim:25751-25756` compares typeIds by string/subtype and never matches. `ran` p_exceptas: `SYMEX as/caught_as: sxUnsat … errs=[]`, `SYMEX as/raised: sxRaised … errs=[]`; `NATIVE as: 3=>after+caught_as`; control `plain/caught: sxSat witness=(3,)`, `plain/raised: sxUnsat` | `tsymex_rfc0016_a01_exceptas`: the SUT above + a native loop over 0..7; also `except T as e` where `e.msg` / `e.name` is read, and nested `try` in the `as` handler (R3-01's shape) | s (unwrap the `as` infix: type = `arm[j][1]`, bind `arm[j][2]` to the in-flight exception as `getCurrentException()` is bound today) |
| **A-02** | float32↔float64 conversions (`float32(f)`, `float(g)`, a `float32` variable initialised from a literal, hidden float convs) | **soundness-confirmed** (false clean `sxSat` and false `sxUnsat`) | `proc f(x: int) = let v = float(x)/10.0; let g = float32(v); if float(g) != v: symexTarget("narrowed")` | `dsl_parser.nim:10451-10659`: `nnkConv` has int↔float, int-family and hierarchy arms and ends in `else: parseExpr(operand, …)` (`:10658`); the hidden-conv arm ends the same way (`:10845`). No `iekConvFloatWidth` exists (`types.nim` IR kinds: `iekConvIntToFloat`, `iekConvFloatToInt`, `iekConvIntWidth`, `iekConvIntReinterpret` only). `ran` p_conv: `f32/narrowed: sxUnsat errs=[]` vs `NATIVE f32: 1,2,3,4,6,7=>narrowed`; `f32/exact_x1: sxSat witness=(1,) errs=[]` vs native never. `ran` p_arith: `f32lit/exact: sxSat witness=(1,)` vs native never; `f32lit/narrow: sxUnsat` vs `1=>lit_narrow` | `tsymex_rfc0016_a02_floatwidth`: the three shapes (explicit narrowing, widening back, literal into a `float32` var), native over 0..7, c and cpp | s–m (model with `fp.to_fp` RNE between the two sorts, or decline every float conversion pair not on an allowlist per §2.1; `float32 / float32` already declines `feUnsupportedOpAborted`, `ran` p_arith `f32arith/*: sxUnknown`) |
| **A-03** | `case x: of 1: … elif cond: … else: …` | **crash (compile stop)** | `proc f(x: int) = (case x; of 1: symexTarget("one"); elif x > 5: symexTarget("big"); else: discard)` | `dsl_parser.nim:19298-19300` `else: error(&"unexpected case-arm kind {arm.kind}", arm)`; `ran` p_caseelif: `probes/p_caseelif.nim(8, 3) Error: unexpected case-arm kind nnkElifBranch`. Same gap in `hoistCaseExpr` for the expression form (`:5657ff`, `read`); the if-expr arm has the same `error()` at `:12789` | `tsymex_rfc0016_a03_caseelif` (sat on `big`, native 6,7) | xs (feed `nnkElifBranch` arms into the same if-chain through `lowerCondChain`, each with its own preamble; §2.4 counts a compile stop as worse than a decline) |
| A-04 | `for i in a .. b` where `b` is not a plain symbol (`s.len`, `t.x`, `f()` after hoisting) and the body changes it | precision (tainted `beBudgetExhausted`), with a soundness caveat for any future "fix" | `proc f(x: int) = var s = @[1,2]; var c = 0; for i in 0 ..< s.len: (if x > 2: s.add 9); inc c; if c == 2: symexTarget("two")` | `dsl_parser.nim:19328-19350`: `hiIR` sits inside the `while` condition and is re-read per iteration. Nim's inline `..` iterator aliases a **symbol** argument (`transf` direct mapping) but evaluates a non-symbol into a temp once. `ran` p_forbound: `seqbound/count2: sxSat … runTaint {scIncomplete} errs=[beBudgetExhausted]`, `count4: sxUnknown`; native always `count2`. The symbol case is already right: `varbound/last0_x3: sxSat (3,)`, `last3: sxUnsat`; native `3=>last0_x3` | `tsymex_rfc0016_a04_rangebound`: BOTH shapes natively (the alias one must stay aliased) | xs–s (hoist a non-symbol `lo`/`hi` into a synth `let`; keep symbol bounds live) |
| A-05 | `raise <value>` (`raise e`, `raise getCurrentException()`, `let e = newException(…); raise e`) | precision (declines `eeUnknownExnType`) | `let e = newException(ValueError, "v"); try: (if x == 2: raise e) except ValueError: symexTarget("c")` | `dsl_parser.nim:20444` `mkRaise(oc.repr, nil)`; `runtime.nim:25737`. `ran` p_declines: `raisevalue/caught: sxUnknown errs=[eeUnknownExnType/sevWarning]`, native `2=>caught_value` | pin after the fix | s (static type of the value via `getTypeInst`, re-raise semantics for the in-flight object) |
| A-06 | five catch-all declines on everyday syntax: `try` as expression; `block` as expression; command-syntax call in expression position (`succ x`); `case` range label `of 2..4`; `when nimvm` | precision (all `sxUnknown`, sound) | p_declines SUTs | `ran` p_declines: `tryexpr/99`, `blockexpr/7`, `cmd/3`, `caserange/mid` → `feUnsupportedExprKind`; `nimvm/rt1` → `feUnsupportedStmtKind`; native hits each | one pin per shape after lifting | xs each (`nnkCommand` → the `nnkCall` arm; range label → `lo <= s and s <= hi`; `when nimvm` → walk the `else` branch; try/block-expr → the `hoistCaseExpr` A-normalisation) |
| A-07 | bitwise `not x` on an int carried as a Z3 Int | precision (`weInternalWalkerFault` decline, reported as a fault) | `let y = not x; if y == -3: symexTarget("t")` | `runtime.nim:10483-10490`; `ran` p_arith `notint/not2: sxUnknown errs=[weInternalWalkerFault]`, native `2=>not2` | pin after fix | xs (`-x - 1` on the Int representation; and reclassify from a walker fault to a named decline until then) |
| A-08 | `nnkPrefix` with a non-builtin operator that is not a user callee | crash (compile stop) suspected, not probed | a stdlib prefix operator on a stdlib type (e.g. `-` on `Duration` is `isUserCallee`? unverified) | `dsl_parser.nim:11243` `error("symex: unsupported prefix operator …")` (`read`) | probe first | xs (→ `declineAtSite(feUnsupportedOp)`) |
| A-09 | markers in expression position; `symexTarget` with a non-literal name; unresolved callee in untyped input | crash (compile stop), by design | — | `:11589`, `:19924`, `:11607` (`read`) | — | — (record as "stays": not reachable from a typed SUT) |
| A-10 | `return` inside `finally` on a raised path | declined `eeFinallyReturnOnRaise`; **c and cpp disagree natively** | S8m header shape `for i in 0..1: (try: raise … finally: break)` | `runtime.nim` `of isReturn` (`read`); S8m header records the backend split | already recorded in S8m's header | — (candidate "declined with reason it stays": the theory cannot express a backend-dependent result; record per §3.3 item 1) |
| A-11 | `yield` under `case`/`for`/`try` inside an inlined iterator; `return` in an iterator; `break`/`continue` in the for body over a user iterator; recursive / closure iterators; non-literal defaults | precision (declines) | `iterator it(): int = (for k in 0..2: yield k)`; `for v in it(): …` | `dsl_parser.nim:15966-16086`, `:19613-19631`, `:19640-19653`, `:10403-10420` (`read`) | pins per shape after lifting | m (the `break`-in-body case needs the unrolled-block label plumbing S8m already has for arrays) |
| A-12 | `float32` arithmetic (`float32 / float32`) | precision (`feUnsupportedOpAborted`) | `let a = float32(x) / 3'f32` | `ran` p_arith `f32arith/exact: sxUnknown errs=[feUnsupportedOpAborted]` | — | float lens |
| A-13 | positive results with **no native pin** (modelled-exact, confirmed by probe only): `defer` writing `result` after `return v`; tuple swap `(a, b) = (b, a)`; `var a, b = f()` evaluated per name; `char(x)` and `int8(x)` RangeDefect; `'a'..'c'` char-range loop; range bound aliasing a plain var | test-harness (turn the probe lines into pins so these do not regress silently) | p_defer, p_conv, p_arith, p_forbound SUTs | `ran`: all SYMEX lines agree with the NATIVE lines (quoted in §1) | `tsymex_rfc0016_a13_constructs_native` (one file, the six SUTs + native loops) | xs |

Severity against `main` (`6cbfe8f`) was not measured (no `main` worktree on eos was available to this
lens and the brief forbade other worktrees); A-01 and A-02 are in code paths that predate RFC-0005
(Phase 15 E1 / F2), so "same as `main`" is the expectation, to be confirmed by the three-way row
before work (§5.7 rule).

Refuted suspicions (recorded so nobody re-chases them): `for i in 0..n` with `n` written in the body
(walker and Nim both re-read a plain symbol bound); `var a, b = f()` (both evaluate twice);
`char(x)`/`int8(x)` range checks; `defer` overriding `result`; tuple swap. All `ran`.

## 3. How to make this axis closed

What already holds (`read`): the two top-level dispatches are closed by a declining `else`
(`dsl_parser.nim:20699`, `:13379`). A brand-new `NimNodeKind` cannot be silently approximated at the
top level. Every finding here is one level down. The closure therefore has to be enforced at three
places, mechanically:

1. **Child-shape census, not kind census.** A-01 (`nnkInfix(as)` under `nnkExceptBranch`), A-03
   (`nnkElifBranch` under `nnkCaseStmt`), and the range label (`nnkRange` under `nnkOfBranch`) are
   children the parent arm reads positionally. Add a macro-time test that `getImpl`s a corpus of
   SUTs (one per construct row of §1, generated from a table of source snippets) and asserts, per
   top-level statement, that the parser's result is either an IR with no `isUnsupported` node or a
   decline whose `SymexErrorKind` is named in the table; a macro `error()` fails the test. The
   corpus is the matrix above; the test is the gate that keeps it closed when Nim's typed AST
   changes shape (the `except … as` shape is exactly such a change the parser never caught up with).

2. **No transparent fallbacks.** Grep-gate (like R4-04's `parkExit` gate) `dsl_parser.nim` for
   `else:\n parseExpr(` / `parseExpr(operand` / `parseExpr(wrapped` as the last branch of a `case`
   or if-chain on a node kind, and for `error(` inside `parseStmtInner`/`parseExpr`/`hoistCaseExpr`.
   Each hit must be either (a) rewritten to an allowlisted match + `declineAtSite` (§2.1), or (b)
   annotated with a `## closed:` comment the gate recognises, naming the pin that proves the
   fallthrough exact. Today's hits: transparent fallbacks `:10658`, `:10845` (A-02); macro `error()` sites `:19300`
   (A-03), `:19202`, `:12789`, `:11238`, `:11243` (A-08), `:11287`, `:11451`, `:11483`, `:11535`
   (seq/field accessors, type lens), `:11589`, `:11607`, `:19924` (A-09, by design).

3. **Type ids come from symbols, never from `repr`.** `:20444` (`raise <value>`) and `:20461`
   (`except` arm) build exception type ids from `repr`. A `typeIdOf(node): Option[string]` that
   accepts only `nnkSym`/`nnkType`/alias-resolved symbols, and whose `none` is a decline
   (`eeUnknownExnType`), closes A-01 and A-05 together and leaves no third place to add a string.

4. **Exhaustive `case` over `NimNodeKind` with no `else`, grouped.** Replace the `else` at `:20699`
   and `:13379` with explicit arms listing every remaining member (the §1.4 set plus the declined
   stmt/expr kinds) in one `declineMarker` arm. Then a Nim upgrade that adds a kind fails the
   compile of nelli itself instead of being declined by accident, and a reader can see the whole
   universe in the source. The census test in (1) reads that arm's set to know what it must cover.

5. **Fuzzer family for this axis.** §4.2's generator targets the memory-sharing class. Add a
   `constructs` family whose alternatives are the rows of §1 (each a small source template with
   integer holes), so the differential harness walks the closed universe and its neighbours
   (construct × construct nesting: `try` in `for` in `block`, `case` in `while` with `continue`),
   which is where R3-01 (try-in-except) and S8m's defects lived.

6. **Backend-split declines stay declined, and say so.** A-10 (`return` in `finally` on a raised
   path, c vs cpp) is the one cell in this axis the theory cannot express; record it under §3.3
   item 1 as "declined, reason: native result is backend-dependent", with the S8m probe lines as
   the evidence, so it is not reopened as precision.
