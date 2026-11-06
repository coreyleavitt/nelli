# Lens B — types and the memory model (value vs shared memory, aliasing, copy/move)

Snapshot read: `scratchpad/research` at 83c1d304. Probes ran on eos `~/nelli/wt-rsB`
(same sha), `scripts/dt-bounded.sh c|cpp probes/<name>.nim`, Z3 5.1, Nim 2.2.10
container image, `--threads:on`; default `--mm:orc` unless a `.cfg` says otherwise.
Every claim is tagged `read` (code) or `ran` (probe output quoted in §5).

Probe harness (`probes/p_hdr.nim`, ran): each SUT takes `k: int`, guards its own
domain (`0..7`, or wider where stated), places `symexTarget` labels; a native loop
calls the SUT on every value of the domain under `symexCaptureBegin/End`
(Defects caught), then `symexFind(fn, tLabel(lbl))` runs per label and the line
`PROBE <lbl> walker=<status> native=<hit> <verdict> [<errors>]` is printed.
`MISMATCH-falseUnsat` / `MISMATCH-falseSat` is a confirmed soundness finding; a
`sxRaised` row was checked only for "no native hit" (exception type not compared).

Paths: bare `dsl_typebridge.nim`, `dsl_parser.nim`, `types.nim`, `runtime*.nim`
mean `src/nelli/smt/…`.

---

## 1. Coverage matrix — type family × memory operation

Status vocabulary: `modelled-exact` (model + native pin), `approx-tainted` (model is
wider than Nim and the result carries a taint/decline), `declined:<kind>` (named
decline by construction), `declined-accidental` (declines, but through an arm that
was not written for the shape — a neighbour may not decline), `silently-approx`
(no decline, model may differ from Nim), `crash`, `unknown` (not read deep enough
or not probed).

### 1.1 Type families (what `classifyType` makes of them)

| Family | IRType | Status | Evidence | Native pin | 0016 row |
|---|---|---|---|---|---|
| `int`, `int8..64`, `uint`, `uint8..64` | `itInt(width, signed)` | modelled-exact | `dsl_typebridge.nim:1774-1788` (read) | `p_intconv` (ran): `uint8(300)` wraps natively and in the walker; `int8(200)`, `int(high uint64)`, `int32(high uint32)` raise natively, walker `sxRaised` | — |
| `Natural`, `Positive` | ranged `itInt` | modelled-exact | `:1789-1790` (read) | s8cq_native | — |
| `range[lo..hi]` inline / alias / enum subrange | `itInt(hasRange)` | modelled-exact | `:1327-1333`, `:1446-1466` (read) | issue #162/#163 suites | — |
| `range` declared in a routine body (`type R = range[...]` inside the SUT) | — | declined:`feUnsupportedStmtKind` (type section) | `p_intconv ic_range_*` (ran) | — | PRC-22 |
| `distinct T` (incl. nested) | `itDistinct(base)` fresh sort, inject/eject | approx-tainted (`geDistinctBijectivitySkipped`, `geDistinctBarrier`) | `:1402-1414` (read); `typeCopiedByValue` follows the base `dsl_parser.nim:7849-7852` (read) | s8cq_native `DI`, `OD` | — |
| stdlib `Rune` | ranged `itInt` [0,0x10FFFF] by symbol | modelled-exact | `:1409-1411` (read) | — | — |
| `enum` ordinary / negative ordinals | ranged `itInt(minOrd..maxOrd)`, `enumName` | modelled-exact for members; the lift admits **holes** | `:1500-1559` (read) | `$`-of-enum SND-04 | SND-04 |
| `enum` with holes | same lift, holes model-reachable | silently-approx (a hole ordinal is a value in the model; natively `H(3)` is also produced unchecked — `p_intconv ic_holey_3` native=true (ran); walker declined on the local type section, so the module-level cell is **unknown**) | `:1500-1559` (read) | none | PRC-35 |
| string-named enum (`eA = "x"`) | as enum | modelled-exact per SND-04 fix | — | SND-04 | SND-04 |
| `bool` | `itBool` | modelled-exact | `:1775` | — | — |
| `char` | `itInt(8, unsigned, isChar)` | modelled-exact; `chr(k)` RangeDefect pending `p_arith ar_chr_*` | `:1777` (read) | `p_intconv ic_char_*` (ran, agree) | — |
| `float32`, `float64` | `itFloat32/64` Z3Fp | modelled (`runtime_floats.nim`); float→int of NaN/inf `feConvFloatToIntUndefined` | `types.nim:71-72` (read) | 13 `*float*` suites | PRC-35 (`$float`) |
| `string` | `itString` byte-faithful | modelled-exact; `$` of int/char/enum SND-02..04 | memory note `symex-string-model` | s8cb | SND-02..04 |
| `cstring` | catch-all `__unsupported:cstring` | declined:`feUnsupportedParamType` (param) / scoped decline (local); as an effect, `pointer`/`cstring` reach sets `acc.heapAll` `dsl_parser.nim:3532` (read) | `:1832-1848` (read) | none | — |
| `seq[T]`, `openArray[T]` | `itSeq(elem)` (one model for both) | modelled; nested `seq[seq[T]]` declined:`seNestedSeqUnsupported` (`p_refshare rs_seqseq_*` ran) | `:1735-1741` (read) | s8cn seqview | PRC-11, PRC-23, PRC-29 (`var openArray` view) |
| `varargs[T]` | arg-side unwrapping of the `nnkHiddenStdConv` bracket | modelled for literal brackets; else unknown | `dsl_parser.nim:3398-3404` (read) | none | — |
| `array[N, T]`, any ordinal index, `static[N]` dims, array alias | `itArray(elem, size, lo)` | modelled; nested arrays "#142"; width decline `termWalkMaxDepth` reads the index type not the path | `:1290-1300`, `:1334-1343`, `:1372-1375` (read) | S8z suites | INT-06 |
| `set[T]` small ordinal (bool/char/enum/8-16-bit/range), alias | `itBitSet` one BV | modelled (S8bq); size-dependent native behaviour pinned S8cd | `:1725-1733`, `:1395-1401` (read) | s8cd_setorder_{small,large} | CI-01 (time) |
| `set` as a **by-value formal** | — | declined:`feUnsupportedOp` (byValueWritten: not on `typeCopiedByValue`; a global reached by name, or a ptr in the same call) | `dsl_parser.nim:7835-7881` (read); `p_setparam` all 10 rows decline (ran) | none | PRC-04 (allowlist widening) |
| `tuple` named / anonymous / alias | `itTuple` | modelled; whole-tuple `==` declines | `:1316-1326`, `:1385-1394` (read) | s8cq_native `Tu` | PRC-34 |
| `object` (final, ≤3 words, no pragma) | `itTuple(objectName, nominalId)` | modelled-exact, on the by-value allowlist | `dsl_parser.nim:7853-7875` (read) | s8cq_native `O1`, `O3` | — |
| `object` > 3 words, `{.byref.}`, `{.byCopy.}`, inheritable, with any pragma | `itTuple` | by-value call: declined:`feUnsupportedOp` unless callee proved inert (byValueWritten) | `:7855-7861` (read) | s8cq_native `O4`, `Inh`, `BR` | PRC-04 |
| `object` with a **field default** (`x: int = 5`, Nim 2) | — | **crash: compile stop** `dsl_typebridge.nim(1218)` "node has no type" | `p_fdef` (ran) | none | **new, B-01** |
| `object` with a `when` member | `__unsupported` | declined:`feUnsupportedParamType` | `:629-634` (read) | — | PRC-20 |
| inheritance (`object of`), `of`, up/down conversion on **ref** | flattened fields + `inheritChain`, per-depth tags | modelled-exact (`p_objslice os_ref_*` ran; downcast of a base-typed ref gives `sxRaised` and natively `ObjectConversionDefect`) | `:1632-1668`, `dsl_parser.nim:10466-10490` (read) | p_objslice (ran) | — |
| `of` / conversion on **value** objects (slicing) | — | declined:`feUnsupportedExprKind` "`of` on a value outside a modelled ref hierarchy" (`p_objslice os_asg_*`, `os_conv_*`, `os_param_*` ran) | `dsl_parser.nim:10027-10040` (read) | none | PRC-04 |
| case object, nested / multi-discriminant | `itVariant` / `itMultiVariant` | modelled; `uncheckedAssign` SND-07; disc bytes `feUncheckedDiscBytes`; as a global heap cell PRC-15 | `types.nim:58-68` (read) | 17 `*variant*` suites | SND-07, PRC-15 |
| case object holding a seq/string/Table arm, under a `let` | — | **silently-approx (suspected)**: `holdsSharedMemory` has no `itVariant`/`itMultiVariant` arm, so `letCursorDecline` never fires | `dsl_parser.nim:16561-16571` (read) | `p_varcur` (ran, see §5) | **B-04** |
| `ref T` object (named, inline, generic instance) | `itRef(pointee)` heap identity (ADR-0022) | modelled-exact; `rs_*` copy-sharing rows agree (ran) | `:1510-1535`, `:1669-1672` (read) | p_refshare (ran) | — |
| `type RI = ref int` (ref alias of a **scalar**) | **`itInt`** (the alias is unwrapped to its pointee) | declined-accidental: `new(a)` "magic with a var parameter … not modelled", `a[] = k` "unsupported nnkAsgn shape", `p == nil` `heUnresolvedRef` (ran) | `:1526-1535` `else: return objCls` (read) | none | **B-02** |
| `type RS = ref seq[int]` | catch-all `__unsupported:RS` (alias trail refuses `nnkRefTy`) | declined:`feUnsupportedParamType` | `:1836-1848` (read) | — | — |
| `ptr T`, `pointer` | `itPtr` / `__unsupported:pointer` | modelled for addr cells; `hePtrArith`, `heUnsafeCast`, `hePtrFamily` (witness) | `:1673-1674`, `dsl_parser.nim:13433-13441` (read) | s8bs, s8bu, s8ch pending | PRC-14, PRC-17, PRC-28, PRC-30 |
| `cast[T](x)` value reinterpretation | — | declined:`feUnsupportedExprKind` (`p_intconv ic_cast_255` ran); `cast[ref Obj]` identity only | `dsl_parser.nim:10424-10432` (read) | none | PRC-04 |
| proc types, closures | `__closure` placeholder; `svClosure` at call sites | modelled for lambdas the walker built; `ceUnsupportedHof`, `ceCaptureByRefUnmodelled`, `ceClosureBodyUncertain` | `:1304-1306`, `:1675-1676` (read) | 13 `*closure*` suites; `p_varalias va_clo_*` exact (ran) | PRC-13 |
| closure iterators | `iekLambda` + iterator marker | declined:`ceNotImplemented` | `dsl_parser.nim:10403-10412` (read) | — | — |
| inline iterators (user, `items`/`pairs`/`mitems`) | inlined (ADR-0014) | modelled; `splitLines` over `readFile` compile stop | `:19043`, `:19603` (read) | 13 `*iter*` suites | INT-09, PRC-05 (non-scalar `pairs`) |
| `Option[T]`, `OrderedTable`, `CountTable`, `Deque`, any stdlib generic object | catch-all (`userGenericObjectImpl` refuses `isStdlibDecl`) | declined:`feUnsupportedParamType` / scoped | `:990-992`, `:1836-1848` (read) | none | PRC-04 (inventory) |
| `Table[K, V]` | `itTable` | modelled for int/string/… keys and values; `V = ref T` declined:`seUnsupportedTableValType` (`p_refshare rs_tabref_shared` ran); iteration order `feTableIterOrder`; `clear`/`pop` PRC-05 | `:1742-1747` (read) | s8cn, s8bl | PRC-05, PRC-06 |
| `HashSet[T]` | `itSet` | modelled for int elements; string/float/tuple elements decline | `:1748-1752` (read) | — | AUD-08, PRC-12 |
| `Atomic[T]`, `owned T` | `__ownership:*` | declined:`heUnsupportedOwnership` | `:1753-1754`, `:1278-1280` (read) | — | — |
| `typedesc` / `static` params | n/a as SUT formals; `low/high(T)` handled; `static[N]` array dims monomorphised | modelled where it appears | `dsl_parser.nim:10044`, `:1290-1300` (read) | — | — |
| user generics (`G[T]`, generic routines) | `classifyGenericInstance`, monomorphised bodies | modelled; `geInstantiationCapped`, `geUnresolvedGeneric` | `:1033-1100` (read) | S8bn suites | AUD-07 |
| threadvar | module global (`isThreadvarSym`) | modelled-exact as a global (`p_varalias va_tv_*` ran; replay marks it a child-own global `symex.nim:2758`) | `symex.nim:2644-2656` (read) | p_varalias (ran) | — |

### 1.2 Memory operations (rows) × families (noted inline)

| Operation | Status | Evidence | Native pin | 0016 row |
|---|---|---|---|---|
| copy on assign — scalars, tuples, objects, arrays | modelled-exact | `rs_tupint_private`, `rs_nested_int` (ran) | p_refshare | — |
| copy on assign — `seq`/`string` payload (deep), `ref` fields (shared), `seq[ref]`, `array[ref]`, tuple-with-ref | modelled-exact on c/orc (`rs_objseq_private`, `rs_objref_shared`, `rs_seqref_shared`, `rs_arrref_shared`, `rs_tupref_shared` ran) | p_refshare | refc / arc-release / cpp rows in §5 | — |
| user `=copy` with non-copy semantics (resets a field) | declined:`feGlobalRouteUnproved` "the lifetime hook `=copy` does not make the plain copy an assignment is modelled by" — **every read in the routine declines**, locals included | `dsl_parser.nim:22483-22547 routeHookCopies` (read); `p_copyhook ch_copy_*` (ran) | none | PRC-04, INT-10 |
| user `=sink` / `=dup` | same route as `=copy` (ran `ch_sink_*`) ; `=dup` of object/tuple through its hook PRC-35 | `:22490-22497` (read) | none | PRC-35 |
| user `=destroy` writing a global at scope end / overwrite / after a `sink` call | declined:`feGlobalRouteUnproved` "may write it, at a call the compiler inserts" (ran `ch_dscope_*`, `ch_dover_*`, `ch_dsink_*`) | S8cs | none | SND-08 (local ref), SND-09 |
| `=destroy` on a **local ref** (no global route) | false pair on both shas | — | — | SND-08 (owned there) |
| `=trace` | walker fault (`coerceIntLit` on `svPtr`) | — | — | INT-11 |
| explicit `=destroy(x)` / `=trace` call, `shallowCopy` | declined by `varParamMagics` (`vmDeclined`) | `dsl_parser.nim:4280-4287` (read) | s8bl_magicscan | — |
| `move(x)`, `wasMoved(x)`, `=wasMoved` | modelled: value, then the type's **zero** (`parseMoveExpr`, `parseZeroWrite`) — correct for `wasMoved` (bitwise zero) | `:4264-4268`, `:17787-17790`, `:17853` (read) | none for `move` of an aggregate | — |
| `ensureMove` of an int | fixed S8cb | — | — | SND-05 |
| `reset(x)` | modelled as zero (`parseZeroWrite`); Nim 2 `reset` = `default(T)` which **honours field defaults** — unreachable today only because B-01 stops the compile first | `:17785-17787`, `:11720-11723` (`default`/`zeroDefault` both → `zeroValueForType`) (read) | none | **B-01 (same fix)** |
| `sink T` formal | stripped to `T`; by-value allowlist path (Nim copies a non-last-use actual, moves a last-use one; neither is observable after the call) | `:1271-1274` (read) | — | — |
| `lent T` formal / result | formal stripped; a `lent` **result** makes `byValueWritten` decline ("a `lent` result") | `:1271-1274`, `dsl_parser.nim:8047` (read) | s8cn_lent*, s8cn_lentnative | PRC-05 |
| `var` formal write-back; two `var` formals on one cell (`two(gx, gx)`) | modelled; aliasing pair declines "`var` argument … is also reached through" (ran `va_two_*`) | p_varalias (ran) | — | — |
| `var` formal + by-value actual of the same cell (`mix(gx, gx)`, local too) | modelled-exact (ran `va_mix_*`, `va_mixloc_*`: scalar on the allowlist) | p_varalias | — | — |
| `var` seq element + the seq by value (`f(s[0], s)`) | modelled-exact for **seq** (`va_selem_9` sxSat, native hit; ran) | S8cn item 5 `seqViewElems` | — | — |
| `var` **string** element + the string by value (`vs(s[0], s)`) | declined:`feUnsupportedOp` "var argument write-back not modelled" + by-value decline (ran `sv_str_*`, `sv_gstr_*`) — the seq form decides, the string form does not | `dsl_parser.nim:8094-8098` (`seqViewElems` is seq-only; read) | none | **B-03** |
| `var` int element + `openArray` of the same seq (`voa(q[0], q)`) | modelled-exact (ran `sv_oa_*`, `sv_goa_*`) | — | — | — |
| `var` return aliasing | S8cq varret pins | — | s8cq_varret{,2,3} | SND-01 |
| `addr x` / `unsafeAddr x` on a local; `addr` aliasing another argument | modelled (S8bs/S8bu cells); aliasing pair declines "addr argument aliases another argument" (ran `sp_ptr_*`, `sp_loc_*`); `addr` of a `set` local "`addr loc` of a variable of type set[u8] is not …" declines | `dsl_parser.nim:7706`, `:8404`, `:9212` (read) | s8bs, s8bu | PRC-14, PRC-28, PRC-30 |
| `addr s[0]` then write through it (no growth) | modelled-exact (`sv_addr_9` ran) | — | — | — |
| `addr s[0]` then the seq **grows** | not probed (undefined natively: realloc may move) — a decline is the only sound answer; `viewFollows` "any other write declines" | S8ca | — | PRC-04 (`viewFollows`) |
| cursor inference — `let c = <shared-memory lvalue>` then a write to its root | declined:`feUnsupportedOp` "shares the memory or copies it, by the memory manager and what cursor inference proved" (ran `sv_let_*`) | `dsl_parser.nim:16678-16706` (read) | ll_*/lg_* (S8cn) | SND-12, PRC-05 |
| cursor inference — `let` over a **variant** holding a seq arm | not declined (no `itVariant` arm in `holdsSharedMemory`) | `:16561-16571` (read) | `p_varcur` (ran, §5) | **B-04** |
| explicit `{.cursor.}` on a `var` or `let` local | `letCursorDecline` returns nil for a `nnkVarSection`, and never reads the pragma; the var-section pragma loop keeps only `noinit` and drops every other pragma silently | `:16679-16681`, `:19771-19792` (read) | `p_pragmas` (ran, §5) | **B-05** |
| `{.global.}` local in a routine | the var-section loop `continue`s on `isModuleGlobal(d[0])`; entry value then follows AUD-09 (fresh) | `:19776` (read) | `p_pragmas` (ran, §5) | **B-06**, AUD-09 |
| `{.noinit.}` local | plain types read a fresh global-like value (sound); managed types decline | `:19777-19792` (read) | `p_pragmas` (ran, §5) | — |
| `swap(a, b)` | modelled (read both, write both) on pure lvalues; a call in either lvalue declines | `:17793-17804` (read); `va_swap_k` (ran) | none | PRC-28 |
| `zeroMem` / `copyMem` / `moveMem` on `addr x` | walker fault (FieldDefect) | — | — | PRC-16 |
| `GC_ref`, `create`, `alloc0` behind a cast, `new(p, finalizer)` | declines / compile stop history | — | — | PRC-17..20, CRH-02 |
| globals vs locals: entry value of a literal-initialised global | fresh (deliberate); a false `sxSat` from it is refuted only by replay | — | — | AUD-09 |
| closure capture of a local `var` (`inc c` in a lambda) | modelled-exact (ran `va_clo_*`) | — | p_varalias | — |
| seq/string growth while a by-value formal holds the old payload (`wrStr(gs)` adds to `gs`) | declined (by-value: callee reaches `gs` by name) (ran `sv_grow_*`, also the loop budget) | — | — | PRC-04 |
| Table value views: `mgetOrPut`, `t[k]` var, `withValue`, `hasKeyOrPut` | `mgetOrPut` modelled (22 sites); `withValue`/`hasKeyOrPut` have no arm (0 hits) → body-walked or declined; `t.clear`, `t.pop` decline | `dsl_parser.nim` grep counts (read) | — | PRC-05 |
| evaluation order of arguments and lvalues | `nimArgTemps` (S8cq), `feEvalOrderUnmodelled` for moved index checks | `:2170-2230`, `:2305-2318` (read) | s8cq_argorder, s8cq_twice* | PRC-28 |
| integer edge cells: shift by ≥ width, `low(int) div -1`, `low(int) mod -1`, `abs(low)`, `-low`, unsigned div by zero, `chr(255+k)`, `succ` past high, `int8 * int8` overflow, `uint8 - 1` wrap, truncating `div`/`mod` | see §5 `p_arith` (ran) | — | — | **B-07, B-08** |
| build sensitivity: `--mm:refc`, `--mm:arc -d:release`, cpp | §5 rows for p_refshare, p_strview, p_varcur, p_varalias (ran) | — | — | §2.2 |
| `-d:danger`, `--fieldChecks:off`, `--overflowChecks:off` | every routine declines (`feCheckOption`) | S8cu | — | PRC-07, PRC-08 |

---

## 2. Findings

| id | cell | class | minimal SUT | evidence | build sensitivity | suggested pin | effort |
|---|---|---|---|---|---|---|---|
| B-01 | object with a Nim 2 field default × every zero-init site (`var o: O`, `O()`, `default`, `reset`, `new`, `newSeq`, `setLen`, `result`, `array[N, O]`) | **crash (compile stop)**, and a latent **soundness** hole behind it | `type O = object; x: int = 5; y: int` then `var o: O; if o.x == 5: symexTarget("hit")` | ran: `p_fdef` stops the compile at `dsl_typebridge.nim(1218, 62) Error: node has no type`; read: no site in the bridge reads `nnkIdentDefs[^1]` (the default), and every zero-init path goes through `zeroValueForType` (`dsl_parser.nim:11720-11723`, `:17785-17790`), which would give `o.x == 0` once the stop is lifted — a false `sxUnsat` on `== 5` and a false `sxSat` on `== 0` | none (front-end) | `tsymex_rfc0016_fielddefault`: the native loop hits `== 5` at every site; the walker must decline the type (first) or honour the default (exact). `wasMoved` stays zero natively (bitwise) — pin that separately so the exact model does not over-apply defaults | S for the named decline (classify a record with a non-empty default as `__unsupported`); M for the exact model (carry defaults on `IRType`, use them in `allocateSym` and `zeroValueForType` except for `wasMoved`/`move`) |
| B-02 | `type RI = ref int` (ref alias of a non-record pointee) × `new`, `[]=`, `== nil`, param | precision (declined-accidental) | `type RI = ref int; proc f(p: RI; k: int) = p[] = k; if p[] == k: symexTarget("hit")` | ran: `p_refalias` all five rows `sxUnknown` with `new#varMagic` unmodelled, "unsupported nnkAsgn shape: a[] = k", `heUnresolvedRef: ref/ptr bEq against a fixed-width integer`; read: `dsl_typebridge.nim:1526-1535` returns `objCls` (the pointee's own classification) when the pointee is not a record — the alias **is** an `int` to the walker | none | none needed for soundness today; a pin that `RI` declines by name (`feUnsupportedParamType`) or is modelled as `itRef(itInt)` | S |
| B-03 | `string` × element view beside the whole (`vs(s[0], s)`) | precision | `proc vs(c: var char; s: string): char = c = 'z'; s[0]` called as `vs(s[0], s)` | ran: `p_strview sv_str_z`/`sv_gstr_z` `sxUnknown` ("var argument write-back not modelled" + by-value decline); the seq form `va_selem_9` is `sxSat` and natively hit; read: `seqViewElems` (`dsl_parser.nim:8094`) is seq-only | none | `tsymex_rfc0016_strview`: native hit on `'z'` | S–M |
| B-04 | case object holding a `seq`/`string`/`Table` arm × `let` cursor (`let c = gV; gV.s[0] = 9; c.s[0]`) | **silently-approx, build-divergence confirmed natively**: the walker **decides** this shape with no decline (`vc_var_copy sxSat`, `vc_var_shared sxUnsat`, `vc_vcal_*` the same, on orc and arc-release, c) where the same shape on a plain object with the same seq field declines (`vc_obj_* feUnsupportedOp "a let holding memory that may be written"`). Natively the `let` is a **copy on orc and arc-release** (walker agrees there) and a **shared view on refc** (`p_varcur_refcnat`: `vc_var_shared native=true`, `vc_var_copy native=false`, and `vc_vcal_shared native=true`). No build on which the walker runs shows the mismatch (B-14: refc has no walker), so this is not a release blocker, but it is exactly the decline the plain-object twin has and the variant twin lacks | `type V = object; case k: bool; of true: s: seq[int]; of false: n: int` ; `let c = gV; gV.s[0] = 9; if c.s[0] == 9: …` | ran: `p_varcur` on c/orc (§5); read: `holdsSharedMemory` `dsl_parser.nim:16561-16571` has arms for `itSeq, itString, itTable, itSet, itTuple, itArray` and `else: false` — `itVariant`/`itMultiVariant` fall to `false`, so `letCursorDecline` returns nil | `--mm` (cursor inference is orc/arc; arc-release and refc rows in §5) | `tsymex_rfc0016_variantcursor` on orc, arc, refc: RED is "decides without a decline on a build where the let is a cursor" | S (add the two arms, recursing into `vPlainFieldTypes` and every arm's `fieldTypes`) |
| B-05 | any family × explicit `{.cursor.}` on a `var` **or** `let` local, root written afterwards | **soundness-confirmed** (false `sxUnsat` **and** false `sxSat`, clean, no decline) | `gs = @[k]; var c {.cursor.} = gs; gs[0] = 9; if c[0] == 9: symexTarget("shared")` (and the `let c {.cursor.}` twin) | ran: `p_pragmas` on c/orc: `pg_cvar_shared walker=sxUnsat native=true MISMATCH-falseUnsat`, `pg_cvar_copy walker=sxSat native=false MISMATCH-falseSat`, `pg_clet_shared`/`pg_clet_copy` the same pair, all with an empty error list (trusted verdicts); read: `letCursorDecline` `:16679` returns nil unless `c.kind == nnkLetSection` (the `let` twin fails for a different reason: the pragma is stripped at `:19771-19792` before `letCursorDecline` sees a plain `let`, and `mayWriteRoot` is only consulted when the type `holdsSharedMemory` — it does here, so the `let` twin's miss needs a second look: the `nnkPragmaExpr` ident is not an `nnkSym`, `:16680` `c[0][0].kind != nnkSym` → nil) | the same four mismatches on c/orc, c/arc-release and cpp/orc (ran, `results_part1.txt`, `results_part2.txt`). Native refc (no walker): the `let` twin shares (`pg_clet_shared native=true`), the `var` twin **copies** (`pg_cvar_shared native=false`), so the exact model is per manager | `tsymex_rfc0016_cursorpragma`: both twins, both labels, three managers | S (decline any local pragma not on an inert list; later, model a cursor as the view it is) |
| B-06 | `{.global.}` local × repeated calls in one SUT (`counter()` twice); literal-initialised `{.global.}` read | precision (sound: the declaration is lifted to a module global whose entry value is havoc, `feGlobalHavoc`, and the replay refutes the false witness) | `proc counter(): int = var cnt {.global.} = 0; inc cnt; cnt` | ran: `pg_global_ge2 sxSat native=true`, `pg_global_1 sxUnknown` (havoc + `feReplayRefuted`), `pg_ginit_5 sxSat`, `pg_ginit_0 sxUnknown` (refuted); read: `:19776` | none | none needed; the initialiser-not-read precision is AUD-09 | — (AUD-09) |
| B-07 | unsigned integer × `div`/`mod` by zero | **soundness-confirmed**: the walker decides `sxRaised` (`divMagics` lists `DivU`, `ModU`, `DivU64`, `ModU64` beside the signed ones, `dsl_parser.nim:4023-4025`), natively the process dies with **SIGFPE** (no Nim check on unsigned division; uncatchable). A SUT with `except DivByZeroDefect:` around it would get a false `sxSat` on the handler's label, exactly S8cu's nil-deref shape | `let r = 10'u64 div uint64(k); if k == 0: symexTarget("after")` | ran: native loop `Traceback … arUDiv0 … SIGFPE: Arithmetic error` (first `p_arith` run, k = 0); walker `ar_udiv_after0 walker=sxRaised native=false` (second run with k = 0 skipped natively) | none (C `/` on unsigned has no check on any manager or backend; `--panics` irrelevant) | `tsymex_rfc0016_udiv0_native` in the `s8cu_nil_native` shape (spawn the SUT, expect a signal, not a `DivByZeroDefect`); walker side: route `DivU*`/`ModU*` zero divisors through `crashRaise` | S |
| B-08 | `int` × `shl`/`shr` by a count ≥ the width | refuted on this host (agrees): the walker models the x86 count mask (`1 shl 64 == 1`, `ar_shl_wrap1 sxSat native=true`, `ar_shl_zero sxUnsat native=false`); C leaves it undefined, so the agreement is host-specific | `let r = 1 shl (60 + k); if r == 1: …` at `k = 4` | ran: `p_arith ar_shl_*`, `ar_shr_*` all agree on x86-64/gcc | `--cpu`, C compiler (UB) — a non-masking target would make the current model a false `sxSat`; keep as a §2.2 per-build pin, not a fix | pin on each CI host; decline when the count is not proved `< width` if a non-x86 leg is ever added | S |
| B-09 | `Table[K, ref T]`, `Table[K, seq[T]]` values; `toTable` with a 2-var `for` | precision | `var a = {1: RO(v: k)}.toTable; var b = a; b[1].v = 9; a[1].v == 9` | ran: `rs_tabref_shared` `sxUnknown` (`seUnsupportedTableValType`, and the `for` over `items` with 2 loop vars) | none | — | M |
| B-10 | `set[T]` by value with the callee writing the same set by name or through `addr` | precision (sound by `byValueWritten`); `byValueShareOfType` returns `""` for `ntySet`, so the S8bs location model never tracks a set actual as `"ptr"` even though a >8-byte set is a C array passed by pointer | `calBig(gBig)` with `gBig.incl 'x'` inside | ran: `p_setparam` 10/10 decline; read: `dsl_parser.nim:7621-7636` | set size (≤8 bytes is a scalar) | pin natively that `sp_big_shared` hits and `sp_small_shared` does not (ran: both as expected) before lifting | S |
| B-11 | `Option[T]`, `OrderedTable`, `CountTable`, `Deque`, every stdlib generic object | precision, declined by the **catch-all**, not by an allowlist entry: `userGenericObjectImpl` refuses `isStdlibDecl` and the alias trail stops at `nnkBracketExpr` of an unknown head | `proc f(o: Option[int])` | read: `dsl_typebridge.nim:990-992`, `:1836-1848` | none | — | (inventory under PRC-04) |
| B-12 | value-object inheritance × slicing assignment (`var v: A = B(...)`), `A(b)`, by-value base formal | precision (declined on `of`); the slice copy itself (`v.a == k`) was not decided because the `of` on the same path declined | `p_objslice os_asg_a` | ran: declines with "`of` on a value outside a modelled ref hierarchy" | none | native: `v of B` is **true** on a sliced value (`os_asg_ofB` native=true, `os_conv_ofB` native=true, `os_param_ofB` native=true — the copied `m_type` is the subtype's); any future value-`of` model must pin this, not static typing | S |
| B-13 | `let c = gs` string/seq cursor | precision only (declined; SND-12 is the soundness row) | `sv_let_*` | ran: declines on orc, arc-release and cpp; natively `c[0] == 'a'` (a copy) on orc and arc-release | per `--mm` | the §5 refc native row | — |
| B-15 | `{.noinit.}` scalar local × read before write | precision / ci (nondeterministic witness trusted): on cpp the walker gave `pg_noinit_0 walker=sxSat native=false` with `feGlobalHavoc` and **no** `feReplayRefuted` — the replay child saw garbage `x == 0` and confirmed the witness, while the in-process loop saw non-zero garbage; on c/orc the same label was refuted, on c/arc-release confirmed with native=true. A label reachable only through uninitialised memory is reported as a trusted `sxSat` whenever the child's stack happens to agree | `var x {.noinit.}: int; if x == 0: symexTarget("z")` | ran: `p_pragmas` c/orc, c/arc-release, cpp/orc (three different answers) | per backend and build (stack contents) | a `noinit` read should decline, or its hit should carry a `feGlobalHavoc`-class *unconfirmable* mark that no replay can lift | S |
| B-16 | `string`/`seq` by-value formal × caller-visible growth (`wrStr(gs)` appends to `gs` and reads `s.len`) | build-divergence recorded (walker declines on every build it runs on, sound): natively `s.len == k` on orc/arc-release and `s.len == k + 1` on **refc** (`sv_grow_k1 native=true` only in `p_strview_refcnat`), and `let c = gs; gs[0] = 'z'` shares on refc (`sv_let_shared native=true`) and copies on orc/arc. Evidence for keeping the by-value and let-cursor declines per manager rather than lifting them from one build's pin | `p_strview` `sv_grow_*`, `sv_let_*` | ran | `--mm` | the refc native rows as the RED half of any PRC-04/PRC-05 lift | — |
| B-14 | every family × `--mm:refc` | **ci / test-harness**: the walker cannot be built under refc at all — nim-z3 `src/z3/ast.nim(63, 1) Error: signature for '=destroy' must be proc[T: object](x: var T)` — so no `symexFind` verdict exists on refc, and §2.2's "pinned on each memory manager" can only be native-only on refc (as `s8cq_native` already is, "No walker"). The `ll_*`/`lg_*` S8cn rows must therefore have been orc/arc-only on the walker side | any `symexFind` under `--mm:refc` | ran: `p_varcur_refc`, `p_strview_refc`, `p_refshare_refc` all rc=1 with that error | refc only | record in the RFC's §2.2 that refc pins are native-only; or fix the hook signature in nim-z3 (then a refc walker leg) | S (doc) / M (nim-z3) |

---

## 3. How to make this axis closed (the §2.1 structure)

The RFC's rule is "admitted by an allowlist, not denied by a denylist". On this
axis the code already has three fail-closed tables, and the findings above all
come from the places that are *not* a table but an implicit `else`:

**What is fail-closed today (read).**
- `typeCopiedByValue` (`dsl_parser.nim:7835-7881`): an explicit `case ty.typeKind`
  with `else: false`; anything off the list goes to `byValueWritten`. This is the
  model for the rest.
- `varParamMagics` (`:4249-4287`) with its guard test `tsymex_rfc0005_s8bl_magicscan`
  that scans the stdlib and fails on an unlisted magic.
- `classifyType`'s catch-all (`dsl_typebridge.nim:1832-1848`): `__unsupported:` →
  `feUnsupportedParamType`.
- `routeHookCopies`/`readHooks` (`:22483-22575`): a hook that is not a plain copy
  opens the route and every read declines.

**Where the implicit `else` is (the holes this lens found).**
1. `dsl_typebridge.nim:1526-1535` — the ref-alias arm's `else: return objCls`
   (B-02). Make it `return unranged(tUninterp("__unsupported:" & s))` unless the
   pointee kind is in `{itTuple, itVariant, itMultiVariant}`; or model `itRef(T)`
   for scalar `T` and pin it.
2. `dsl_typebridge.nim` record classification — a field with a non-empty
   `nnkIdentDefs[^1]` (B-01) is read nowhere. The bridge must either carry the
   default on the `IRType` field or return `__unsupported:` for the record. Today
   it does neither and the compiler stops in `viewTypeInst`.
3. `dsl_parser.nim:16561-16571 holdsSharedMemory` — `else: false` (B-04). Invert
   it: `holdsSharedMemory` is true for every kind except an explicit
   value-only list `{itInt, itBool, itFloat32, itFloat64, itDistinct-of-those}`
   and `itRef`/`itPtr` (a handle is copied; its cell is the heap's), recursing
   through `itTuple.fields`, `itArray.elemTy`, `itVariant.vPlainFieldTypes` and
   each arm's `fieldTypes`, and `itMultiVariant` axes.
4. `dsl_parser.nim:19771-19792` — the local-declaration pragma loop keeps
   `noinit`, skips `isModuleGlobal` (`{.global.}`), and drops every other pragma
   (`cursor`, `volatile`, `register`, `exportc`, `importc`, `threadvar`,
   `codegenDecl`, `noalias`, `align`, …) with no decline (B-05, B-06). Replace
   with an allowlist of inert pragmas (`inject`, `used`, `noinit` handled) and
   `ctx.declineMarker(feUnsupportedStmtKind, …)` for anything else.
5. `letCursorDecline` (`:16679`) is `let`-only. A `var c {.cursor.}` is the
   same shape; the gate in (4) covers it if `cursor` is not on the inert list.
6. Unsigned `div`/`mod` by zero and over-width shifts (B-07, B-08): the integer
   op lowering has no "undefined in C" table. Add one keyed by (op × signedness
   × operand-proof) with the three answers Nim has: checked (`DivByZeroDefect`,
   `OverflowDefect`), crash (`crashRaise`, as S8cu's nil deref), undefined
   (decline unless the path proves the count `< width`).

**The table that would close the axis.** One compile-time table in
`dsl_typebridge.nim` (next to `varParamMagics` in spirit), keyed by
`(NimTypeKind, MemOp)` where `MemOp` is the row set of §1.2 (`copyAssign`,
`byValueArg`, `letCursor`, `varFormal`, `lentFormal`, `lentResult`, `addrOf`,
`hookCopy`, `hookSink`, `hookDestroy`, `move`, `wasMoved`, `reset`, `swap`,
`zeroInit`, `localPragma`, `globalEntry`), each cell one of
`{exact(pin: string), declined(kind: SymexErrorKind, why: string)}`. Three
consumers read it: `typeCopiedByValue` (replace its own `case`),
`holdsSharedMemory` (replace), and a new `localDeclGate` for (4)/(5). A guard
test in the shape of `s8bl_magicscan` enumerates `NimTypeKind` and fails when a
kind has no row for every `MemOp`; a second guard enumerates the pragma names
Nim's `pragmas.nim` lists for `var`/`let` and fails on one neither inert nor
declined. Then an unlisted (type × op) cannot produce a verdict: it is either
`__unsupported:` at classification or a `declineMarker` at the declaration.

**Build-setting axis.** `tsymex_rfc0005_s8cq_native` already runs its allowlist on
nine settings. The same harness (no walker, native only) should take the §1.2
rows that are *decided* today — `rs_*`, `va_*`, `sv_oa_*`, `sv_addr_9` — and run
them on refc/orc/arc × release/danger × c/cpp, since a decided row pinned on orc/c
alone "says nothing about another" (§2.2). §5 has the first four of those rows.

---

## 4. Probe inventory (all ran on eos `~/nelli/wt-rsB`, sha 83c1d304)

| probe | cells | result |
|---|---|---|
| `p_fdef` | field defaults × 11 zero-init sites | compile stop (B-01) |
| `p_refalias` | `ref int`/`ref string` alias × share, param, `nil` | 5/5 decline (B-02) |
| `p_copyhook` | `=copy`, `=sink`, `=destroy` scope/overwrite/sink-param | 12/12 decline (sound) |
| `p_objslice` | value slicing, `of` on values/refs, downcast | 7 decline, 4 agree |
| `p_intconv` | 17 conversion labels | 9 agree, 4 `sxRaised` with no native hit, 4 decline (`cast`, local `type`) |
| `p_refshare` | 14 copy/share labels | 11 agree, 3 decline (`Table[K, ref]`, `seq[seq]`) |
| `p_setparam` | 10 set-by-value labels | 10/10 decline (sound) |
| `p_varalias` | 13 aliasing/threadvar/closure/swap labels | 11 agree, 2 decline |
| `p_strview` | 13 string/openArray view labels | 5 agree, 8 decline (B-03, B-13) |
| `p_arith` | 25 integer edge labels | 18 agree, 7 `sxRaised` with no native hit — one of them (`ar_udiv_after0`) is natively a SIGFPE, not a raise (B-07) |
| `p_pragmas` | `{.global.}`, `{.cursor.}` var/let, `{.noinit.}` | **4 MISMATCH** (B-05: `pg_cvar_shared`, `pg_cvar_copy`, `pg_clet_shared`, `pg_clet_copy`), 6 agree or decline-with-replay |
| `p_varcur` | variant/let-cursor (B-04) + controls | 4 decided (variant twin, no decline), 6 decline; agree on orc and arc-release |
| `*_arcrel` (c), cpp | p_refshare, p_strview, p_varcur, p_varalias, p_pragmas | every row the same status as c/orc; B-05's four mismatches repeat on both; `pg_noinit_0` differs by build (B-15) |
| `*_refc` | p_varcur, p_strview, p_refshare | walker does not build under refc (B-14) |
| `*_refcnat` | native-only refc rows of p_varcur, p_strview, p_refshare, p_pragmas | refc shares where orc/arc copy: `vc_var_shared`, `vc_obj_shared`, `vc_vcal_shared`, `sv_let_shared`, `sv_grow_k1`, `pg_clet_shared` all native=true (B-04, B-16); `pg_cvar_shared` native=false |

Totals: 14 probe files, 36 build-runs (c/orc 12, c/arc-release 4, cpp/orc 4, refc walker 3 unbuildable, refc native-only 4, plus reruns), 163 labels; 4 confirmed walker-vs-native mismatches (one cell, B-05), 1 confirmed crash-vs-raise (B-07), 1 compile stop (B-01), 0 mismatches on any other decided cell.

## 5. Probe output

Verbatim `PROBE` lines (error text truncated) are in
`research-out/probes/B/results_early.txt` (p_fdef, p_refalias, p_copyhook,
p_objslice, p_intconv, first p_arith run) and
`research-out/probes/B/results_part1.txt` (p_refshare, p_setparam, p_varalias,
p_strview on c/orc; p_arith, p_pragmas, p_varcur; the `_refc`, `_arcrel` and cpp
rows). `results_part2.txt` holds the cursor-pragma rows on arc-release and cpp and
the refc native-only rows. Probe sources: `research-out/probes/B/p_*.nim` (+ `.cfg`).

The four confirmed-mismatch lines (c, orc, Z3 5.1; empty error list means a
clean, trusted verdict):

```
PROBE pg_cvar_shared walker=sxUnsat native=true MISMATCH-falseUnsat []
PROBE pg_cvar_copy walker=sxSat native=false MISMATCH-falseSat []
PROBE pg_clet_shared walker=sxUnsat native=true MISMATCH-falseUnsat []
PROBE pg_clet_copy walker=sxSat native=false MISMATCH-falseSat []
```

The compile stop (B-01): `/work/src/nelli/smt/dsl_typebridge.nim(1218, 62) Error: node has no type`.

The crash-vs-raise pair (B-07): native `SIGFPE: Arithmetic error` at `arUDiv0`
(`10'u64 div 0'u64`); walker `PROBE ar_udiv_after0 walker=sxRaised native=false`.
