# RFC-0016 merged work list (draft for Corey, not yet in the RFC)

Snapshot `83c1d304` (walker 272). Merged from six read-and-probe lenses
(A constructs, B types x memory, C magics/stdlib, D machinery/builds,
E reconcile/harvest, F tests/finish line), all in
`research-out/{A..F}-*.md`, plus control-loop verification in
`research-out/00-verification-notes.md`.

Evidence tags: **V** = re-run by me on eos, confirmed; **P** = lens ran a
probe (walker and native on one build), not re-run by me; **r** = read only,
no SUT yet. Severity against `main` (6cbfe8f) was not measured for any row;
every Tier-0 mechanism predates RFC-0005, so "same as main" is expected and
each row needs its three-way line before work (the S8cu rule).

Work ids are `W-nn`; the lens id follows in brackets so the report row can be
found.

---

## 1. Tier 0: confirmed clean false verdicts (fix first)

A clean false verdict is the worst class: no taint, no decline, `trusted()`
is true. Seven, all on the default or a documented build.

| W | item | verdict wrong how | ev | cause | fix | effort |
|---|---|---|---|---|---|---|
| W-01 | `except T as e:` in a SUT [A-01] | handler label `sxUnsat` (native hits); raise target `sxRaised` (native catches) | V | `dsl_parser.nim:20460-20461` stores `"ValueError as e"` (the repr) as the typeId; never matches at `runtime.nim:25751` | unwrap the `as` infix; bind `e` as `getCurrentException()` is bound; one `typeIdOf(sym)` for every typeId (closes W-31 too) | s |
| W-02 | explicit `{.cursor.}` on a `var` or `let` local [B-05] | false `sxUnsat` and false `sxSat`, c/orc, c/arc-release, cpp | V | local-pragma loop `dsl_parser.nim:19771-19792` drops every pragma but `noinit`; `letCursorDecline` is let-only | decline any local pragma not on an inert list (K3); model the cursor later | s |
| W-03 | `--panics:on` [D-01] | label inside `except <Defect>` / `finally` after a defect is a clean `sxSat`; Defect target clean `sxRaised`; natively the process dies | V | walker never reads `nimPanics` (only `replayInScope`, `symex.nim:2343`) | under panics a Defect is a `crash: true` escape, like S8cu's nil deref; part of BuildProfile (K5) | s |
| W-04 | `float32` <-> `float64` conversions, incl. hidden convs [A-02] | false clean `sxSat` and `sxUnsat` | P | `nnkConv` and hidden-conv arms end in a transparent `else: parseExpr(operand)` (`:10658`, `:10845`) | `fp.to_fp` RNE between sorts, or decline every pair off an allowlist; grep gate K2 | s-m |
| W-05 | `low(int) mod -1` with a literal/const divisor [C-01] | false `sxUnsat` (native returns 0: gcc folds `x % -1`) | P | `runtime.nim:8862-8870` adds the trap condition regardless of divisor shape | no trap for a literal/const `-1`; pin on gcc, clang, MSVC (`--cc` axis) | s |
| W-06 | unsigned `div`/`mod` by zero [B-07] | walker `sxRaised` DivByZeroDefect; natively SIGFPE (uncatchable). With `except DivByZeroDefect` around it: false `sxSat` | P | `divMagics` lists `DivU/ModU/DivU64/ModU64` beside signed (`dsl_parser.nim:4023-4025`) | route through `crashRaise`; native pin by child exit signal | s |
| W-07 | unchecked signed overflow modelled as wrap [D-02; same as HRV-37 / S8cu note] | `v + 1 > v` clean `sxSat` at `high(int)`; gcc folds it away | P | `runtime.nim:24500-24502` consumes the overflow marker without a token when the settings "model the wrap" | wrap only for unsigned; signed wrap survivors replay-gated or declined unless `-fwrapv` (K5, K7) | m |

## 2. Tier 1: soundness risks found by reading (no SUT yet, or latent)

Each needs a probe first: a hit moves it to Tier 0, a miss closes it with
the probe kept as a pin.

| W | item | ev | note |
|---|---|---|---|
| W-08 | `nodeWritesHeap` is a fail-open denylist: asm, emit, cast, `inc(p[])`, `swap(p[],x)`, `setLen(p[],n)` read as "no write" [D-05] | r | feeds the S8cn let-cursor/lent decline; `scanOpaqueEffects` gets the same shapes right. K6 |
| W-09 | hook copy-proof `check` defaults to "copied" for unknown node kinds (`swap`/`move`/`copyMem` in `=copy`) [D-06] | r | K6 |
| W-10 | `ptrUsesStayLocal`, `routeStoresThroughDeref`, `bindsViewWhole` same denylist shape [D sec.2] | r | K6, moderate |
| W-11 | `svWithRaw` returns the old value for a composite kind, no record [D-07] | r | one caller today; doAssert/decline |
| W-12 | object field defaults: behind W-20's compile stop every zero-init site would give `0`, not the default [B-01] | r | fix with W-20: decline first, model second; `wasMoved` stays bitwise zero |
| W-13 | `{.noinit.}` read: replay confirms a witness reachable only through garbage memory [B-15] | P | three builds, three answers; a noinit read must be unconfirmable or decline |
| W-14 | `int` hard-coded BV64; `--cpu:i386` unread and unkeyed [D-09] | r | refuse 32-bit in BuildProfile until modelled |
| W-15 | `isThreadvarSym`/`isImportedVar` read a `getImpl` failure as "no" [D-10] | r | fail closed |
| W-16 | `defectExclusions` user set silently turns a Defect path into unreachable, `sxUnsat` stays trusted [D-12] | r | excluded defect records `dcOmitted` |
| W-17 | `-d:nimOldCaseObjects` / `strictCaseObjects` unread, unkeyed [D-11] | r | BuildProfile row |
| W-18 | `;impl=` digest holes: importc/dynlib bodies, override callees, proc-value targets, `lib/` tree [HRV-36] | r (documented in m0.9.1) | stale cache verdict on body change; fold into INT-31 |
| W-19 | default-route int-offset arithmetic without overflow fork (N24, #166) and `range[0'u64..>int64.high]` round-trip (#169) [HRV-33/34/35] | r | owner decision: RFC-0014 or here (D-4 below) |
| W-19b | S8cs "not covered" store routes (threads/signals, dynamic-subtype hooks, ORC cycle collector) [HRV-38]; Windows re-exec unseen macro hooks [HRV-39]; S8cu scan misses (`mitems` instantiated under a push elsewhere, never-popped push, importer outside graph, nelli under a user push) [HRV-71]; opaque proc with `var T` params leaves env unmutated [HRV-82] | r | each: three-way row, then fix or a "stays" record |
| W-19c | closure-unverified: S1b block/break binding [HRV-40], S7 `lowerInExpr` drains [HRV-41] | r | probe; likely closed |
| W-19d | SND-07 and SND-12 need a native re-pin; PND-11 is soundness, not pending | r (E) | |

## 3. Tier 2: crashes, compile stops, hangs

A compile stop counts as worse than a decline (RFC sec.2.4).

| W | item | ev | fix |
|---|---|---|---|
| W-20 | object with a Nim 2 field default: compile stop `dsl_typebridge.nim(1218)` [B-01] | P | classify as `__unsupported` now (s); exact model later (m) |
| W-21 | `case` with an `elif` arm: compile stop `:19300` (and `:12789` expr form) [A-03] | P | feed into `lowerCondChain` (xs) |
| W-22 | `parseBool(s)` with `s.len == 4` hangs, no budget bites [C-03] | P | find the bound that misses a string `case` over a built string (m) |
| W-23 | `--mm:refc`: nim-z3 `ast.nim(63)` `=destroy` signature, compile stop [B-14, D-04] | P | named refusal in BuildProfile (s), or fix nim-z3 + refc leg (m) |
| W-24 | `filterIt` -> `weInternalWalkerFault` (`runtime.nim:19688`) [C-02] | P | named decline, then model |
| W-25 | bitwise `not` on an int carried as Z3 Int -> walker fault [A-07] | P | `-x - 1`; name the decline meanwhile |
| W-26 | `assertCoveredBy` splat catches 4 Defects; Overflow/DivByZero/Range/ObjectConversion witness kills the host [D-08] | r | catch `Defect` |
| W-27 | macro `error()` sites reachable from typed SUTs (suspected): prefix op `:11243`, empty `@[]` of non-seq type `:11206`, others listed in A sec.3 [A-08, C-12] | r | probe, then `declineAtSite` (K2 grep gate) |
| W-28 | `<`/`<=` on `ptr` reaches `cmpBV` on `svPtr` (suspected) [C-10] | r | probe; named decline (allocator-dependent) |
| W-29 | harvested crash/hang items with no row: N35 OOM (`while check(x) and ...`) [HRV-43]; generic param `.len/.add` compile stop [HRV-44]; `cast[int32]` helper `lowerConvIntWidth` fault [HRV-45]; PCRE interpreter SIGSEGV near 8000 bytes [HRV-46]; `{'0'..'9'}` contains [HRV-47]; witness KeyError on multi-axis variant ref [HRV-48]; composite arm-field reassignment ValueError, `array[Enum,T]` stop [HRV-49]; 8 `$simplify` literal-test sites that hang on big terms [HRV-50]; cumulative Z3 MEMOUT at ~20 calls [HRV-51]; `unsupportedFieldPlaceholder` `mkIntLit(0)` fallback [HRV-06] | r (docs/code) | probe each; most closure-unverified |
| W-30 | existing rows still open: CRH-01 (now declines, retitle as precision per C-06), CRH-03 (=INT-02 OOM), PRC-16 (walker fault, reclassify), INT-11 (`=trace` fault) | E | |

## 4. Tier 3: precision, ranked by how often real code hits it

High-frequency first; these are what make symex `sxUnknown` on ordinary
Nim.

| W | item | ev | effort |
|---|---|---|---|
| W-31 | `x in 0 .. 10` / `notin` declines (commonest bounding idiom) [C-18] | P | s |
| W-32 | five everyday syntax declines: try-expr, block-expr, command call in expr (`succ x`), case range label `of 2..4`, `when nimvm` [A-06] | P | xs each |
| W-33 | `raise <value>` declines [A-05 = HRV-21] | P | s (via `typeIdOf`) |
| W-34 | `$` of seq/array/tuple/object/set/cstring [C-05; PRC-35] | P | m (needs PRC-07 for `addQuoted`) |
| W-35 | `==` on seq/array/tuple [C-08, PRC-34, HRV-53] | P | m |
| W-36 | `sort`/`sorted`/`align`/`formatFloat`/`parseHex`: formals with defaults unreadable [C-06] | P | m |
| W-37 | `min`/`max(openArray)`, `low/high` on seq/array values [C-07, HRV-19] | P | s |
| W-38 | `&` with a char operand; `intToStr`; `s.add('c')` outside loops [C-04 = HRV-20/58] | P | s |
| W-39 | `for i in a ..< s.len` with a non-symbol bound written in the body [A-04] | P | xs-s |
| W-40 | iterator shapes: yield under case/for/try, `return` in iterator, break/continue over a user iterator, closure iterators, tuple-yield of a var [A-11 = HRV-14/15/23/80] | r | m |
| W-41 | `split` variants, `contains(set[char])`, `fmt`, `%`, `cmp(string)`, `count`, `binarySearch`, `mapIt`/`toSeq`, `parseFloat` [C-09, C-14] | P | m each |
| W-42 | `string` element view beside the whole `vs(s[0], s)` [B-03] | P | s-m |
| W-43 | `ref int` alias classified as `itInt` [B-02] | P | s |
| W-44 | `Table[K, ref T]`/`seq[T]` values; Table non-string keys at zero-init [B-09, HRV-04] | P | m |
| W-45 | value-object slicing / `of` on values (native: `of` is true on a sliced value) [B-12] | P | s |
| W-46 | set by value, >8-byte set passed by pointer untracked [B-10] | P | s |
| W-47 | stdlib generic objects (Option, OrderedTable, CountTable, Deque) decline by catch-all, not allowlist [B-11, HRV-62] | r | inventory |
| W-48 | harvested precision with no row: HRV-01, 02, 07-12, 16-17, 22, 24-25, 28-30, 52, 54-57, 59-60, 63-70, 72-79, 81, 83-88 (see E sec.2.1, 3.3) | r | per item; many are closure-unverified and close on a probe |
| W-49 | existing open PRC rows after E's collapse: PRC-03..15, 17..21, 23, 25, 26, 28, 29, 31..33, 35; INT-05/06/09/10/18/19/21; AUD-05..09 | E | as written, evidence refreshed per E |

## 5. Build sensitivity (one mechanism, K5)

| W | item | ev |
|---|---|---|
| W-50 | BuildProfile keyed **and read**: checks, panics, mm, exceptions, backend, `--opt`, `--cc`, `--cpu`/`sizeof(int)`, `--os`, `--passC` fragments (`-fwrapv`, `-ffast-math`), `nimOldCaseObjects`; outside the verified set -> `feBuildUnverified` | r (D sec.3) |
| W-51 | per-build native pins of decided memory rows on refc/orc/arc x release/danger x c/cpp (refc native-only) [B sec.3, B-16] | P |
| W-52 | shifts by >= width agree only because x86 masks [B-08]; `sizeof`/constant folding are host-compiler facts [C-15]; symbolic-divisor `low(int) div -1` unprobed [D-03] | P/r |
| W-53 | INT-31 widened to HRV-36's digest holes and `--opt/--cc/--cpu/--os` | r |

## 6. Test harness and CI

| W | item | ev |
|---|---|---|
| W-54 | 481 of 696 verdict-asserting symex suites (69%) have no native pin; every pre-RFC-0005 family unpinned [F-03] | ran |
| W-55 | native-pin helper copy-pasted in 52+ files; make one exported module (`nativeHits`, `verdict`, `declines(kind)`) [F-04] | ran |
| W-56 | 132 suites assert `sxUnknown` without naming the kind [F-05]; make `declines` require a kind | ran |
| W-57 | `symexAssume` is a no-op natively: native harness must enumerate the declared domain [F-07] | r |
| W-58 | no cfg suites for `--mm`, `--panics`, `-d:useMalloc`, setjmp on Linux, `-d:release` [F-08, D sec.6.7] | ran |
| W-59 | 48 non-symex suites run in no CI leg [F-06] | ran |
| W-60 | Linux has no per-push leg; Windows is the de-facto gate [F-10]; CI-A symex-linux, CI-B cpp + Z3 4.13.4 nightly, CI-C baseline artifacts + sweep-diff in CI, CI-D 60 s enforced, CI-F skip accounting, CI-G log provenance (`.summary` required) | r/ran |
| W-61 | probe results that agree today but have no pin: A-13 (defer/result, tuple swap, `var a, b = f()`, `char(x)`/`int8(x)`, char-range loop, symbol-bound alias), C-19 enums, B probe agreements | P |
| W-62 | existing CI rows: CI-02 (no cpp leg), INT-17 (30 suites > 60 s), HRV-89 mingw B5-4, HRV-90 msvc PR trigger, HRV-91 refc never tested, HRV-93 R1-12/13 unpinned, HRV-94 dt-bounded orphans, HRV-95 witness folding across nim-z3 | E |
| W-63 | JIT PCRE suites `skip()` on every build in use; Z3 4.13.4 verified only on Windows + release gate [F-09] | ran |

## 7. Hygiene and docs (one zero-tech-debt slice each, no walker bump)

- W-64: 12 `SymexErrorKind`s with no producer, plus two produced only in dead arms [HRV-05]; decide with INT-39 for 0.10.0.
- W-65: stale "STUB/defer/fail before GREEN" comments and dead boundary arms [HRV-31, HRV-99]; `caseNarrow` duplicate [HRV-32]; transparency `dOpaque` stubs [HRV-26].
- W-66: close six GitHub issues for shipped work: #152 #153 #160 #161 #162 #163 [HRV-96].
- W-67: RFC-0002 is listed but gitignored and absent; issues #146/#148/#149/#150 open [HRV-97]; commit or drop.
- W-68: stale docs: SYMEX_PLAN status block, ADR "PROPOSED" for landed ADRs, 0.9.0 known-gap text for landed items, RFC-0001 "Complete" and CLAUDE.md "active RFC 0001", 0014/0015 gates citing a pre-0.9.0 baseline [HRV-107..110].
- W-69: CLAUDE.md and `sweep-diff.sh` "not green on a good day" are stale on Linux (c 989/989, cpp 989/989 at 1a02b496) [F-02]; keep the diff gate, retire the wording.

## 8. Corrections to the existing RFC-0016 tables (from E, spot-checked)

- **Close (16):** SND-02, 03, 04, 05, 10, 11; PRC-27; CRH-02, CRH-04; PND-01, 02, 05, 07, 08, 09; INT-08, INT-24 (and INT-16, AUD-04, AUD-10 already closed).
- **Close as decline, keep a precision remainder (4):** SND-01 (-> HRV-01), SND-06 (-> PRC-21), SND-08, SND-09.
- **Duplicates (14):** INT-01/13/14 -> PRC-01/02; INT-02 -> CRH-03; INT-03 -> CRH-04; INT-04 -> CI-03; CRH-05 -> PRC-05; PRC-24 -> PRC-33; PRC-22 -> PRC-34; PRC-30 -> PRC-28; INT-10 -> PRC-04; PND-06 -> INT-20; CI-01 -> INT-17; AUD-08 -> PRC-12.
- **Reclassify (3):** INT-05 builds and declines (not a compile stop); PRC-16 is a walker fault; PND-11 is soundness.
- **Rewrite stale evidence (11):** CI-01, CI-03/INT-04, CRH-01, INT-20 (reports are on `origin/worker-sls2`), INT-28/INT-32 sub-items, PRC-11..14 ("probed at 136ad60"), PRC-26 (`nsc_dead` in no test); docs naming `ceUnsupportedCapture`/`geVtableDispatch` as firing are wrong.
- **Refuted lens claim, do not add:** F-01 (cpp log a copy of c). Column 4 is the warning count; the eos `.summary` shows backend=cpp 989/989.

Net: 86 distinct open table rows after collapse, plus about 100 harvested
items, plus the 60-odd new W rows above (many overlap the harvest).

## 9. Moves to RFC-0017 (reach, not parity)

N7/Q1/Q2/B0 scan recognisers and checksum loops (L2); N20 per-iteration
solve (L1); loop invariants #133 (L3); OQ1 path merging and CRH-03's ref-merge
OOM (P1); `maxLoopUnwind` never validated (M1); cross-module private
callees #138 (E1, cite #138); `maxRecursionDepth`/`maxHeapDepth`,
`geInstantiationCapped`, call-cache conservatism; `maxFrontierSize` default
and the stale `canonicalize.nim:2033` doc (P2); interval fixpoint across
iterations (0014 border, L3); RFC-0011 i3. Source: E sec.3.5.

## 10. "Declined, and it stays" records (closes a row without a model)

Each needs the reason and its evidence in the ledger, not prose:
`return` in `finally` on a raised path (c re-raises, cpp returns) [A-10];
Table/HashSet iteration order (hash and build dependent) [C-13]; pointer
order `<` [C-10]; `owned T`, `Atomic[T]` [HRV-18]; `nextafter` [HRV-27];
concurrency, sNaN payloads, float80, full Unicode case fold, symbolic-length
sort [HRV-105]; `addr s[0]` then growth (UB) [B sec.1.2]; Z3-version-dependent
`deepUnsat` [HRV-63]; AUD-01/AUD-09/AUD-11 records.

---

## 11. Closing the universe instead of whack-a-mole

Every Tier-0 bug has the same shape: **a clean model at a place that is not a
table** (a transparent `else`, a repr string, a stripped pragma, an unread
flag, a C-compiler fact). The carrier itself is sound: lens D traced 23
taint mechanisms (fork, merge, cache, unroll, prune, halt, replay, cache
load) and none loses taint. So the fix for the class is to turn each
implicit `else` into an enumerated table with a guard test, so the next
instance cannot be written silently.

| K | mechanism | closes | effort |
|---|---|---|---|
| K1 | **Universe ledger** `docs/rfc/0016-universe.tsv` + registered test `tsymex_0016_universe`: cells regenerated from enums/sources each build (constructs, type x memop, magics, stdlib arms, build rows, error kinds, RFC rows); every cell `exact(pin)` / `declined(kind, reason)` / `out-of-scope(reason)`; test fails on unclassified, stale, missing pin file, pin without native idiom, decline whose kind the pin does not assert. Its counts are the RFC's progress figure | the finish line itself | ~1 week |
| K2 | **Constructs:** child-shape census (getImpl a snippet corpus, assert IR or a named decline, `error()` fails); grep gate on transparent `else: parseExpr(...)` and `error(` in the parser (each hit allowlisted or `## closed:` with its pin); `typeIdOf(sym)` the only typeId source; replace the `else` at `:20699`/`:13379` with explicit arms over every `NimNodeKind` | W-01, W-04, W-21, W-27, W-33 | s each |
| K3 | **Type x memory-op table** keyed `(NimTypeKind, MemOp)`, read by `typeCopiedByValue`, `holdsSharedMemory` (inverted to a value-only list) and a new `localDeclGate`; guard tests over `NimTypeKind` and over Nim's var/let pragma list | W-02, W-12, W-20, W-43, B-04 | m |
| K4 | **Magic registry** (216 names, `mmArm/mmBody/mmDeclined/mmFold/mmNotRuntime`, pin + build axes per entry) + guard scanning all of `lib/` with multi-line decls; bodied magic not `mmBody` declines; stdlib bodies walked recorded as `feStdlibBodyWalked`, then an allowlist; every raise-text decline gets a `SymexErrorKind`; every stdlib body walked under a bound with one bounded run in the guard | W-05, W-06, W-22, W-24, C-11, C-16 | m |
| K5 | **BuildProfile** computed once, keyed, carried on `WalkCtx`, read by every arm that depends on it; outside the verified set -> `feBuildUnverified`; verdict carries the profile hash | W-03, W-07, W-14, W-17, W-23, W-50..53 | m |
| K6 | **One `mayWrite(n)` oracle**, allowlist of read-only kinds, replacing five denylist predicates; pinned on a write-shape corpus with native runs | W-08..W-10 | m |
| K7 | **Degrade discipline:** `w.halt(kind,msg)` returns no survivors; grep pin that `discard w.degrade(` appears only in S1 probes; grep pin that every check-option marker is consumed by a token or a halt | W-07, D-13 | s |
| K8 | **Differential fuzzer (slice D1)** with families per axis: constructs (incl. nesting), memory sharing, magic operand classes (literal/const/variable, widths, signedness), build rows; native domain enumerated exactly (W-57); runs scheduled per build row (CI-E) | finds the next W-01 before a user does | l |
| K9 | **Shared native-pin helper** and kind-required `declines`; migrate the 52 copies; pin the 481 unpinned verdict suites by family (generated where the SUT is a pure proc) | W-54..W-56 | m + long tail |

## 12. The finish line (D-0016-1, made checkable)

RFC-0016 is done when all five hold:

1. `tsymex_0016_universe` is green on c and cpp, Z3 5.1 and 4.13.4, Linux and
   mingw: zero unclassified cells; every `exact` cell native-pinned on each
   build row it claims; every `declined` cell's pin asserts its kind.
2. Every RFC-0016 table row maps to cells that are all `exact` or `declined`.
3. No failing file on any gate; no `skip()` or platform arm without a cell;
   no unnamed `sxUnknown` assertion.
4. Every fuzzer family has coverage on each build row it is claimed on; the
   generator's unexercised-production count is zero.
5. The certifying gate logs carry their `.summary` sidecars.

Size: about 1,000-1,100 cells, most classified in bulk from the code's own
dispatch tables; the long tail is about 250 construct cells and about 190
type x op cells that each need a pin. Lens F's estimate: 2-3 months of slice
work plus fuzzer hours. That number is the honest answer to "where is the
finish line": known, finite, and measured by one test's output.

## 13. Recommended order

1. **Wave 1 (days):** W-01..W-07 with three-way rows, walker bump, CR2 pin;
   W-20, W-21, W-26 (cheap compile stops/host crash); W-31, W-32 (cheap,
   high-frequency precision). Patch release 0.9.2.
2. **Wave 2 (1-2 weeks):** K1 ledger + enforcing test (initially reporting,
   not failing), K9 helper, K7 discipline, CI-A symex-linux leg, table
   corrections from sec.8, hygiene W-64..W-69.
3. **Wave 3 (weeks):** K2, K3, K4, K5, K6 in that order; each converts a
   denylist into a table and surfaces its own cells; probes for Tier 1 and
   W-27..W-29 as each table lands.
4. **Wave 4:** K8 fuzzer per family; flip K1 to failing on unclassified.
5. **Long tail:** precision rows by frequency (sec.4 order), pins for the
   481 suites by family.

## 14. Tracking in quipu

Today quipu counts 8/17 front-matter rows for 0016 and none of the 126 table
rows, so "the work list is empty" has no measure. Recommendation: one
`[[item]]` per Tier-0 bug and per K mechanism (about 20 rows, each with
evidence claims), and the universe ledger's state counts as the fine-grained
figure, printed by the enforcing test and quoted in the handoff. Putting all
~250 rows into front matter would duplicate the ledger.

## 15. Decisions (Corey, 2026-11-06)

- **D-1 Order:** Wave 1 fixes ship as a 0.9.2 patch ahead of the closure
  work, but only after this design passes `/architect`, since W-01..W-03's
  fixes are instances of K2/K3/K5.
- **D-2 Tracking:** about 20 `[[item]]` rows (one per Tier-0 bug and per K
  mechanism) plus the generated universe ledger as the fine-grained figure.
- **D-3 refc:** refused by name (`feBuildUnverified` / compile-time error with
  a named reason), not supported.
- **D-4 Int-offset soundness (N24/#166/#169):** owned by RFC-0014; 0016
  carries a pointer row.
- **D-5 Wrap mode:** replaced by K10 below (UB as an outcome).

## 16. K10: C-level undefined behaviour is an outcome, not a value

Neither "wrap" nor "trap" is right for unchecked arithmetic: with checks off
Nim emits plain C operators, and signed overflow, division by zero,
`INT_MIN / -1`, `INT_MIN % -1` and shifts by `>= width` are undefined in C.
The compiler may assume they never happen (gcc folded `v + 1 > v` away,
D-02; it folded `x % -1` to 0, C-01; a variable divisor traps). Replay on one
build is not evidence either (W-13's lesson).

Design (the CBMC / Frama-C RTE / Alive2 treatment):

1. **Definedness condition per unchecked op.** The predicates exist
   (`addNoOverflow` etc., `runtime.nim:8478-8492`, today used for the
   `OverflowDefect` fork).
2. **Fork on it.** Defined side: continue with exact semantics (no wrap model
   needed, nothing wrapped). UB side: the path halts with a new outcome
   `sxUndefined` (a `dcUndefined` degrade: no survivor, run `{scIncomplete}`),
   so `sxUnsat` is untrusted while UB is feasible and `sxSat` through a
   defined path stays trusted.
3. **UB is a first-class finding and target** (`tUndefined`, beside
   `tRaisedExn`): "signed overflow reachable at f.nim:12 with v = high(int)".
   Native pin: a UBSan build (`-fsanitize=undefined`) traps at exactly the
   witnesses the walker reports. Compiler-independent, unlike any wrap or trap
   pin.
4. **BuildProfile (K5) decides what is defined.** Unsigned: always wraps
   (defined), exact. `-fwrapv` read from the profile: signed add/sub/mul
   wrap, exact. Division by zero, `INT_MIN / -1`, `INT_MIN % -1`, shifts
   `>= width`: UB under every flag. Checks on: Nim's checked ops define
   overflow as `OverflowDefect` (today's behaviour).
5. **`arithChecks` stops meaning "pretend it wraps".** An "assume no UB"
   analysis becomes an explicit assumption carried on the verdict's soundness
   record, never a silent claim about the build. Breaking; 0.10.0 with INT-39.

Closes W-05, W-06, W-07, B-08 (shift width) and W-13 (`{.noinit.}` read is
an indeterminate value, the same outcome class) with one
(op x build-defines-it) table under K1. Effort m.
