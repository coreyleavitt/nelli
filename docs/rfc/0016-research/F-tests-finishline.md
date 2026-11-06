# Lens F — the test surface, and the finish line for RFC-0016

Snapshot `83c1d304` (src identical to the gated `1a02b496`). Gate logs:
`scratchpad/g11gate/{c,cpp}-1a02b496.log` (+ `.summary`, `.drift`,
`.warnings`), baseline `scratchpad/b11gate/*-8177eb27.log` (c, cpp, Z3 4.13.4),
`scratchpad/baseline-6cbfe8f.log` (`main` before RFC-0005). Every claim is
tagged `read` (a file read) or `ran` (a grep/awk/gh query I executed; no
builds, no probes). The per-file classification behind §2 is in
`research-out/F-testclass.tsv` (columns: is-symex, prefix group, file,
symex-entry count, native-idiom count, decline-assert count, verdict-assert
count).

## Headline findings (new rows, F-xx)

| id | finding | basis |
|---|---|---|
| F-01 | **The cpp gate log at 1a02b496 is not a cpp run.** `cpp-1a02b496.log` has the same rc, file and seconds on all 989 rows as `c-1a02b496.log` (0 diff lines on `(rc,file,secs)`), is exactly 1978 bytes larger (989 × `"cpp"−"c"`), has no `.summary`/`.warnings` sidecar (its `cpp.diff` says so), and `g11gate/c.out` is the only summary and reads `backend=c`. So there is no cpp evidence at 1a02b496. The "FIXED tsymex_rfc0005_s8by_remainder 1 -> 0" in `cpp.diff` is an artifact: that test file has no commits in `8177eb27..HEAD`. The last real cpp sweep is `b11gate/cpp-8177eb27.log` (968/969, one red) | ran |
| F-02 | **"Not green on a good day" is stale on Linux.** c: 989/989 at 1a02b496; Z3 4.13.4: 969/969 at 8177eb27 (`z413-all`); cpp: 968/969 at 8177eb27; `known_linux_hangs` is empty; `.drift` is 0/0/0. All three Windows legs are green at 1a02b496 (`gh run list`). The CLAUDE.md sentence and `sweep-diff.sh`'s header ("never green on a good day") should be retired; the baseline-diff gate stays, for the warnings and for the day it goes red | ran |
| F-03 | **69% of verdict-asserting symex suites have no native pin.** 696 of 854 `tsymex_*` files assert `sxSat`/`sxUnsat`/`sxRaised`; 215 use a native idiom (`symexCaptureBegin/End`, a local `nativeHits`, `replayWitness`, `assertCoveredBy`, a subprocess `nim c`); 481 do not. Every pre-RFC-0005 family is unpinned (phase15: 104 verdict suites, 2 native; r6: 51/5; 163rev: 29/0; phase16: 15/0). §2 | ran |
| F-04 | **The native-pin helper is copy-pasted, not shared.** `nativeHits`/`verdict`/`declines` are redefined per file (10 `proc nativeHits` definitions, 52 files with a local `template declines`); nothing in `src/` or `tests/*.nim` helper modules exports them, so a pin's meaning (hit-set equality, exhaustive or sampled domain) is per-file folklore | ran |
| F-05 | **132 suites assert a decline without naming its kind.** They `check r.status == sxUnknown` with no `fe*/se*/he*/ce*/be*/ee*/ge*/we*` identifier in the file, so a decline for the wrong reason (or a walker fault routed to `weInternalWalkerFault`) passes | ran |
| F-06 | **48 non-symex suites run in no CI leg** (fuzzer legs glob `^(tfuzz\|tdb\|tengine_)` plus five exact names, plus `tsmoke`, `trequiresinit`, `s8ab_letaudit` by name): `tbias tbisim tbmc tbundles tchoice tcombine tcoveragemode tcovsourcetable tdatasource tdeadline tderive tdetect tdisplay tdistribution tdsl tengine tevents texamples texplain tfrequency tjsonschema tlaws tlinearisable tmetamorphic tmining tmutation tn45probe tnested tparallelcheck tpipeline tprobe_n45stats trefine treporter treservedlabel trng tserialize tshrinker tshrinkpass tstateful tstrategies tstrategy tsymbolic ttarget tvariantbind twiderange tz3free_probe tautolabels tbiasthreading`. They pass only in local Linux sweeps. Out of 0016's soundness scope, but the differential fuzzer (§4) is built on `given`/strategies/shrinking, i.e. exactly these | ran |
| F-07 | **`symexAssume` is a no-op natively** (`markers.nim:127`, `discard cond`). §4's "declare the domain with `symexAssume` and enumerate natively" needs the native harness to enumerate exactly the declared domain (or the generator to emit the guard as a real early return); otherwise the native side runs inputs the walker excluded and reports false disagreements | read |
| F-08 | **No build-setting variant exists in the suite for memory manager, `--panics:on` or `-d:useMalloc`.** 52 `tests/*.nim.cfg` files carry 19 distinct flags (table in §3); none is `--mm:`, `--panics`, `-d:useMalloc`. §2.2 names verdicts that vary by memory manager (S8cn `ll_*`/`lg_*`); INT-23/INT-27 name `useMalloc` and `panics:on`. These are pinned nowhere | ran |
| F-09 | **Z3 4.13.4 and the PCRE builds are verified only off the Linux gate.** The three Windows legs pin Z3 4.13.4 (`--cc:gcc`/vcc); the Linux image is Z3 5.1; a Linux 4.13.4 sweep runs only at the release gate. The JIT PCRE suites (`s8cf_jitlimit_b`, `s8cf_jitutf`) `skip()` on every build in use (image PCRE 8.45 without JIT; Windows legs likewise) | ran |
| F-10 | **The Linux whole-suite gate runs only at batch boundaries, so Windows is the per-push gate.** Review finding G-01 (`0005-review.md:158`) was a kind-gate red caught by `symex-mingw` at 245e0fba, not by a Linux sweep, because no Linux sweep ran on that sha. §6 proposes the Linux leg | read |

## 1. What's red on a good day, and why

File-level status at the newest gated sha, both backends and both Z3 builds
(`ran`): **c 989/989, cpp (8177eb27) 968/969, Z3 4.13.4 (8177eb27) 969/969,
Windows symex-mingw / fuzzer-mingw / fuzzer-msvc green at 1a02b496.** So the
red inventory is one failing file, plus everything that passes only by
skipping, by asserting a platform-conditional decline, or by asserting an
unnamed decline. Each is either mapped to a 0016 row or given a new id.

| test | backend / leg | outcome | reason class | owning row | becomes green or an explicit decline by |
|---|---|---|---|---|---|
| `tsymex_rfc0005_s8by_remainder` | cpp (Linux, Z3 5.1) | **fail rc=1** at 8177eb27; "fixed" at 1a02b496 only in the rewritten log (F-01) | test-harness: `r.units == base.units` asserts Z3 spend equality; the spend drifts within one process on cpp (INT-04) | CI-03 / INT-04 | either assert outcome equality and a spend *ratio* bound, or make the units check c-only with the reason in the test; a real cpp sweep at the tag head to confirm |
| `tsymex_rfc0005_r1_replaychild` | Windows (all three legs skip it; symex-mingw runs the file) | passes by `skip()` ("POSIX only", `:262`) | platform: the replay-child tests are POSIX-only | INT-28/INT-29 (replay child hardening) | a Windows twin of the R1-18/19/20 checks (CreateProcess path), or an explicit out-of-scope note in the test naming the Windows row |
| `tsymex_rfc0005_s8cf_jitlimit_b` | every build in use | `skip()` unless `pcreRunsJit() and pcreVersion() == "8.37 2015-04-28"` | needs a PCRE 8.37 JIT build; the image has 8.45 non-JIT, Windows legs likewise | PND-01, PND-02, INT-19 | a PCRE-build matrix leg (the "differential-only leg for older PCRE builds", S8co item 2); until then the skip is an explicit decline, but it should be counted as one, not as a pass |
| `tsymex_rfc0005_s8cf_jitutf` | every build in use | `skip()` unless `pcreSearchEngine() == peJit837` | same | PND-02 | same |
| `tsymex_rfc0005_s8ct_deepterm` | Windows | passes by asserting `sxUnknown` where Linux asserts `sxSat` (`:116`, a `Lock` global cannot be handed to the re-exec child); teardown 78 s | platform-conditional pin | PRC-01, PRC-02, INT-08, INT-13, INT-14 | PRC-01/02 lift the re-exec marshalling; the pin then becomes `sxSat` on both. Until then the Windows arm must name the decline kind (`feReplayDeclined`), not just `sxUnknown` |
| `tsymex_rfc0005_s8ca_stack` | Windows | two checks under `when not defined(windows)` (`:149`, `:166`) | platform: stack-size behaviour | PND-03 (and S8cp item 6) | a Windows-specific expectation, or the row recorded as "stack size on Windows: declined, reason" |
| `tsymex_rfc0005_s8cu_nil_setjmp` | Windows | whole suite under `when not defined(windows)` (`:18`) | crash same as `main`: `--exceptions:setjmp` SIGSEGV entering the fiber | INT-12 | INT-12 fix, or a pin that the walker *declines* under setjmp on Windows instead of crashing |
| `tsymex_rfc0005_s8cu_nil_native` | Windows | passes; adds `--cc:gcc` for the child compile (`:27`) | OK, but only gcc: the MSVC half of "same build" is never exercised for this pin | CI-02 (backend/toolchain coverage) | an MSVC twin when the `symex-msvc` slot is filled, or an explicit "mingw only" note |
| 132 `tsymex_*` suites (F-05) | all | pass | an unnamed `sxUnknown` cannot distinguish a sound decline from a walker fault | **new F-05** (also PRC-04's inventory) | a shared `declines(fn, lbl, kind, why)` helper; a lint test fails any `check r.status == sxUnknown` not followed by a kind assertion |
| 107 `tsymex_*` suites that say "native" in prose but have no native idiom | all | pass | unverified claim dressed as a pin | **new F-03b** | re-pin with the shared helper or strip the word |
| `tfuzzcbuild`, `tfuzzcmplogshm`, `tfuzzcmplogshmleak`, `tfuzzcovreset`, `tfuzzcovshm`, `tfuzzshmhold`, `tfuzzworkerspawnfailshm`, `tprobe_n45stats` | env-dependent | `skip()` when the environment lacks a C compiler / shm | fuzzer infrastructure | out of 0016 scope (RFC-0003) | note only |
| `tfuzzwinjoblimits`, `tfuzzwinshm`, `tfuzzwinworker` | Linux | whole suite `when defined(windows)` | Windows-only suites; they run on the fuzzer legs | OK as designed | — |
| 931 of 989 suites | c | pass with 25,412 warnings (12,047 `UnusedImport`, 2,349 `Deprecated`, 768 `UnnamedBreak`, 55 `HoleEnumConv`, 43 `UnreachableElse`, 4 `ProveInit`) | gate noise; `sweep-diff` reports only the delta | **new F-11** | fix the two src-level ones that dominate (`symex.nim` unused `sha256`: ~800 new entries in `c.diff`; `dsl_typebridge.nim` `HoleEnumConv`); the gate then has a warnings floor it can hold at zero-new |

Also red by construction and already owned: CRH-03's OOM kill (`iteDeep`, 8.36 GB,
killed at 124–135 s; no suite runs it), CRH-05's 1400 s liveness (the pin uses one
insert), INT-18 (p7 declines where `main` decides).

**How "not green on a good day" ends.** (a) F-01: regenerate the cpp gate for
real and keep the `.summary` sidecar as the proof a log is what it claims
(`sweep.sh` prints `backend=` there; a log without a matching summary is not a
gate). (b) Every `skip()` and `when defined(...)` arm in a `tsymex_*` suite
names the 0016 row or the decline kind it stands for, and `sweep.sh` counts
them (it has a `skip` status already; the suites self-report via unittest's
skip, which the sweep does not see). (c) F-05/F-04: one shared pin helper. After
those three, "green" means: no red file, no unnamed skip, no unnamed decline.

## 2. Native-pin coverage of the existing suite

**Idioms found (`ran`).** The strongest is in-process capture on the same
binary: `symexCaptureBegin()` / run the SUT natively / `symexCaptureEnd()`
returns the labels `symexTarget` hit (`src/nelli/engine/markers.nim:72-110`);
the suite then compares with the walker's verdict (`nativeHits` wrappers in
71 files). Second, a subprocess `nim c` of the SUT with its own flags
(`execProcess`/`startProcess` in 11 files: `s8ct_isolation*`, `s8cu_nil*`,
`r1_replaychild`, `b11_hoststate`, `w2_settle`), which is the only idiom that
can pin a *different build* (check options, setjmp, re-exec). Third, the
engine's own replay (`replayWitness`, 33 files; `assertCoveredBy`, 13;
`symexForAll`, 14), which runs the witness natively but only confirms `sxSat`
and never refutes an `sxUnsat`. Zero suites use nelli strategies (`given`,
`forAll`) around `symexFind` (0 files), and only 3 use an explicit exhaustive
integer loop; "exhaustive" appears in 26 files' prose.

**Counts (`ran`, from `F-testclass.tsv`).** 854 `tsymex_*` files. 696 assert a
definite verdict; 215 of those carry a native idiom (31%); 481 do not (69%).
430 assert a decline; 132 of those name no kind. Only one `SymexErrorKind`
member (`geUnresolvedGeneric`) is named in no test; the other 80 appear
somewhere, so the decline-kind vocabulary is at least reachable from tests.

| family (prefix) | files | verdict-asserting | native idiom | unverified verdict suites | decline-asserting |
|---|---|---|---|---|---|
| rfc0005 | 485 | 386 | 207 | **179** | 263 |
| phase15 | 113 | 104 | 2 | **102** | 50 |
| r6 | 54 | 51 | 5 | **46** | 44 |
| 163rev | 31 | 29 | 0 | **29** | 14 |
| phase14 | 20 | 12 | 2 | 10 | 3 |
| phase16 | 16 | 15 | 0 | 15 | 3 |
| phase1–phase7 (7 groups) | 27 | 23 | 1 | 22 | 6 |
| rectify / retest | 16 | 14 | 0 | 14 | 6 |
| 163 / 163audit | 6 | 5 | 0 | 5 | 2 |
| snd1/1b/2/3/4 | 6 | 6 | 0 | 6 | 4 |
| r1–r14, q1, p1/p2a/p2b, a2–a9, CR2a/b/c, cr9c, cr22, h, m6, ot1, funcdef, discard, augmented, uninit, configdefaults, 161/162 | ~60 | ~51 | 1 | ~50 | ~30 |
| phase11/12/13, g*, canonicalize, typebridge | ~21 | 4 | 4 | 0 | 2 |

Reading: everything RFC-0005 did not touch is a self-consistency suite. The
areas the other lenses enumerate (constructs, types × memory, magics) will
largely land on phase15 / r6 / 163rev pins that were never run natively. Any
`sxSat`/`sxUnsat` there is an unverified claim under §0's rule; the
closed-universe ledger (§5) must not count them as `exact+native-pinned`.

## 3. Drift

| axis | state | basis | owning row / new id |
|---|---|---|---|
| Registry | `.drift`: 0 unregistered, 0 missing, 0 stale skip entries; 989 files on disk, all in `nelli.nimble`'s `test` task | ran | — |
| Linux c gate | local only (`sweep.sh`, 4–6 jobs, 900 s timeout); 423 CPU-min for 989 files; run at batch boundaries | ran | F-10, §6 |
| Linux cpp | **no leg**; last real sweep 8177eb27 on eos (968/969); the 1a02b496 "cpp" log is a copy | ran | CI-02, F-01 |
| Z3 4.13.4 | Windows legs only on push; Linux 4.13.4 only at release gate (`z413-all` 969/969 at 8177eb27) | ran | CI-02 |
| Windows `symex-mingw` | derived from `nelli.nimble` (floor 150, accounting check); skip list **empty**; 9 scan-tail matrix suites; 24 corpus shards of 14–27 min (run 41934332864); 854 `tsymex_*` per push on `main`/`rfc-*`, docs-only pushes excluded; Z3 4.13.4; `--cc:gcc` | ran | CI-01 |
| Windows `fuzzer-mingw` / `fuzzer-msvc` | glob `^(tfuzz\|tdb\|tengine_)` + 5 exact + `tsmoke`, `trequiresinit`, `s8ab_letaudit` (85 + 3 suites); 15 / 24 min | ran | — |
| Non-symex suites in no leg | 48 (list under F-06) | ran | F-06 |
| `symex-msvc` | deliberately empty slot (header, 2026-09-03); the only MSVC exposure is the fuzzer-msvc leg's 3 named symex/aux suites | read | CI-02 |
| Windows-pinned verdict differences | `s8ct_deepterm` (decline on Windows), `s8ca_stack` (two checks off), `s8cu_nil_setjmp` (suite off), `r1_replaychild` (skip) | ran | §1 |
| Per-file build flags (`tests/*.nim.cfg`, 52 files) | `-d:symexQueryStats` ×26, `-d:nelliReplayReexec` ×8, `-d:symexTestInjectWalkerFault` ×6, one each of `--checks:off`, `--boundChecks:off`, `--overflowChecks:off`, `--rangeChecks:off`, `--fieldChecks:off`, `--objChecks:off`, `--assertions:off`, `--floatChecks:on`, `-d:danger`, `--opt:none`, `-d:nimCallDepthLimit`, `-d:nelliVmAliasAudit`, `-d:z3WithSeqReplaceAll`, three `--warningAsError`; 22 suites use in-file `{.push ...Checks.}` | ran | F-08 (no `--mm`, `--panics`, `useMalloc` variant) |
| PCRE builds | image 8.45 non-JIT; JIT suites skip everywhere | ran | PND-01/02, INT-19 |
| Examples | built on `symex-mingw` (step "All examples built and ran") and by `scripts/check-examples.sh`; not on Linux CI | read | — |
| Per-file 60 s convention | Linux c: 5 files over 60 s (max 79 s: `s8s_precision_h`, `phase11_walker`, `s8bz_overlap`, `s8f_witness`, `CR2c_witnessreader_catchall`); Windows: 30 over 60 s, max 127 s (`ci-suite-seconds.tsv`, 825 rows, 529 min total) | ran | CI-01, INT-17 |

## 4. The differential fuzzer (§4): a concrete generator spec

**Shape of one run.** A nelli property draws a *module* of K SUTs (K ≈ 20–40,
so one ~24 s compile serves all: S8ca item 9), writes it to a temp dir,
compiles it once with `symexFind` over every label and once as a native
enumerator, and compares per label. The module is the unit of compile; the
SUT is the unit of shrinking and of the ledger row.

**SUT skeleton.** `proc sut_<n>(x0, x1, x2: int)` with inputs declared in a
small domain `lo..hi` (default `0..7`, three inputs = 512 points; up to five
inputs = 32,768, still cheap natively). The domain is emitted twice: as
`symexAssume(x0 in lo..hi)` for the walker **and** as the native enumerator's
loop bounds (F-07: `symexAssume` is a no-op natively, so the native side must
never run an input the walker excluded). A SUT carries 3–6 labels
(`symexTarget("L<k>")`) placed by the grammar at statement boundaries, in
branches, after loops, in handlers, and in hooks.

**Grammar productions.** Each production is a named family so the coverage
metric (below) can count it. Draft universe, aligned with the other lenses'
axes:

| family | productions (each a strategy) |
|---|---|
| statements | `var`/`let` decl; assignment; compound `+=`/`-=`/`inc`/`dec`; `swap`; `discard call`; `block`/`break` with label; `return` mid-body; `if`/`elif`/`else`; `case` on int/enum/range (with and without `else`); `while` with a bounded counter; `for` over `0..<n`, over `items`/`pairs`/`mitems` of a seq, over `keys` of a Table; `try`/`except` (typed, catch-all, nested, inner `try` in a handler); `finally` with `return`/`break`; `raise` user exception / defect; `defer` |
| expressions | int arithmetic with overflow reach; `div`/`mod` with a zero reach; comparisons; `and`/`or` short-circuit with a call on the right; `succ`/`pred`; conversions (`int8`, `uint8`, range, holey enum); `cast`; string `&`, `len`, `[i]`, `[a..b]`; `$` of int/char/enum/float; set literal small (`set[0..7]`) and large (`set[0..255]`), `incl`/`excl`/`in`/`card`; tuple construct/unpack; object construct with and without discriminator; `isNil`; `addr`/`unsafeAddr`/`[]` deref |
| types (declared per module) | object, object with `case` discriminator (2–3 arms, shared field names), tuple, `ref object`, `ptr`-of-object, `distinct int`, enum (contiguous, holey, string-named), `array[0..3, T]`, `seq[T]`, `seq[seq[int]]`, `string`, `Table[string,int]`, `Table[int,Obj]`, `HashSet[int]`, `HashSet[string]`, `set[E]`, `Option[int]`; T drawn recursively to depth 2 |
| memory routes | module-level `var` read / written / aliased by `ptr`; by-value param of each type above (allowlist S8cq); `var` param; `lent`; `openArray` view over seq/array, written through (`fill`); `addr` of a local escaping to a global; `ref` shared by two locals; closure capturing a local / a loop var / a `var` param; `=destroy`/`=copy`/`=sink`/`=dup` hooks that write a global or a `ref` field; `setLen`/`add`/`del`/`pop` on a seq that another view reads; a call inside an lvalue (`s[nextI()] = v`); argument evaluation order with side effects (`f(g(), h())`) |
| calls | direct; through a proc value; `method`; recursion to a bounded depth; generic instantiation (two instantiations of one generic); iterator (inline and closure); `template` with a side-effecting argument; `procCall`; opaque routine (`{.noSideEffect.}` lie, `importc` stub, `{.emit.}`) |
| magics / stdlib allowlist | one production per allowlisted name (the ~80 quoted names in `dsl_parser.nim`'s `of "..."` arms and the ~50 `{.magic: "X".}` names at `:3990-4320`) with each argument drawn from the type family, plus one "unlisted" production (a routine the walker must decline) |
| regex (shares the harness, S8co item 2) | literal patterns from a small PCRE grammar × `match`/`contains`/`find`/`replace`/`count`, subject strings from a 3-letter alphabet of length 0..6 |
| check options (per module, not per SUT) | module compiled under one of: default; `--overflowChecks:off`; `--boundChecks:off`; `--rangeChecks:off`; `--fieldChecks:off`; `--checks:off`; `-d:danger`; a `{.push overflowChecks:off.}` region around a routine; `--panics:on`; `--mm:orc`/`arc`/`refc`; `-d:useMalloc`; `--exceptions:setjmp` (Windows) — each is a `build` row in the ledger (§5) |

**Native oracle.** The enumerator is the same module compiled without the
`symexFind` calls: for each SUT, for each point in the domain, run with
`symexCaptureBegin/End`, record the hit label set and the exception type (if
any), and write one line `sut label input hit/raised:T`. Exhaustive because
the domain is finite and small, so an `sxUnsat` is refuted by a single hit and
confirmed by an empty column. For labels inside hooks, the enumerator must run
each input in a fresh process group or at least reset the module globals
between inputs (a generated `reset()` that re-assigns every global's initial
value), otherwise global state leaks between points and the "no input reaches
it" claim is about a sequence, not a point.

**Comparison and triage, automated.** Per (SUT, label, build): walker status
∈ {sat(w), unsat, raised(T,w), unknown(kind)} against native ∈ {hit-set,
raised-set}. Disagreement classes: `sat-no-hit` (witness `w` does not reach the
label natively), `unsat-hit`, `raised-mismatch`, `sat-raised`; a decline is
never a finding and is counted into the precision rate by `kind`. Every
disagreement is re-run with the same seed on the last release tag (a second
checkout in the same container: same backend, Z3, PCRE, flags) to fill the
three-way row, so the §2.4 severity (`worse`/`same`/`better`) is computed, not
judged. Fingerprint = (disagreement class, production set of the shrunk SUT,
decline kind if any); one ledger row per fingerprint, with hit count.

**Shrinking.** nelli's choice-sequence shrinker reduces the generator's
choices while the oracle still disagrees; the shrunk SUT is re-emitted as a
single-SUT module, re-compiled on both sides, and that source (typically
10–20 lines) goes into the `F-NNNN` row's `shape` field. The RFC-0005 blockers
were all of that size, so a minimal SUT is the expected output, not a hope.

**Cost per SUT.** Compile ≈ 24 s/module c (S8ca item 9), two compiles per
module (symex + native), ≈ 1.5 s/SUT amortised at K=32. Walk + solve: the
suite's own median is a few seconds per `symexFind` (735 of 989 files finish
under 30 s with several finds each), so budget ~5 s/label × 4 labels = 20 s;
native enumeration < 0.1 s. Roughly **100–150 SUTs per CPU-hour**, 2,500–3,500
per day on the 12-core worker. A `seqQueryRLimit`-sized budget per label keeps
a bad draw from eating the hour; a label that times out is `unknown(budget)`
and counted as precision, not hang, unless the process dies.

**Generator coverage metric.** The generator reports, per family and per
production: SUTs emitted, labels with a definite verdict, labels declined (by
kind), CPU-hours, findings by class. A production is *exercised* once it has
≥ N (say 200) SUTs with at least one definite verdict depending on it, on
each build row. A family's CPU-hours are the §3.1 unit. The report is a table
the ledger (§5) consumes: a cell is `fuzzed` only when its production is
exercised on that build.

## 5. The finish line, defined so it is checkable

**The closed universe.** A ledger `docs/rfc/0016-universe.tsv` (one row per
cell, generated and then annotated) whose rows are the product of a few
mechanically enumerated axes, each row in exactly one state. States:

- `exact` — the walker decides it; requires ≥ 1 named pin test with a native
  idiom on the same build, and the fuzzer production that covers it exercised.
- `declined(kind)` — the walker declines with a named `SymexErrorKind`,
  pinned by a test that asserts the kind; reason recorded (theory cannot
  express / measured out of budget with the number / platform).
- `out-of-scope(reason)` — never walked (e.g. `nnkAsmStmt`, `nnkIncludeStmt`,
  `mNewSeqOfCap` in a context the walker never sees), with the reason.
- `unclassified` — the only state the enforcing test rejects.

| axis | rows | generated from | note |
|---|---|---|---|
| A. construct | `NimNodeKind` (≈120 members in Nim 2.2; `read`: `dsl_parser.nim` names 119 distinct `nnk*`) × context {statement, expression, lvalue, iterator body, handler, hook body} ≈ 720, of which most are `out-of-scope` by kind (literals, type nodes) → ~250 live cells | `low(NimNodeKind)..high(NimNodeKind)` at compile time in the test itself, so a new Nim adds rows | contexts are the walker's own walk entry points (`parseStmtInner`, expr lowering, iterator inline, `routeRaise`) |
| B. type × memory op | `IRTypeKind` (17) × op {read, write, by-value param, `var` param, `lent`, `openArray` view, `addr`/`ptr` deref, global, closure capture, hook, container element} = 187 | `IRTypeKind` enum (`types.nim:47`) | plus the Nim-level shapes the bridge maps onto each kind (case object, holey enum, distinct, nested seq) as sub-rows where S8cq's allowlist distinguishes them |
| C. magic | `TMagic` members (several hundred; the exact count is read from `compiler/ast.nim` in the container, not available on this host) | a script run in the dev image dumps `TMagic` names with the Nim version; the test checks the ledger's stamp equals `NimVersion` | the walker matches by `{.magic: "X".}` name (`dsl_parser.nim:3994-4302`, ~50 names); every other magic is `declined(feOpaqueCallUnmodelled/feUnsupportedOp)` or `out-of-scope` |
| D. stdlib allowlist | the ~80 quoted routine names in `dsl_parser.nim`'s `of "..."` arms, each × the type family it accepts | a test extracts the arms with a compile-time read of the source (the N2 kind-gate audit already reads `dsl_parser.nim` this way) | an entry with no pin is `unclassified` |
| E. build row | {c, cpp} × {Z3 5.1, 4.13.4} × {orc, arc, refc} × {default, each `--*Checks:off`, `--checks:off`, `-d:danger`, `--panics:on`, `-d:useMalloc`, setjmp} × {PCRE 8.45, 8.37 JIT, 8.39 JIT, 8.44 JIT} — listed as rows, not a product: each is a row stating which cells of A–D are pinned on it | the cfg flags table (§3) plus §2.2's list | today only the default c/Z3 5.1/PCRE 8.45 row is anywhere near covered |
| F. decline vocabulary | `SymexErrorKind` (81) | the enum | each kind must be *reachable*: named by ≥ 1 test (80/81 today) and by ≥ 1 cell in A–D; a kind no cell names is dead and is deleted |
| G. existing rows | every 0016 item (SND, PRC, CRH, CI, INF, UPS, PND, INT, AUD, F) | the RFC's tables | each maps to ≥ 1 cell; an item whose cells are all `exact` or `declined` is closed |

Size: roughly **250 + 187 + ~400 + ~80 + ~25 + 81 ≈ 1,000–1,100 cells**, most of
which classify in bulk (out-of-scope kinds, declined magics). Effort: the
generator script and the enforcing test are one slice (a week); classifying
the bulk from the code's own dispatch tables is mechanical (the `of` arms *are*
the allowlist); the long tail is the ~250 construct cells and 187 type×op cells
that need a pin each, which is where the other lenses' gap lists land. At the
suite's current rate of ~5 pins per slice-day with the shared helper (F-04),
that is 2–3 months of slice work plus the fuzzer's hours.

**The enforcing test** (`tests/tsymex_0016_universe.nim`, registered, in the
Linux and Windows corpora): at compile time, regenerate axes A, B, F from the
enums and axis D from the source; read the ledger; fail on (1) any generated
cell missing from the ledger ("a new Nim version / a new error kind added
rows"), (2) any ledger cell not generated ("stale row"), (3) any cell in two
states or in `unclassified`, (4) any `exact` cell whose pin test file does not
exist, is not in `nelli.nimble`, or contains no native idiom (the helper's
name, once F-04 lands), (5) any `declined` cell whose kind is not asserted by
its pin, (6) any `exact` cell whose fuzzer production has no coverage entry
for the build rows it claims. The same test prints the ledger's state counts,
which is the RFC's progress figure (`unclassified` → 0, `exact` share).

**"Done" (D-0016-1, made checkable).**
1. `tsymex_0016_universe` is green on c and cpp, Z3 5.1 and 4.13.4, Linux and
   mingw: zero `unclassified` cells, every `exact` cell native-pinned on the
   build rows it claims, every `declined` cell naming its kind.
2. Every row of §5 and §5.8 maps to cells that are all `exact` or `declined`
   (an item with a `declined` cell keeps its reason in the ledger, not in prose).
3. §1's table is empty: no failing file on any gate, no `skip()` or platform
   arm in a `tsymex_*` suite without a named cell, no unnamed decline (F-05).
4. Every fuzzer family has a coverage entry on each build row it is claimed
   on; the generator's own `unexercised production` count is zero.
5. The gate logs that certify 1–4 carry their `.summary` sidecars (F-01).

## 6. CI and test time

Numbers (`ran`): Linux c sweep = 25,412 s = 423 CPU-min for 989 files; 735
files under 30 s, 249 in 30–60 s, 5 over 60 s, max 79 s; on a 4-core GitHub
runner that is ~1 h 50 m wall in one job, ~15 min in 8 shards. Windows
`symex-mingw` already does this: 24 time-balanced shards of 14–27 min for 854
symex suites (529 CPU-min on Windows). `fuzzer-mingw` 15 min, `fuzzer-msvc`
24 min.

Proposals:

| id | change | why |
|---|---|---|
| CI-A | **`symex-linux` leg on every push** (`ubuntu-latest`, c, Z3 5.1): reuse `derive-ci-suites.ps1`'s shard placement (it is pwsh; it runs on ubuntu already in the `derive-suites` job), 8–10 shards, per-suite watchdog 240 s as on Windows, and run the **whole** `test` task, not only `tsymex_*` (closes F-06). Z3 comes from the Linux Z3 release or from `scripts/build-dev-image.sh`'s image via podman on the runner | F-10: today Windows is the only per-push gate; G-01 was found there |
| CI-B | **`symex-cpp` leg on `main` nightly and on `rfc-*` by label**, same shards, `--backend:cpp`; plus a **Z3 4.13.4 Linux** matrix row on the same schedule | CI-02, F-01: cpp has no leg and the last gate log for it is a copy |
| CI-C | **Baseline artifacts**: each `main` run uploads its `sweep.sh` log + `.summary` + `.warnings`; `rfc-*` runs download the `main` baseline and run `sweep-diff.sh`, failing on REGRESSED or NEW WARNINGS only | makes "what moved" the CI verdict, not a local ritual; retires the "not green on a good day" wording |
| CI-D | **60 s convention enforced by the sweep**: `sweep.sh` and the shards flag any file over 60 s compile+run as a `ci` finding (§3.2 class) rather than letting it accumulate in the tsv; the 30 Windows and 5 Linux offenders get split (each is "a single long test or compile-bound" per INT-17: split by suite, or move the long query to a scan-tail-style isolated job) | CI-01, INT-17, PRC-31 (`configdefaults_depth` under 60 s) |
| CI-E | **The fuzzer (§4) as a scheduled job** on a Linux runner, 2 h per run per build row, uploading its coverage table and any `F-NNNN` candidates; this is also where the Linux cpp and 4.13.4 rows get their hours | §4.2 "Where it runs"; it does not run on every push |
| CI-F | **Skip accounting**: unittest `skip()` is invisible to `sweep.sh` (rc=0); make the suites print `SKIP <reason>` and have the sweep count it into the summary, so §1's skips are a gate figure | §1 |
| CI-G | **Log provenance**: `sweep-diff.sh` refuses a current log without its `.summary` whose `backend=` matches the log's second column | F-01 |

Cost: CI-A adds ~15–20 min of 8-way Linux runner time per push (ubuntu minutes
are the cheap ones); CI-B adds the same twice nightly. The local eos sweep stays
the tool for a worktree-pinned baseline, but it stops being the only gate.
