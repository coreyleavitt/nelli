# Changelog

Notable changes to nelli. Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
versioning is [semantic](https://semver.org/spec/v2.0.0.html).

> **Why this file now.** Releases through 0.6.0 carried their notes in the
> release commit message alone. That works while the surface is additive; it
> stops working the moment a downstream maintainer has to migrate. 0.7.0 is
> breaking in three separate ways, and the one real downstream (chapulin) has
> **not yet absorbed 0.6.0's own breaking change** — so it must migrate across
> two releases at once, from a document it can actually find. 0.6.0 is
> reconstructed below from its release commit for exactly that reason.
> RFC-z3-optional S5 adopted this as a deliberate practice, not a one-off.

## [0.9.2] — 2026-11-07

This release is Wave 1 of RFC-0016 (native-parity hardening): the seven clean
false verdicts the 2026-11-06 research round found (RFC-0016 §5.0, W-01 to
W-07), the model of undefined behaviour the checks-off work needed, the
Wave 1 wiring audit (WA-A and WA-B, handoff entries of 2026-11-07) and the
code review of the same surface (`docs/rfc/0016-review.md`, two rounds, floor
at round 2). Slices are cited as W1-x and the audit's fixes as WA-x; review
findings by the id the ledger gives them (SC2, D1, M2 to M6, N1, R2-01).
Upgrading: `docs/migration/0.9.2.md`. The verdict fixes come first, ordered by
how wrong the old answer was: a trusted `sxSat` or `sxUnsat` that native Nim
contradicts, then a raise or confinement the build does not do, then
constructs that declined and now decide.

The walker version moves from `"272"` to `"287"` (fifteen bumps), and the
soundness codec from version 3 to 4. Every 0.9.1 cache entry is orphaned; the
first run after the upgrade is cold.

### Fixed — wrong clean verdicts

- **A generic exception type is no longer identified by its last type
  argument** (SC2). `typeIdOf` took the last child of any bracket expression,
  so `G[ValueError]` got the id `ValueError`, and `except ValueError` caught a
  `G[ValueError]` that escapes natively: a trusted `sxSat` for a target in the
  handler. Only `ref[T]` and `ptr[T]` unwrap now; any other instantiation
  declines `eeUnknownExnType` (the exact model is PRC-38, below). Walker 287.
- **`except T as e:`, `raise e`, and a handler naming a type through an alias**
  (W1-a, W-01). A raise site and a handler stored different ids for one type
  (the `repr` of the node), so a handler was missed (a false `sxUnsat` for its
  label) or the wrong type matched (a false `sxRaised`). One id now comes from
  `canonicalExnTypeSym`; `raise e` has the static type of `e`. An exact raised
  value is modelled only for a `let`-bound `newException`; a handler whose type
  cannot be named declines. Walker 273.
- **`--panics:on`: a `Defect` inside a `try` ran its `except` arm and
  `finally`** (W1-c2, W-03). Natively a `Defect` ends the process under
  `--panics:on`; a label after it was a clean `sxSat`. `routeRaise` now tests
  defect-ness before the handler search and sends a known `Defect` down the
  crash channel: no `except` arm or `finally` runs, and the claim is a crash.
  Every crash claim carries `witnessUnsafe` (it was set only on some), and the
  flag survives the replay settle and the cache, so a lossy `AssertionDefect`
  claim under `--panics:on` is no longer reported host-runnable (WA-B). A
  `raise` of an unknown-typed `ref Exception` under any `try` declines. Walker
  274, 286.
- **`low(T) mod -1`, `low(T) div -1`** (W1-d1a, W-05). The walk trapped
  regardless of the divisor and confined the survivor, a false `sxUnsat`
  where gcc folds the expression. Natively the operation is SIGFPE on x86-64.
  The path now halts (`ubIntMinModMinusOne`; the unchecked `div` case is
  `ubSignedOverflow`), 32 and 64 bits.
- **Unsigned `div` or `mod` by zero** (W1-d1b, W-06). It was a catchable
  `DivByZeroDefect` (a `sxRaised`, or a trusted `sxSat` through an `except`
  arm). Natively it is SIGFPE; Nim has no check for it. The path now halts
  (`ubUnsignedDivZero`). The opaque-call scan no longer lists
  `DivByZeroDefect` for the unsigned division magics.
- **Signed `+`, `-`, `*` and negation overflowing with the overflow checks
  off** (W1-d2a, W-07). The walk wrapped (two's complement), so `v + 1 > v` at
  `high(int)` was a clean `sxSat` while gcc folds it to true. The operation is
  undefined in C: the overflow side is an `ubSignedOverflow` trap, pruned where
  unreachable and otherwise halting the path. Signed 8 and 16 bit arithmetic
  is computed in C's promoted `int` and narrowed, a defined wrap, so it does
  not halt; 32 and 64 bit stay undefined (WA-B). Walker 282, 286.
- **Signed `div` or `mod` by zero with the overflow checks off** (WA-B). Nim
  emits no zero check then and the C division is undefined (SIGFPE on x86-64).
  It was a definite trap that confined the survivor, with no omission
  recorded. The path now halts as `ubSignedDivZero`, appended to `UbKind` so
  earlier codec ordinals hold. Walker 286.
- **A `{.noinit.}` local read before any write** (W1-d3). The value was
  unconstrained and trusted. The reading path now records
  `ubIndeterminateRead`; the verdict is not `trusted()` and is not run in your
  process. Walker 281.
- **A local with `{.cursor.}`, `align`, `volatile`, `codegenDecl` or any
  pragma outside `noinit`, `global`, `inject`, `gensym`, `used`** (W1-b, W-02).
  The parser dropped every local pragma but `noinit`, so a `{.cursor.}` that
  shares memory was modelled as a copy: a false `sxUnsat` and a false `sxSat`
  on c/orc, c/arc and cpp. It declines `feLocalPragma` on every path that
  reaches it (the exact model is PRC-39, below).
- **`float32` <-> `float64` conversions, explicit or compiler-inserted**
  (W1-e, W-04). The conversion was a transparent pass-through, so a value of
  one width flowed on as the other (`float64(float32(x)) == x` was decided).
  It declines `feFloatWidth` (the exact model is PRC-40, below). int <-> float
  verdicts are unchanged.
- **`{.push overflowChecks: off.}` on a routine** in a checking build is modelled as the
  settings said; it always declines now (`feOverflowCheckOption`) (W1-d2).
- **A call summary that relied on a pruned undefined side** was reused
  anywhere. It is reused only where the prune holds (W1-d1c).

### Fixed — wrong in a checks-off build, or declined without cause

- **Closure-iterator loops and unchecked ordinal steps in a checks-off
  build** (WA-A). A `for` over a closure iterator was replaced by an empty
  block; it is inlined now. `inc`, `dec`, `succ`, `pred` and `+=` on an enum,
  char or range raised `OverflowDefect` where the arithmetic is unchecked; the
  out-of-range side now declines as unmodelled. A magic-backed callee (`abs`)
  takes its caller's arithmetic scope, and a closure iterator compiled under a
  different scope than its caller declines. Walker 285.
- **`{.push overflowChecks: on.}` on a routine in a checks-off build** was
  modelled with the unchecked model. Checked-ness is per routine now (W1-d2c):
  such a body raises `OverflowDefect` and `DivByZeroDefect` whatever the
  build-derived settings say, and a call across the boundary keeps each side's
  own arithmetic. Walker 283.
- **`assertCoveredBy`, a witness that reaches the target and then raises a
  `Defect` the splat has no arm for** (W1-c3, W-26). The `Defect` unwound out
  of the call and, with no handler above it, ended the process. The call
  reports the finding and the host survives (panics-off only).
- **`x in a .. b` and `x notin a .. b`** over an ordinal, including
  non-constant `..<` bounds, declined (W1-g, W-31). They lower to `a <= x and
  x <= b`, pinned against native including the boundary.
- **`case ... elif`** in statement, expression and hoisted forms declined
  (W1-f, W-21). It is modelled.
- **A `seq` field default `@[]` or `@[1, 2]`** reached the parser as a bare
  `[]`: a compile stop for an empty default (W1-f, W-20). A bracket typed
  `seq[T]` is lowered as a seq literal. The slice's premise that object field
  defaults needed a decline was wrong: native `var o: T` reads zero while
  `default(T)`, constructors and `new` apply the defaults, and the walker
  already agreed in every shape.
- **A re-executed replay (Windows) of a SUT naming its own routine
  `{.global.}`** was refused, so the verdict stayed `sxUnknown` where the POSIX
  fork confirmed it (W1-m). A global named from inside its own routine links in
  the child and is confirmed; one named from another routine stays open.
  Walker 284.
- **`symexFindAllWitnesses` and `symexForAll` on a SUT with no parameters**
  did not compile (N1). The first annotated the witness with an empty tuple
  type, the second passed a zero-argument SUT as a one-argument property. Both
  accept the SUT now. `concolicAssist` still refuses zero parameters by design.

### Changed

- **`SymexSettings.arithChecks` derives from the build** (W1-d2a).
  `defaultSymexSettings` calls `arithChecksFor`: a debug build is all-on,
  `--overflowChecks:off` drops `acOverflow` and `acDivByZero`,
  `--rangeChecks:off` drops `acRange`. A value that disagrees with the build
  taints the run `feCheckOption`: the program the build compiles does not do
  what the setting says. An opt-out through `arithChecks` therefore no longer
  yields a clean verdict. See Deprecated.
- **Undefined behaviour rides the path and the verdict** (W1-d3). The omission
  is recorded on `Path.undefined`, joined by every taint carrier, and the
  verdict carries `Soundness.witnessUndefined` (`undefinedKinds()`). A replay
  cannot lift it: such a witness is not `trusted()`, and neither `symexForAll`
  nor `assertCoveredBy` runs it in your process. It is rendered by `UbKind`
  name in the text line, the JSON and a GitHub warning. Soundness codec 4.
- **`--mm:refc` is a compile error at `import nelli/symex`** (W1-c1b), naming
  the build field. Under refc nim-z3's `=destroy` hooks do not compile and the
  error used to name `z3/ast.nim`. Use `--mm:orc` or `arc`.
- **The build is read in one module** (W1-c1a, W1-c1b). `nelli/smt/buildprofile`
  owns the build reads (checks, panics, memory model, exceptions, backend) and
  `arithChecksFor`/`arithChecksDisagree`. `admitBuild` returns
  `Option[BuildRefusal]` keyed by a `BuildField` enum, which removes the
  `Admission` name clash with `nelli/coverage` (M4). The walker follows an
  in-source `push` as the build; nelli cannot tell a push from the command
  line, and a push-time import fails closed.
- **The arithmetic scope is decided once** (D1, R2-01). The walker kept the
  scope in a bool threadvar read raw at about ten sites, with a save and
  restore around routine bodies that nothing enforced. It is now a lexical
  stack read through `wraps()` and `checked()`, and the parser computes it
  through one pure function, `arithScopeFor`, with the build's checks folded
  into `overflowChecked` (R2-01). A refactor under green: no verdict or cache
  key moves and the walker is not bumped for it.
- **The symex README's decline catalogue is rewritten** around every `fe*`
  and `ub*` kind (W1-z, M2, M6). `scripts/check-readme-kinds.sh` derives the
  kinds from `SymexErrorKind` and fails if the README omits one; it runs on
  docs changes and has a negative self-test. The README states which `ub*`
  kinds can ride a witness (only `ubIndeterminateRead` does today).
- **Deprecation noise is scoped** (M3). The three module-wide
  `warning[Deprecated]` pushes in `types`, `canonicalize` and `runtime`, two
  of them never popped, are gone; internal reads of `arithChecks` go through
  one accessor. `symexFind` no longer initialises `SymexResult.fromCache`.
- **Remediation text names the right reason** for a witness that is not run in
  the host (`witnessUndefined`, a crash claim) rather than a replay, and the
  `feLocalPragma` message no longer cites a missing README heading.

### Added

- **`UbKind` and the `ub*` kinds** in `SymexErrorKind`: `ubUnsignedDivZero`,
  `ubIntMinModMinusOne`, `ubSignedOverflow`, `ubFloatToIntRange`,
  `ubIndeterminateRead`, `ubSignedDivZero`. `ubFloatToIntRange` is declared
  and has no emission site yet; float-to-int out of range stays
  `feConvFloatToIntUndefined`.
- **`feLocalPragma`, `feFloatWidth`**, and the `feCheckOption` and
  `feOverflowCheckOption` uses above.
- **`Soundness.witnessUndefined`, `undefinedKinds()`, `Path.undefined`,
  `ArithScope` (`asBuild`, `asChecked`)** on a routine body, and the
  `nelli/smt/buildprofile` module.
- **K1-0, the native-reproduction join** (`tests/tsymex_0016_k1lite.nim`,
  `tests/k1lite.nim`, `scripts/k1lite.sh`). It joins `pinRecords` against the
  seven §5.0 cell keys (W-01 to W-07) and fails, naming the W row, slice and
  key, when any lacks an exact or declined record from this build row. It runs
  on Linux only, on the c and cpp backends in two steps of the `symex-linux`
  leg, and on Z3 4.13.4 at release by hand. The native-pin helpers (K9a:
  `pinExact`, `pinDecline`, `pinCrash`, `skipCell`, `pinRecords`) classify
  Windows crashes by evidence and install a first-chance fault handler.
- **Tooling.** The Z3 4.13.4 dev image with `-i IMAGE` on `dt-bounded.sh` and
  `sweep.sh` (INF-05); `sweep.sh` records the libz3 version it ran; the
  `symex-linux` leg provisions the Nim artifact, Z3 5.1 and PCRE 8.45 (CI-A1)
  and runs on pushes to main; `sweep.sh` runs on the host and derives its list
  from the test task, keeping the output tail of each failing test (CI-A2);
  `fuzzer-msvc` runs the RFC-0016 walker tests under `vcc` (W1-m); the 0.9.1
  sweep baselines are published as release assets.
- **Tests** for each row above, among them
  `tsymex_0016_crb_macro_deprecation` (a `symexFind` call site is
  deprecation-clean) and `tsymex_0016_cr_zeroarg`.

### Deprecated

Both are removed in 0.10.0 (RFC-0016, INT-39). Nim's `deprecated` pragma takes
no message on an object field, so the warning reads "`arithChecks` is
deprecated" and the path forward is in the field's documentation and the
migration note.

- **`SymexSettings.arithChecks`**: do not set it. The build decides, through
  `--overflowChecks` and `--rangeChecks`. To model checks off, build with them
  off; the unchecked operations are then undefined and halt (`ub*`).
- **`SymexResult.fromCache`**: always `false`, since `symexFind` has no cache.
  The cache-hit flag is `SymexFinding.fromCache`, set by
  `symexFindAllWitnesses` and `symexForAll`.

### Known limitations

- **Designed declines, tracked as precision rows.** PRC-39 (W1-b): a
  `{.cursor.}` local declines `feLocalPragma`; the exact model is a non-owning
  alias of the source's storage. PRC-40 (W1-e): a `float32` <-> `float64`
  conversion declines `feFloatWidth`; the exact model rounds to binary32 and
  needs native pins at 0.5 and 0.1. PRC-38 (CR-A): a generic exception type
  such as `G[ValueError]` declines `eeUnknownExnType`; the exact model
  identifies the full instantiation. None blocks this release.
- **A fork replay inherits a routine `{.global.}`** (INT-40, found in review as
  SC1b, older than this release). A fork replay child inherits the host's
  current value, so after earlier host calls a walker `sxSat` through that
  global can be confirmed from run history, with no `runDependence`. Re-exec
  replay starts from the initial value and refutes it.
- **A `sxSat` is trusted on its prefix.** C's undefined behaviour is not
  sequenced and the walk stops at the first label hit, so a trusted `sxSat`
  can be defined up to the label and undefined after it. The tail is not
  scanned; the whole-run check is planned (K10b).
- **Destructors during panic unwinding are not modelled** (W1-c2). Under
  `--panics:on` a destructor's side effect between the raise and the exit is
  not walked.
- **Unsigned division in an opaque callee gives no answer** (W1-d1b, K10b): it
  is neither a raise nor a halt.
- **A checked routine calling an unchecked callee that overflows** declines
  `ubSignedOverflow` (W1-d2c).
- **The halted path records no `undefined` set** (W1-d3): the halt is visible
  as the path's absence.
- **On Windows a `{.global.}` named only from another routine** stays open under
  the re-exec replay, so such a SAT is not confirmed there (W1-m).
- **The native-reproduction join covers Linux only.** The mingw and MSVC rows
  are pinned by their suites but not joined (K1a-ci, K5a `rowOf`, Wave 2).
- **Open Lows from the review** (R2-03 to R2-08, R2-10, L9, SC3, D8) carry into
  Wave 2 under INT-42; the ledger is `docs/rfc/0016-review.md`.
- **`tsymex_rfc0005_s8by_remainder` is red on c and cpp** at the 0.9.1
  baseline: its spend-equality check (`r.units == base.units`) asserts Z3 spend
  that drifts within a process (INT-04, CI-03). It is unchanged by this release.
- **The deprecations above land in 0.10.0** (INT-39).

## [0.9.1] — 2026-11-04

This release carries two sets of fixes made after the 0.9.0 tag (RFC-0005):
the wiring audit (handoff entry "2026-11-03 — Wiring audit", WA-1 to WA-13)
and the multi-round code review of the same surface (`docs/rfc/0005-review.md`,
R1-01 to R1-35, review rounds 1 to 8). Review findings are cited as R<round>-nn
in the entries below, and by the finding id the review gave them where a round
re-reviewed an earlier fix. Upgrading: `docs/migration/0.9.1.md`. Three of the
wiring-audit fixes are regressions that 0.9.0 shipped against 0.8.0; they come
first. Then come the verdicts that were wrong on 0.8.0 as well, then the ones
wrong only in machinery 0.9.0 introduced.

### Fixed — regressions against 0.8.0

- **Seq `items`/`pairs` whose body changes the seq's length** (WA-3). Nim's
  `items` and `pairs` read the length once and assert it is unchanged after
  each step, so a body that grows or shrinks the seq ends the loop in
  `AssertionDefect`. The walk bounded the loop by the live length with no
  assert, so `for _ in s: discard s.pop()` was a clean false `sxSat` for a
  target after the loop and a clean false `sxUnsat` for one in `except
  AssertionDefect`. 0.8.0 gave `sxUnknown` there. Both iterators now use the
  length-assert model `mitems`/`mpairs` already had; in a module where
  `assert` may be compiled out the loop declines, as `mitems` does.
- **`symexFindAllWitnesses` and `symexForAll` see user exception types**
  (WA-1). They built their program without the user exception hierarchy that
  `symexFind` passes. 0.8.0 omitted it too, but 0.9.0 reads an exception type
  it does not know as ⊤ (`eeUnknownExnType`): a named `except` of a user type
  (or `RegexError`) was skipped, and a verdict `symexFind` decided came back
  `sfUnknown` where 0.8.0 gave `sfUnsat`. The cache key now covers the
  hierarchy (below), so a changed parent type is a new key.
- **A witness that ends its process after reaching the target is not run in
  the host** (WA-2). A replay that reached the target and then exited
  (`quit`, a raw `exit`), was signalled or ran past `replayTimeoutMs` was
  confirmed with nothing saying how it ended, and `assertCoveredBy`'s splat
  and `symexForAll`'s seeds then ran the same witness in the calling process,
  which it ended or hung. 0.8.0 replayed nothing and declined such a
  candidate. The claim still stands (the target is reached), but it now
  carries `Soundness.witnessUnsafe` and a `feReplayCrashed` or
  `feReplayTimedOut` hint saying how the child ended and on what input.
  `symexForAll` does not seed such a witness, cold or from the cache.
  `assertCoveredBy` never splats it: with no `testFn`, the confirming replay
  is the coverage and the check passes; with a `testFn`, or on an `sxRaised`
  claim (whose replay targeted the raise, not the check's target), the check
  fails with an `AssertionDefect` that says why.

### Fixed — wrong on 0.8.0 too

- **An inner `try` inside an `except` handler gave a false `sxSat`** (review
  round 3, T1; `157a578a`). A handler body is walked with the handler stack
  cut back to the `try` that caught the raise, so a `try` inside the handler
  had that outer `try`'s depth, and its claim on the caught entries (a filter
  on depth) took every caught entry at that depth, not only the ones its own
  body produced. When one `try` caught two raises from separate statements,
  the claim walked the earlier catch's continuation through the rest of the
  handler a second time. With `except ValueError: try: inc y; except
  CatchableError: discard; inc x`, a path ran `inc x` twice, and a target on
  `x == 2` (which native Nim never reaches, one handler run per path) was a
  clean false `sxSat`. The depth-filtered claim is the same code in 0.8.0 and
  0.9.0. A statement's exit entries are now identified by the serial they were
  parked with (`park`), and a `try` claims only the entries parked while it
  ran, so an inner `try` cannot take an older entry. The channels are their
  own internal module (`smt/exits.nim`), grouped by owner and bound to the
  walk's clock.
- **An `elif` condition's preamble ran before the whole `if`** (R1-01;
  `bfbc34e1`). A later condition's bounds fork, hoisted call or defect fork was
  appended ahead of the entire `if` (statement, value position and iterator
  body alike), so it ran on the paths that took an earlier branch. `if i >=
  s.len: symexTarget("past-end") elif s[i] == 3: discard` gave `sxRaised
  IndexDefect` on `s = @[]`, `i = 0`, reported `trusted()`, where native Nim
  reaches the label; a label target gave a false `sxRaised`, and `if a == 1:
  ... elif bump(s)` with a `var` seq gave a clean false `sxUnsat`. 0.8.0
  lowers `if` the same way. A condition with a preamble is now nested into the
  `else` of the arm before it, so the preamble runs only where that condition
  is tested.
- **`succ`, `pred`, `inc`, `dec`, `+=` and `-=` are checked against the
  operand's bounds** (R1-02; `00101ddb`, `0f89a68f`). `succ`/`pred` on an enum
  or `char`, and `inc`/`dec` on an enum or `char` variable, lowered to an
  unchecked sum, so a target on `OverflowDefect` was a clean false `sxUnsat`
  and a label behind the wrapped value a false `sxSat` (`succ('\xff')`).
  `inc`/`dec` and `+=`/`-=` on a range variable raised the assignment's
  `RangeDefect` where native Nim raises `OverflowDefect`. `succ`/`pred` check
  the base type (an enum's first and last ordinal, `char` 0..255; a range is
  checked against its base), `inc`/`dec`/`+=`/`-=` the variable's own type, a
  range included; both raise `OverflowDefect`. A type whose bounds are not
  read declines. 0.8.0 lowers `succ`/`pred` as plain `+`/`-`.
- **A finding from an earlier `assertCoveredBy` showed up in a later
  `symexForAll` report** (R1-10; `dd30ee50`). Findings went through a
  thread-local sink that only `symexForAll` drained, so findings made by an
  earlier call on the thread leaked into its report. The sink is removed
  (below); a finding belongs to the call that made it.
- **Float checks in an opaque callee** (WA-4). An inert `{.symexOpaque.}`
  callee's defect scan assumed the default checks. A callee compiled with
  `nanChecks` or `infChecks` on (by `push`, or `floatChecks`) raises
  `FloatInvalidOpDefect` or `FloatOverflowDefect` from float arithmetic, and
  neither was forked: a target in `except FloatingPointDefect` around the
  call was a clean false `sxUnsat`. The scan now reads each scanned routine's
  check options (`routineChecks`), the callee's and every routine it calls. A
  callee compiled with a check OFF now forks a `Defect` it cannot raise; that
  fork carries `feOpaqueEffectHavoc`, so a hit through it is replayed and
  refuted (`sxUnknown`), and an `sxUnsat` stands.
- **Argument order of a statement-position opaque call** (WA-5). The
  statement-position opaque and foreign arm, and the `{.symexTransparent.}`
  fallback beside it, parsed arguments one after another, so a later
  argument's call ran before an earlier argument was read: `opq(v div b,
  bump(b))` with `b == 0` divided by the bumped `b`, a clean false `sxSat`
  after the call and a clean false `sxUnsat` in `except DivByZeroDefect`.
  They now read arguments where Nim's C backend does (`parseOrderedArgs`),
  as the expression-position arm already did.
- **A deleted `{.symexTransparent.}` call keeps its arguments' checks.** A
  transparent call in statement position whose arguments are inert is
  deleted. Its arguments were parsed and their values thrown away, so a check
  an argument carries was never forked: `trv(v div b, 0)` with `b == 0` was a
  clean false `sxUnsat`. Each argument that is not a literal or a variable is
  now bound to a sink `let`, as `discard <expr>` is.
- **A cached `sfRaised` finding is the cold one** (WA-10). A `:raised` hit
  kept only its status and soundness: the `raised(<type>)` descriptor,
  `defectTypeId` and the witness were lost. The `:raised:<type>` sentinel now
  stores the witness and the defect-ness.
- **The no-targets finding carries `soundness`, `gaps` and
  `annotationViolations`** (WA-12), derived from the parse-time errors, as
  every other finding does.

### Fixed — wrong in 0.9.0, in machinery 0.8.0 did not have

- **PCRE's compile limits are modelled** (R1-03, R1-05, R1-22; `c9682ebc`,
  `9663105d`). The regex reader did not model what `pcre_compile` rejects, so
  a pattern native Nim raises `RegexError` on got a clean verdict: 300 nested
  groups gave `sxSat "a"` (trusted), `(?:[a-z]){1700}|b` gave `sxSat "b"`,
  and an `except RegexError` target gave `sxUnsat`. A group opened past
  `PARENS_NEST_LIMIT` (250) is now rejected with Nim's own message ("parentheses
  are too deeply nested") and offset, so the walk raises `RegexError` as native
  does (2600 nested groups no longer recurse the host). The reader also keeps a
  saturating upper bound on `pcre_compile`'s pre-pass length and its compile
  workspace: a pattern whose bound passes 65536 code units ("regular expression
  is too large") or nears the workspace limit ("too complicated") is declined
  as `sxUnknown`, never decided. That bound is an upper bound, so a pattern
  PCRE would accept but whose bound is past the limit declines too. Counted
  groups are checked at parse time, before the NFA expands them: a counted
  group nested three deep (`200` repeats at each level) took 33.6 s and peaked at 5.7 GB of the
  test host's memory before it declined through `maxSeqLen`. `codeSize` and
  `branchSize` now add and multiply with saturation (a large repeated group
  overflowed the code-unit count into an `OverflowDefect`). The reader's
  recursion is bounded by the nesting limit. The pattern families are pinned
  against `re()` in `tsymex_rfc0005_r1_pcrelimits`. Closes RFC-0016 CRH-04.
- **A variant construction's taint no longer lands on a sibling path**
  (R1-04; `222b78af`). A variant constructor's plain fields were lowered
  without draining the taint a decline queued (an unwritten global's
  `feGlobalHavoc`), so it landed on whichever lowering drained next, a sibling
  path or none. `if b > 3: let p = Pkt(opcode: op, tag: gN); if p.tag == 5:
  <label>` gave `sxSat` with `pathTaint = {}`, reported `trusted()`, where
  native Nim never reaches the label. Both raw lowering sites now lower through
  `lowerInExpr` on the path they bind. Structurally, the statement is the unit
  of the pending-taint discipline: any stray taint found queued, or still queued
  when the statement returns, goes on every path the statement yields,
  including the ones it sends down an exit channel (`return`, `break`,
  `continue`, a raise or `finally`). The caller's queue survives a nested
  walk, and the parameter set-up's queue is drained onto the initial path
  (`initialWalkPath`).
- **A variant field write the receiver has no slot for is a substitution**
  (R1-13; `69c2f0a1`). `lowerVariantFieldSet` kept the old value and went on
  without the write, recording the read arm's halt kind (`dcOmitted`, no taint).
  It now records `feUnsupportedOp` (`dcSubstituted`), as every other dropped
  write does. No program was found that reaches the write on a clean path, so
  no verdict is known to move.
- **Per-run walk state is reset** (R1-12; `08e40fc8`). `resetSymexRunState` did
  not clear `pendingPtrCompares`, so a run aborted between a pointer
  comparison and its drain left Z3 terms of the freed context for the next
  run. The same gap in eight more per-expression lowering threadvars
  (`closureEnvWrites`, `loweringReadNames`, `lastDrainedClosureExitPc`,
  `lowerAsReceiver`, `allocEnumZeroLegal`, `glUnwrittenCtx`, and the
  `seqConformCounter` and `strCharsCounter` counters) is closed. No abort
  shape that reaches it was constructed, so there is no test.

### Changed

- **Lossy clean winners are replayed** (WA-9). A clean winning path whose
  witness renders lossily (a `wfLossy` parameter shape, or a run whose
  extraction substituted a value, `feExtractionFailed`) was `trusted()`
  though nothing had run that witness. It is now replayed as the settle's one
  job. A confirmation makes it `rsConfirmed`; any other outcome, or
  `SymexSettings.replay = false`, leaves it `rsUnconfirmed` (new, below) with
  a hint, and its status stands. **This widens when `fn` runs at verdict
  time** (the S10 execution contract, 0.9.0 migration note §1.1): a clean
  `sxSat`/`sxRaised` with a lossy witness now executes `fn` once, in a child.
- **A run-dependent `:unk` is not cached** (WA-7). A replay left undecided
  for a reason of the run (a child killed at `replayTimeoutMs`, one ended at
  the replay's memory limit, or one that could not be started or handed its
  state at that moment, including a runtime hook the host had set) no longer
  stores a permanent `:unk`; the next run replays again. An `rsUnconfirmed`
  lossy winner left so for such a reason is not stored either.
- **The cache key gains two parts.** `|rm=<mode>` says how the build replays
  (`fork`, `reexec` or `none`, plus `+panics` under `--panics:on`), so a
  database shared across platforms or builds does not serve one build's
  `:unk` to another that would confirm (WA-8). `;uxh=[...]` in the program's
  canonical form keys the user exception hierarchy, and is absent when there
  is none (WA-1).
- **The soundness cache encoding is version 3**
  (`"3:<pathTaint>:<runTaint>:<replay>:<unsafe>"`, with an optional sixth
  field for `runDependence`; version 2 was the wiring audit's, version 1
  0.9.0's). `witnessUnsafe` is stored (WA-2), and from version 3 it also marks
  an unconfirmed witness whose replay ended its child (review R2, DD1). A
  version-1 or version-2 entry cannot say whether a stored witness is safe to
  run, so it is a miss. The fields are the enums' ordinals, which compile-time
  pins now fix; reordering a member, or a field past one digit, fails to
  compile and needs a new encoding version (review R3, E8).
- **Walker version 272** (264 in 0.9.0). The cache's key and value changed
  and the walker's exit handling changed (above), so every 0.9.0 cache entry
  is orphaned: a miss, then a cold run.
- **The cache key moves to `sx2:` plus SHA-256, and gains two more parts**
  (review R1-08, R1-09, R3 E10). The key was `sx:` plus a SHA-1 of its
  canonical form; it is now `sx2:` plus the SHA-256 of it (`symexCacheKeyPrefix`,
  the new internal module `nelli/smt/sha256`, which runs in the compile-time
  VM), so every SHA-1 key is a miss. `|bf=<flags>` (`buildFlagsSegment`) names
  the build flags that decide whether the native `fn` raises: the runtime
  checks compiled in (assertions and each check switch), `-d:danger`,
  `-d:release`, the memory model, the backend, `--exceptions`, `--threads`,
  `--stackTrace` and `--lineTrace`. Without it, a debug build's replay-confirmed
  raise could be served as trusted to a `-d:danger` build whose `fn` does not
  check. `;impl=<digest>` in the program's canonical form (`implDigest` on
  `SymexProgram`, `nelli/smt/impl_digest`) is a SHA-256 over the source of every
  user routine `fn` reaches natively, transitively, with the check options each
  was compiled under, absent when there is none. A cached `rsConfirmed`,
  `witnessUnsafe` or `:raised` record is a fact about the real `fn` and the
  callee bodies the IR holds only by name (`{.symexOpaque.}`,
  `{.symexTransparent.}`, a declined call); an edited callee body used to
  leave the key unchanged and serve the old run's trusted result. The digest
  is length-prefixed and counted, so two different bodies cannot collide by
  sliding a literal into the next node's kind. Not keyed, by design: the
  external body of an `importc` or `dynlib` routine (its name, signature and
  pragmas are), the overrides of a method `fn` calls (those the walk
  dispatches over are in the IR; their own callees are not followed), the
  target of a call through a proc value, and the compiler's `lib/` tree (the
  `nim=` segment moves with the toolchain).
- **Every cache entry macro keys a method-calling SUT as `symexFind` does**
  (R1-11; `b19ea30e`). `symexCacheKeyForFn`, `saveSymexWitness`,
  `loadSymexWitnesses`, `saveSymexVerdict` and `loadSymexVerdict` parsed
  without registering the SUT's methods, so for a SUT that calls a method they
  keyed the undispatched program wherever no other entry had registered the
  methods yet: a key `symexFindAllWitnesses` never writes, and one that
  depended on expansion order. Every entry macro now parses through one helper.
- **The `:raised` index is `:raised2`, and a raised-type save is
  all-or-nothing** (review rounds 6 to 8; `51d6a02b`, `29a60d5a`, `c0283f30`).
  A save writes an empty index first, then every per-type sentinel, then the
  real index, one entry listing every type id; the load needs every indexed
  sentinel and rejects an index that lists a type id twice. A save that fails
  part-way reads back as a miss, never as a partial set or a mix of old and
  new sentinels (a failure of the very first write leaves the previous
  complete set). The index moved to the new key `:raised2` because an old
  multi-type index did not parse as the new format and an old single-type
  one did, so every record written before is now a clean miss. Old `:raised`
  index entries are not removed. The guarantee is for one writer that crashes;
  concurrent writers to one directory database, or a power loss without
  fsync, can still interleave. `symexFindAllWitnesses` saves one type and
  loads the first, so it is unaffected. A verdict hit no longer reads the
  raised slot.
- **`Soundness.runDependence` replaces the run-dependence threadvars**
  (R1-07, `d8969822`; review rounds 5 and 6). Whether a verdict is this run's (a
  solve cut off by the wall clock, a call declined for want of native stack, a
  replay left undecided for a reason of the run) was three thread-local flags
  read at save time, so a public `saveSymexVerdict` after other work on the
  thread read another run's flags. It now rides the result as
  `Soundness.runDependence: set[RunDependence]` (`rdQueryTimeout`,
  `rdNativeStack`, `rdReplay`), set by `runSymex` and by the replay settle,
  and the save paths read the soundness they are handed. A child killed at its
  bound, or whose status was lost, is run-dependent by its ending.
  `Soundness.cacheable` is the one save-side rule: an `rsUnconfirmed` claim,
  or one with `witnessUnsafe`, whose `runDependence` has `rdReplay` is not
  stored, since a hit would run in the host a witness whose replay hung or
  lost its child on another host. The `:notes` record is saved only when its
  verdict was.
- **A replay's result is a value** (R1-06, R1-14; `d8969822`). A replay
  returns a `ReplayResult` (the outcome and the child's report) handed to the
  settle as an argument; the thread-local `replayDetail`, `replayEnding` and
  run-dependence flags, and their readers, are gone. `replayWitness` returns a
  `ReplayResult`: compare `.outcome`, not the result. The mapping from a
  child's ending to `ReplayStatus`, run-dependence and every `feReplay*` hint
  is in `nelli/smt/replayresult` (hint texts are unchanged). The zero value of
  `ReplayResult`, `ReplayOutcome` and the child's `ReplayEnding` is the replay
  that did not run (`roDeclined`, `reRefused`): never a confirmation, never
  host-safe (review round 3, E1). A child that started and whose exit status was
  lost (`reLost`: `SIGCHLD` ignored, or the status reaped by another wait)
  ended: a reach it wrote confirms, a miss is a crash, and the witness is
  never run in the host. It was reported as a refused replay before.
- **`witnessUnsafe` is set by any replay that does not finish** (review round 2,
  DD1, DD2). Whether a witness could run in the host was read off its
  `feReplay*` hints, which a cache hit rebuilds from the best-effort `:notes`
  record; with it missing, a witness whose replay ended its child ran in the
  host. A replay that does not finish now sets `witnessUnsafe` whether or not
  it confirmed, and it is stored with the verdict. One function decides:
  `hostRunnable(Soundness)` in `nelli/smt/soundness`, false for a
  `witnessUnsafe` or `rsUnsettled` claim and true otherwise (so an
  `rsUnconfirmed` witness is run, which is how a consumer learns whether it
  reaches the target).
- **`assertCoveredBy` decides on `trusted()`** (R1-15; `dd30ee50`). Reading
  `status` alone, it spliced an `rsUnconfirmed` lossy witness and blamed `testFn`
  when it missed. A trusted claim whose witness `testFn` misses still blames
  `testFn`. An untrusted one is run unless it is not `hostRunnable`; a hit
  proves coverage, a miss is reported as unconfirmed, as an `sxUnknown` is, and
  `acceptUnknownAsCovered` downgrades it. `symexForAll` seeds only
  `hostRunnable` witnesses.
- **Findings are returned by value, and `assertCoveredBy` returns its own**
  (R1-10; `dd30ee50`, `947bffea`). The thread-local `SymexFinding` sink is
  removed, as are `consumeSymexFindings` and the `symexFindings` variable.
  `assertCoveredBy` returns its call's `SymexFinding` (a `seq[SymexFinding]`,
  one per target, for the multi-target form), discardable; on failure it raises
  `SymexCoverageDefect`, a subtype of `AssertionDefect` (an `except
  AssertionDefect` still catches it), whose `findings` carries them. Inside a
  `forAll` the finding is also recorded on the run's engine frame
  (`recordSymexFinding`) and the engine moves the frame's findings onto
  `Report.symexFindings` when the run ends, passed or failed; a nested `forAll`'s
  findings reach the enclosing run when its frame is popped
  (`popEngineFrame`). Outside a `forAll` (a plain test body, a fuzz or concolic
  harness, a thread the property started) nothing is recorded and
  `droppedSymexFindings()` counts the drop; the return value and the defect
  are then the only channel. One entry is kept per `fn`, call site and target,
  in the order each was first made, and it is the most severe finding made
  under that key: a trusted coverage failure outranks an unconfirmed miss, which
  outranks an `sfUnknown`, which outranks a covered unconfirmed claim, which
  outranks a trusted covered one, with `sfNotApplicable` and `sfReplayMiss`
  lowest; among equals the latest wins. A later passing example or shrink
  candidate no longer hides an earlier failure.
- **A zero `Soundness` is untrusted** (R1-16; `d390f119`, `9e0c4c2b`).
  `ReplayStatus` gains `rsUnsettled` as its zero value, and neither
  `trusted()` arm trusts it, so a record whose producer forgot the field fails
  closed. A hand-built `SymexFinding(status: sfSat)` or `SymexResult` that
  left `soundness` at its default was `trusted()` before; it is not now.
  `runSymex` settles every verdict it ships that needs no replay (an `sxUnsat`,
  an `sxUnknown`, a winner on a path with no `scSpurious`); anything else
  leaves it unsettled until the replay pass settles it.
- **The replay child is bounded and its host half hardened** (R1-18 to R1-21,
  R1-23, R1-30; `c2e7751f`, `6d04387f`):
  - *Quadratic decode.* The child reported a hit one byte at a time and the
    host re-decoded the whole buffer as it grew, so a flooding child overran
    `replayTimeoutMs` and, with no timeout, grew memory without bound. The
    child now reports a hit and an allocation failure once; the host decodes
    incrementally as the report arrives (`ReportReader`), keeps nothing and caps
    it at `replayReportCap` (4096) bytes. A child that writes past the cap, or
    bytes that are not a report, is killed and read as timed out
    (run-dependent), with nothing it wrote trusted; its hint says that reason,
    not `replayTimeoutMs`. The bound is measured on the monotonic clock,
    decode included. The decoder parses the exit code itself and cannot raise
    (an uncaught parse leaked a descriptor and left a zombie).
  - *Wait status.* A child whose exit status is lost (`ECHILD`) was reported as
    exit 0, so a signalled child read as a clean exit; it is now `reLost`
    (above). `EINTR` is retried. A child, and its process group, is signalled
    only while it has not been waited for, so its pid cannot name another
    process. The POSIX re-exec path leads its own process group, handles
    `waitpid` returning -1 (it spun, then killed a possibly reused pid), and
    builds its environment before `fork` and `execve`s, with no `putEnv` in the
    child.
  - *Temp-file names.* The re-executed child's files had predictable names in
    the shared temp directory (a symlink or time-of-check race, or a forged
    report, was possible). They now live in a private directory (`mkdtemp`, or
    a random name `CreateDirectoryW` will not reuse), created exclusively
    (`O_EXCL|O_NOFOLLOW`, mode 0600; `CREATE_NEW`). The host reads the report
    through the descriptor it created it with, capped, and watches its size
    while the child runs. The child clamps the fiber stack size it is told, and
    the wire reader rejects negative or oversized lengths.
  - *Windows handle inheritance.* `CreateProcessW` ran with `bInheritHandles`
    true, handing every inheritable host handle to the child and the SUT. It now
    inherits only the NUL handle, through `PROC_THREAD_ATTRIBUTE_HANDLE_LIST` in
    a `STARTUPINFOEXW`. Cross-compiled; the Windows legs are the proof.
  - *Environment marker.* `NELLI_REPLAY_CHILD` came from the environment, so a
    stale marker the program merely inherited refused every replay (silent
    precision loss), and a `|` in the temp directory broke the spec so the
    child ran `main` and replayed recursively. The marker now carries a
    per-spawn nonce and the private directory, and the witness file starts with
    the same nonce and the site; a marker that matches no file is ignored. A real
    child removes the marker from its environment, and the Windows environment
    block drops an inherited copy instead of appending a second.
- **`SymexFinding` carries the bounds a verdict was decided under, and the
  renderers show them** (R1-17; `50ebce5b`, `b091aaeb`). See Added.
- `saveSymexWitnessImpl`, `saveSymexVerdictImpl` and `saveSymexRaisedImpl`
  return a `{.discardable.}` `bool`: true only when they wrote. A caller that
  ignored the result compiles as before. `saveSymexWitnessImpl` and
  `saveSymexRaisedImpl` skip a claim that is not `cacheable`.
- `symexCacheKey` gains a trailing `buildFlags = buildFlagsSegment()` after
  `replayMode`; pass it only to compute another build's key.
- `SymexResult.fromCache` is documented as always `false`: `symexFind` has
  no cache. The 0.9.0 migration note (§2) said otherwise. The cache-hit flag
  is `SymexFinding.fromCache`.
- `trustedSat` reads `rsUnconfirmed` as untrusted; `rsNotNeeded` keeps its
  0.9.0 meaning (trusted unless the path is `scSpurious`).

### Added

- **`SymexFinding.hints` and `SymexFinding.diagnostics`** (WA-6). `hints:
  seq[FindingHint]` holds every entry of the run's error list that `gaps`
  leaves out, the replay outcomes among them: `feReplayCrashed` names the
  input the real fn crashed on, and `feReplayDeclined` says why a replay did
  not run (the Windows guidance in the 0.9.0 migration note, §5a and §7, can
  now be followed through `symexForAll`). `diagnostics:
  seq[FindingDiagnostic]` holds the raises the run reached that did not
  decide the verdict, each with its witness. `symexFindAllWitnesses` and
  `assertCoveredBy` fill both, and a cache hit serves the cold run's, from a
  new `:notes` record.
- **Every report format renders them.** `ofText` (and `ofJunit`'s `<system-out>`, which carries the same
  text): a `hint <kind>: <msg>` line per hint and an `also raised
  <type>[ (defect)][: <msg>] witness=<n> choices` line per diagnostic, under
  the finding. `ofJson`: `"hints"` (`kind`, `severity`, `msg`) and
  `"diagnostics"` (`raisedTypeId`, `isDefect`, `raisedMsg`,
  `witnessChoiceCount`) arrays on every symex finding, `[]` when empty. A
  finding with neither renders as it did, apart from the bounds and soundness
  fields below.
  `ofGithubAnnotation`: a `::notice title=symex hint::` line per hint.
- **`Soundness.witnessUnsafe: bool`** (WA-2): a replay of the claim's witness
  did not finish. On an `rsConfirmed` claim the child reached the target
  first; on an `rsUnconfirmed` one it ended before it (review round 2, DD1).
  Only a replay sets it.
- **`ReplayStatus.rsUnsettled`** (R1-16), the first member, so the zero value:
  no producer settled the record, and it is never trusted. Ordinals move
  (`rsNotNeeded` 0 to 1, `rsConfirmed` 1 to 2); an exhaustive `case` needs an
  arm.
- **`ReplayStatus.rsUnconfirmed`** (WA-9), tail-appended: a clean winner with
  a lossy witness that no replay confirmed. Not `trusted()`. An exhaustive
  `case` over `ReplayStatus` needs an arm.
- New exports, by module:
  - `nelli/engine/types` (so `import nelli`; `nelli/symex` re-exports only
    `SymexFinding`, `SymexFindingStatus`, `FindingGap` and `trusted` from
    it): `FindingHint` (`kind`, `severity`, `msg`, as strings) and
    `FindingDiagnostic` (`raisedTypeId`, `isDefect`, `raisedMsg`,
    `witnessChoices`).
  - `nelli/symex`: `CachedNotes`, `saveSymexNotesImpl` and
    `loadSymexNotesImpl` (the `:notes` record). `CachedRaised` gains a third
    field, `choices` (the stored witness), and `saveSymexRaisedImpl` an
    optional trailing `witnesses`. Neither breaks a call; a positional
    unpack of `CachedRaised` into two names does.
  - `nelli/smt/canonicalize` (import directly): `replayModeSegment`, and
    `symexCacheKey` gains a trailing `replayMode = replayModeSegment()`.
  - `nelli/smt/replayproc` (import directly): `refusedHostHook`;
    `ReplayChild` gains `outOfMemory` and `runDependent`. Review rounds
    added `reLost` to `ReplayEnding` and put `reRefused` first, and
    `replayReportCap`.
- **`SymexFinding.bounds: ResourceBudget`** (R1-17): the budget the verdict was
  decided under, since an `sfUnsat` is a proof only within it and an
  `sfUnknown` may be one a larger budget decides. A cold finding carries the
  run's echo and a cache hit the budget its key was derived from.
  `ResourceBudget` moved to the Z3-free leaf `nelli/smt/budget` (re-exported by
  `nelli/smt/types` and `nelli/engine/types`, so `import nelli` sees it). The
  renderers show it: `ofText` and `ofJunit` a `bounds <field>=<value> ...`
  line under every finding except `sfNotApplicable` and `sfReplayMiss`; `ofJson`
  a `"bounds"` object with the budget's field names, on the same findings;
  `ofGithubAnnotation` a `::notice title=symex bounds::` line for an `sfUnsat`
  ("sfUnsat within ..."). The soundness rendering now also shows what no
  renderer showed: `witnessUnsafe` and `runDependence` in the text head, a
  `"witnessUnsafe"` boolean and a `"runDependence"` array of member names in the
  JSON `"soundness"` object, and a `::warning title=symex witness unsafe::` line
  for a witness that is not run in the host.
- **`Soundness.runDependence: set[RunDependence]`** and
  **`RunDependence`** (`rdQueryTimeout`, `rdNativeStack`, `rdReplay`) in
  `nelli/smt/soundness` (R1-07). Verdict-neutral: `trusted()` does not read it.
  Stored as an optional sixth field of the soundness encoding.
- **`ReplayResult`**, a value type in the new `nelli/smt/replayresult` with
  private fields (R1-06, review round 2, DD6): built only by `replayNotRun()`
  and `replayResultOf(child, lossy)`, read through `outcome`, `child`, `detail`
  and `runDependence` (`nelli/symex` exports the type and those four).
  `ReplayOutcome` moved from `nelli/symex` to that module, still exported by
  `nelli/symex`, with `roDeclined` now its first member (zero); the other
  members' ordinals each move up one.
- **`hostRunnable(Soundness): bool`** and **`Soundness.cacheable`** in
  `nelli/smt/soundness` (above).
- **`SymexCoverageDefect`** (`nelli/symex`; an `AssertionDefect`, with
  `findings: seq[SymexFinding]`), and the return values of `assertCoveredBy`
  (above).
- **`nelli/engine/frame`**: `FindingOrigin` (`site`, `fnId`),
  `recordSymexFinding(origin, f)`, `pushEngineFrame()` and `popEngineFrame()`
  (`withEngineFrame` now uses them, and `EngineFrame` gains a `symexFindings`
  table), `droppedSymexFindings()` and `resetDroppedSymexFindings()`.
  `droppedSymexFindings` is per thread and only grows, so a test that reads it
  resets it first. The fn identity in `FindingOrigin.fnId` is the routine's
  name and body hash (`routineKey`) and its type.
- **`nelli/smt/canonicalize`**: `symexCacheKeyPrefix` (`"sx2:"`),
  `buildFlagsSegment` (and `buildChecksOn`, `buildMemModel`, `buildBackend`,
  `buildExceptions`, the build-time values it defaults to).

### Removed

- **`consumeSymexFindings`, the thread-local `symexFindings` variable and
  `recordSymexFinding(f)`** (`nelli/engine/types`, so `import nelli`). Findings
  are returned by value or carried by `SymexCoverageDefect` (R1-10). Use
  `assertCoveredBy`'s return value; inside a `forAll` they arrive on
  `Report.symexFindings`. `recordSymexFinding` is back as the two-argument form
  above.
- **`lastReplayDetail`** (`nelli/smt/replayproc`) and **`symexQueryTimedOut`**
  and **`symexNativeStackCut`** (`nelli/smt/runtime`): replaced by
  `ReplayResult.detail` and `Soundness.runDependence`. All three were exported
  for the symex entry macros, not for callers.
- The wiring audit's `lastReplayEnding`, `resetReplayRunDependence` and
  `replayRunDependent`, which were never in a release.

### Known limitations

- **macOS and musl report exit code 0 in a replay hint.** Where libc has no
  `on_exit`, the forked child's exit hook is `atexit`, which is not told the
  status, so a `feReplayCrashed` hint reads "exited the process with code 0"
  for any `quit(n)` or C `exit(n)`. The ending and every verdict are right;
  only the code in the message is not. Linux with glibc, and the re-executed
  child (Windows, `-d:nelliReplayReexec`), report the real code.
- The review's Low findings that stay open (R1-24 to R1-29, R1-31 to R1-34:
  grandchildren the SUT starts that outlive a child that ends by itself, the
  unread `annotationViolations` on the fuzzer path, no memory cap on macOS or
  BSD, among them) are marked open in `docs/rfc/0005-review.md`.
- The others are tracked in `docs/rfc/0016-native-parity-hardening.md` §5.8
  (INT-22 to INT-27). Two to know about: a clean, faithful winner (one
  nothing replays) that crashes after its target still runs in the host
  through `assertCoveredBy`/`symexForAll`, as on 0.8.0; and under
  `--panics:on` every lossy winner is `rsUnconfirmed`, because nothing
  replays there.

## [0.9.0] — 2026-11-03

RFC-0005, soundness channels. Each symex result now says how far to trust it:
a decline costs only the paths that reach it, an answer the analysis could not
model is checked by running the SUT, and what remains untrusted names its
cause.

Upgrading: `docs/migration/0.9.0.md`. **Read its §1 before you upgrade.** The
symex entry points can now execute your SUT, and that SUT must link and load.
Neither change produces a compile error. Open gaps, including where Windows
answers less than Linux and macOS, are in its §7.

### Changed

- **`fn` is executed at verdict time** (RFC-0005 S10). A witness on a path
  through something the analysis could not model is replayed by calling `fn`
  on it, and it is reported `sxSat`/`sxRaised` only if the real run reaches
  the target. The SUT's side effects happen for real, in a child process
  (below): effects outside it, such as files and sockets, are not undone.
- **`fn` must link and load** into the calling binary when replay is on. An
  undefined `importc` fails the link, and a missing `dynlib` (e.g. PCRE1 for
  `std/re`) fails at start-up. To opt out, set `SymexSettings.replay = false`
  (cache key `;rp=off`).
- **Every replay runs in a child process** (RFC-0005 S8ct), so nothing a
  replay does can end or corrupt the calling process: a `quit`, a raw C
  `exit`, a nil dereference, unbounded recursion or a runaway allocation used
  to end the whole test binary.
  - POSIX forks the child. Windows re-executes the program and hands the child
    the witness and the variables the SUT reaches; what cannot be handed over
    declines (`feReplayDeclined`, message `replay not marshallable: ...`), so
    the same SUT can be `sxUnknown` on Windows and decided on Linux or macOS.
    The shapes are listed in the migration note, §5a.
  - A replay's effects, stdout and stderr stay in the child. Use
    `replayExecutions()` to observe whether a replay ran.
  - A child that ends before reaching the target is `feReplayCrashed`, a hint
    on an `sxUnknown`, never a refutation. `replayTimeoutMs` kills the child.
  - `runReplayBounded`, `replayStackSize`, `replayAbandonedLive`, `ReplayRun`,
    `rrEnded`, `rrContended`, `roContended`, `ptrAimsSnapshot` and
    `ptrAimsAdopt` are removed.
- **Routines compiled with other runtime checks decline** (RFC-0005 S8cu). A
  routine compiled with `fieldChecks`, `overflowChecks`, `rangeChecks`,
  `boundChecks`, `objChecks` or `checks` off, or with `floatChecks`,
  `nanChecks` or `infChecks` on (by `push`, a pragma statement, the command
  line or `-d:danger`), gives `sxUnknown` with `feCheckOption` or
  `feOverflowCheckOption` on the paths that reach it. 0.8.0 gave the checked
  verdict, including raises that never happen. The rule, its spellings and its
  limits are in the migration note, §5.
- **A nil dereference is a crash finding** (RFC-0005 S8cu): an
  `sxRaised NilAccessDefect` at the SUT boundary, whatever `except` or
  `finally` encloses it, as Nim 2.2.10 runs it. In a `--exceptions:setjmp`
  build it declines under a `try` (`heNilDerefMayBeCaught`).
- **Declines are kinded and scoped.** 37 `SymexErrorKind` members are new
  since 0.8.0, each with the `DegradeClass` that names its lever; they are
  listed by class in the migration note, §3.3. A `SymexErrorInfo` built by
  hand needs a `scope` (§1.4).
- **Verdicts are more precise** (RFC-0005).
  - An over-taint-only run proves `sxUnsat`.
  - The blanket decline vetoes are gone, and unreached declines are
    `sevHint`.
  - Many previously declined Nim shapes are modelled.
  - Several Nim-unfaithful semantics are corrected, including float→int,
    `low(T)` negation/`div`, `mod`, slices and `finally`/`defer`.
  - Each moved verdict is listed in the migration note, §4–§5.
- **The cache helpers carry soundness.** `saveSymexVerdict(Impl)` takes a
  `Soundness`. `loadSymexVerdict(Impl)` returns `Option[CachedVerdict]`, and
  `loadSymexWitnesses(Impl)` returns `seq[CachedWitness]`. A custom
  `ExampleDatabase` used with the symex cache must implement
  `saveWithMetaImpl`/`loadPrimaryWithMetaImpl`.
- `RawResult.pathTaint` → `RawResult.soundness.pathTaint`.
- `ResourceBudget.maxBytesEncodingLen` and
  `SymexErrorKind.heRefVariantUnsupported` are removed.
- The walker version bump invalidates every symex cache entry.

### Added

- **`Soundness`** (`pathTaint`, `runTaint`, `replay: ReplayStatus`) on
  `SymexResult` and `SymexFinding` (RFC-0005 S11).
- **`trusted(r)`**: the one predicate to branch on, for results and
  findings.
- **`gaps(r)`**: each cause behind an untrusted result, with the
  `DegradeClass` that names its lever. `SymexFinding.gaps` carries it as
  `FindingGap`s.
- **`SymexResult.bounds`**: the `ResourceBudget` the run used, so an
  `sxUnsat` states the bounds it is a proof under.
- **The annotation-violation channel**: `annotationViolations` on
  `SymexResult` and `SymexFinding` reports a false `{.symexTransparent.}`
  promise without changing the verdict.
- **Symex findings in every report format**:
  - `ofText`: a `[symex]` section;
  - `ofJson`: `symexFindings`;
  - `ofJunit`: `<system-out>`;
  - `ofGithubAnnotation`: an `::error` per violation and a `::warning` per
    untrusted finding.

  Output is unchanged when there are no findings.
- `ResourceBudget.maxSeqLen` and `seqQueryRLimit`, along with
  `symexLoopIterations`, `loopPruneRLimit` and `defaultLoopPruneRLimit`.
- New `SymexErrorKind` members, all tail-appended. They are listed in the
  migration note, §3.3.

## [0.8.0] — 2026-09-08

Upgrading: `docs/migration/0.8.0.md`. **Read it before you upgrade** — this
release changes what existing code *means* without breaking any build, so
neither the compiler nor the version number can tell you which of your call
sites moved.

### Changed

- **A partial object literal now carries its type's defaults.** This is the
  headline and it is a *silent* behaviour change: every literal that compiled
  before compiles after, and means something different. Nim zero-fills the
  fields an object literal does not list, and nelli's configuration objects
  carry meaningful non-zero defaults — so the documented idiom shipped a
  different engine than `defaultSettings()`, with no warning, no error and no
  symptom except worse testing. `Settings`, `SymexSettings`, `ResourceBudget`,
  `BmcSettings`, `IntegerBiasConfig` and `OrchestratorPolicy` now declare their
  defaults on the fields, so `T()` **is** the documented default configuration
  and a partial literal differs from it only in what it lists.

  An explicitly-written zero still means zero. That is what makes this
  mechanism viable where every sentinel and merge scheme failed:
  `maxShrinks: 0` (unbounded), `targetedSAIters: 0` (SA off) and
  `useSA: false` all keep saying what they look like they say.

  **Read `docs/migration/0.8.0.md` before upgrading.** It carries the per-field delta tables, runnable greps and a
  triage recipe. The short version: if you meant the zeros, write them
  explicitly *before* you upgrade.

  The sharpest instances, for calibration:
  - `Settings(maxExamples: 7, seed: 42)` — the README's own example — left
    `maxRejections` at 0, and the first rejection ended the run as
    `otExhausted`. Any filtered or `assume`-using property reported exhaustion
    after about two examples, on a property that holds.
  - The symex suite's ten `const SymexSettings(...)` literals left
    `arithChecks` empty, so no arithmetic defect fork was emitted at all and
    `OverflowDefect`/`DivByZeroDefect`/`RangeDefect` were unreachable.
  - `BmcSettings(maxDepth: 5)` — the idiom `bmc.nim`'s own doc comment
    recommended — left `maxStates` at 0 and returned `bmcExhaustedBudget`
    before expanding a single state.

- **`0` now means unlimited on both `BmcSettings` caps.** It previously meant
  "stop immediately", which is the worst available reading of a value a caller
  might deliberately write. This matches the convention `ResourceBudget`
  documents — a convention the stage-4 review then found `ResourceBudget`
  itself did not keep; see below.

- **`ResourceBudget`'s "0 = unlimited for every field" was false for four
  fields**, and is now true for two more of them. `maxClosureInlineCount` and
  `maxBytesEncodingLen` were missing the `cap > 0 and` guard their siblings
  had, so an explicit `0` exhausted the budget on the *first* use and degraded
  the run to `sxUnknown` — the opposite of what the type promised, and of what
  this release's own migration notes said you could rely on. Both now
  honour `0`.

  Three fields are documented exceptions where `0` does **not** mean
  unlimited. `maxCallDepth` is the one to know about: its check is ordinary
  *native* recursion in the walker, so removing the cap does not widen the
  search, it removes the only thing between the walker and the host stack —
  `maxCallDepth: 0` segfaults on ordinary linear recursion. It exhausts
  immediately by design. Do not assume a large round number is safe either;
  the ceiling bounds native stack depth and was measured near 85 on one
  build, so `maxCallDepth: 1000` crashes. `maxLoopUnwind` (`>= 1`, a
  decidability bound) and `seqInlineThreshold` (a strategy selector, where 0
  means the opposite of unlimited) are the other two. Full table in
  `docs/migration/0.8.0.md`.

- **An explicitly all-zero `IntegerBiasConfig` is honoured rather than
  rescued.** It was a sentinel for "use the library default"; it now means an
  unbiased uniform draw. Only affects callers who wrote the zeros on purpose.

### Deprecated

Warnings, not errors; all removed at the next major.

- `withSymexSettings` — write the `SymexSettings(...)` literal.
- `` `+` `` on `SymexSettings` and `ResourceBudget` — set the field on the base
  value. These had no production callers.
- `resolved()` — now the identity function.
- `orchestratorPolicy()` — write the `OrchestratorPolicy(...)` literal.
- `optimisedSymexSettings()` — byte-identical to `defaultSymexSettings()` since
  the Phase-2 endpoint; its doc comment claimed otherwise until now.
- `looseSymexSettings()` — use the new `looseSymexSettingsPreset` **const**,
  which carries the identical value. This RFC argues against preset *procs*
  as a second construction path beside the literal, and the library was not
  following its own prescription. A rename was unavoidable regardless: Nim
  does not allow a `const` and a `proc` to share an identifier.

`defaultSettings()`, `defaultSymexSettings()`, `defaultResourceBudget()` and
`defaultIntegerBias` are deliberately **not** deprecated yet. Deprecating them
in the same release that already changes what every partial literal means would
be two migrations at once.

### Fixed

- **`given x in <a Strategy type alias>` now fails with a message that names
  the mistake.** `type MyStrat = Strategy[int]` followed by `given x in
  MyStrat` is a typedesc, so the round-D sugar expanded it to
  `arbitrary(Strategy[int])` and the user got "cannot derive a strategy for
  `Strategy[int]`" — advice to write `newStrategy(...)` when the real error
  was passing a strategy TYPE where a strategy VALUE was meant.
- **`ResourceLimits.stdoutBytes` is marked NOT ENFORCED.** It is declared, and
  `FUZZ_PLAN.md`'s D16 describes it as applied via `setrlimit`, but nothing
  reads it — while its siblings `addressSpaceBytes` and `cpuSeconds` genuinely
  are applied. Setting it does nothing and reports no error. Documented rather
  than removed, since the capability is still wanted.

- **`examples/symex_loops.nim` had not compiled since CR-9(b)** moved the
  resource caps onto a `budget` sub-object, and **`examples/symex_oob.nim`
  compiled but failed at runtime** — Phase 15 made an out-of-bounds access a
  raise path, so `tIndexError` yields `sxRaised`/`raisedWitness`, not
  `sxSat`/`witness`. The README's own symex snippet had the same CR-9(b)
  breakage. Nothing compiled `examples/`, and compiling is not running.
- **`validateSymexSettings` is now called.** It was exported, unit-tested and
  invoked by nothing in `src/`. Its "arithChecks is empty" warning is exactly
  the defect above; it now runs at macro time, at zero runtime cost, on every
  entry macro that walks a SUT under caller-chosen settings — `symexFind`,
  `assertCoveredBy`, `concolicCollect`, `concolicFlip`, and
  `symexFindAllWitnesses` (and, transitively, `symexForAll`). A follow-up
  review found the first cut wired only `symexFind`/`assertCoveredBy`, so
  the identical `arithChecks: {}` literal warned there but not on
  `concolicCollect`; all five now share one internal chokepoint so a future
  entry macro gets the check by construction rather than by a call site
  someone remembers to add.
- **`arbitrary`'s "cannot derive" error now says what to do.** It named the
  type and stopped. It now lists what derivation covers, notes that a
  supported-looking type may simply have an unreachable definition, and gives
  the three escape hatches (`newStrategy`, `map`, or defining an `arbitrary`
  overload that every containing type then picks up).
- **Four registered-nowhere symex suites** (`tsymex_phase13_rlimit`,
  `_layer1_wire`, `_acceptunknown_guard`, `_unknown_roundtrip`) are registered
  in `nelli.nimble`, so they run in the sweep and in the `symex-mingw` corpus
  it derives.

### Added

- **`given x in int`** — a `given` binding may name a type instead of a
  strategy, and derives it via `arbitrary`. Mixed bindings work unchanged:
  `given a in int, b in integers(0, 10), c in bool`. (The obvious spelling
  `given x: int` is not the one that landed: the colon produces a different
  AST shape from the `in` infix the parser requires, and `given x: int, y in
  ys` does not parse as intended at all, because the colon swallows the
  remainder.)
- `scripts/sweep.sh` and `scripts/sweep-diff.sh` — a whole-suite parallel
  sweep and a baseline diff. There was previously no command that ran the
  whole suite: `psweep.sh` covers only `tsymex_*`, and `nimble test` is a
  serial loop that includes suites which hang on Linux. The sweep also reports
  registry drift; 92 test files on disk are registered in neither
  `nelli.nimble` nor any CI leg.
- `scripts/check-examples.sh`, plus an examples build step on the
  `symex-mingw` leg. Adding examples to `nimble test` would have bought zero
  CI coverage, because nothing in CI runs that task.

## [0.7.0] — 2026-08-29

Upgrading: `docs/migration/0.7.0.md`.

### Fixed

- **`import nelli` no longer reaches Z3.** v0.6.0's Track-G C4 wiring made
  `fuzzmacro` auto-build a real concolic bridge for every caller, which forced
  `import ./symex` into core and pulled Z3 into the base import surface. That
  silently broke a contract `README.md` documents and `tests/tsmoke.nim`
  asserts — and `tsmoke` sat red for a whole release because no workflow ran
  it. Both the property and its CI pin are restored: a compile-only probe
  (`tests/tz3free_probe.nim`) now runs on both Windows fuzzer legs with every
  config source skipped and the nimblepath withheld, and `tsmoke` runs as a
  named step alongside it.

### Added

- **`nelli/concolic`** — the opt-in door for concolic-assisted fuzzing, and
  the only module in the fuzz stack that imports the walker.
  - `fuzzConcolic(strategy, property, settings)` — the documented default
    form. It names the strategy and property once and generates both uses, so
    the pair the campaign draws from and the pair the assist solves for cannot
    diverge.
  - `concolicAssist(strategy, property, stallRounds = 1, maxBranchAttempts = 8)`
    — builds the assist as a value, for composition.
  - `guardSolverUnavailable` — see *missing libz3* below.
- **`ConcolicAssist`** (in `nelli/fuzz`, Z3-free): a bridge plus the
  activation policy that fires it, as one value.
- **Graceful degradation when `libz3` cannot be loaded.** Previously a failed
  lazy load aborted the entire campaign — an optional feature killing the
  whole run. The assist now catches `SoftlinkError` (and only that; a solver
  that computes something *wrong* still raises), latches so a broken load is
  not retried every stall round, and reports the new `cfoSolverUnavailable`
  outcome while the campaign completes on ordinary mutation.
- **`ConcolicAssistError`** — raised at campaign start for a hand-built
  `ConcolicAssist` that names an activation policy but carries no bridge.

### Changed

- **BREAKING: `import nelli` no longer re-exports `nelli/symex`.** Concolic
  fuzzing needs `import nelli/concolic`; symbolic execution needs
  `import nelli/symex`. Forgetting the import is a compile error, never a
  silent no-op.
- **BREAKING: `GuidanceConfig.stallRounds` and
  `GuidanceConfig.concolicMaxBranchAttempts` are removed.** They were a fossil
  of auto-wiring: while core built a bridge for everyone, bridge presence
  carried no user intent, so a second knob had to. That made either-key
  omission a silent no-op. The policy now travels with the assist, and
  `stallRounds` defaults to the *active* value.
  - Migration: `fuzz(s, p, FuzzSettings(guidance: GuidanceConfig(stallRounds: 1)))`
    → `fuzzConcolic(s, p, FuzzSettings())`. The old spelling is a compile
    error naming the missing field, which is a better diagnostic than any
    runtime warning.
- **BREAKING: `fuzz`'s `concolicBridge` parameter is now `assist: ConcolicAssist`.**
  Affects direct `proc fuzz*[T]` callers only.
  - Migration: `concolicBridge = b` → `assist = ConcolicAssist(bridge: b, stallRounds: 1)`.
- **A non-nil bridge with `stallRounds <= 0` is now coerced active, not
  inert.** Assist present ⇒ assist active; "off" is spelled by passing no
  assist. This inverts the old "opt-in required" behavior *at the `fuzz` entry
  points only* — the raw `newOrchestrator` seam deliberately keeps
  `concolicBridge` and `OrchestratorPolicy.stallRounds` as independent knobs,
  where "bridge configured, `stallRounds` 0 ⇒ inert" remains the contract.
- `symexTarget` / `symexAssert` / `symexAssume` and the `assertCoveredBy`
  capture cluster moved to `nelli/engine/markers`, reachable from bare
  `import nelli`. **No migration needed** in either direction: they resolve
  under `import nelli` and are still re-exported by `nelli/symex`. This is
  what keeps marker-annotated production code compiling without a solver in
  its build.
- `docs/fuzz/INTERFACE.md` is now checked by `tests/tfuzzpackaging.nim`
  instead of being normative by convention. It had drifted.
- The package version is pinned across all three of its sites
  (`nelli.nimble`, `milpa.kdl`, `nelliVersion`), which had drifted to
  0.6.0 / 0.4.0 / 0.1.0.

## [0.6.0] — 2026-08-28

Reconstructed from the release commit (`1f50752`) because chapulin has not yet
migrated across it and 0.7.0 compounds it.

### Added

- RFC-fuzzer-nextgen: the isolated-executor track (process/fork workers, the
  centralized orchestrator, lifecycle and circuit breakers), the coverage and
  cmplog shared-memory transports, the scheduling track (Entropic power
  schedule, UCB1 operator bandit, havoc stacking, corpus culling,
  checkpointing), and the concolic-assist track.

### Changed

- **BREAKING: `FuzzSettings` was regrouped (ADR-0031).** The guided-fuzzing
  knobs moved from the flat settings object onto three nested config objects —
  `ExecutorConfig`, `GuidanceConfig`, `SchedulingConfig`. The core fields
  (`maxIterations`, `database`, `persistKey`, …) stay flat.
