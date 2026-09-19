# Issue #163 — an opaque call ahead of the target must not cost the answer

Issue-scoped handoff (not an RFC; no `docs/rfc/NNNN` number). Newest entries
at the BOTTOM.

- **Branch:** `rfc-161-163-symex-defects` — the combined branch, created at
  the same sha as `rfc-163-opaque-call-taint` once it became clear the three
  issue branches were ALREADY cumulative (each was cut from the previous
  one's tip, so `main` is an ancestor and all 22 commits sit in one linear
  line; nothing needed merging, only a name that says so). The three
  per-issue branch names remain as markers. Still `rfc-*` deliberately — the
  three Windows legs trigger on `[main, 'rfc-*']`.
- **Consequence of the stack:** #161 and #162 can no longer be evaluated
  independently. The walker version is cumulative (125→132 across the three)
  and #162 retires a trip-wire #161 deliberately planted, so gates and audits
  are scoped to the COMBINED surface.
- **Base:** `ac507c1` (the tip of #162). The stack is incidental, not
  semantic: #163 touches the opaque-call arm and the pragma plumbing, which
  #161/#162 never went near. It is stacked only because #162 has not
  fast-forwarded to `main` yet.
- **Issue:** #163.
- **Test file:** `tests/tsymex_163_opaque_transparent.nim`.

## The defect

`walk`'s `#137` opaque-call arm (`runtime.nim`, `if stmt.opaque:`) did two
things unconditionally: set `w.sawUnknown = true` and continued every path via
`forkPathTainted`. So any target reached *after* an opaque call degraded the
whole run to `sxUnknown`.

Reproduced at `ac507c1` (`scratchpad/bench/probe_163_opaque.nim`, gitignored):

| SUT | `tRaisedExn` | `tLabel` |
|---|---|---|
| `plain` | `sxRaised` | `sxSat` |
| `withEcho` (echo *before* the branch) | `sxUnknown` | `sxUnknown` |
| `echoAfter` (echo *after* the branch) | `sxRaised` | — |
| `covered` (`{.cover.}`) | `sxUnknown` | **`sxSat`** |
| `callsCovered` (plain proc calling a `{.cover.}`'d one) | `sxUnknown` | — |

The `covered`/`tLabel` cell is the one the issue predicted as `sxUnknown` and
which measured `sxSat`. It is not a discrepancy, it is the mechanism in plain
view: `{.cover.}` injects `recordEdge` *inside each branch arm*, so the
fall-through path (no `else` arm to instrument) reaches the trailing label
untainted, while the raise path — which goes through the instrumented `if`
arm — does not. `withEcho` degrades both queries because `echo` sits ahead of
every path.

Every `sxUnknown` carried exactly one error: `weInternalWalkerFault`,
"sxUnknown produced with no classified reason". That is the Invariant-7
backstop firing, i.e. the walker reporting *its own bug* for an ordinary
unmodelled call.

## Two problems, deliberately kept separate

1. **The taint is too coarse.** Correct for an opaque call whose result is
   used or that can mutate state the SUT reads. Wrong for a void call taking
   only values — `recordEdge(id)`, `logCmp(lhs, rhs, op)`, `echo "x"`.
2. **The degrade is unclassified.** Even where the taint is right, the user
   should learn *which call* cost them the answer.

## Design decision — `{.symexTransparent.}` is a promise, not a heuristic

`{.symexOpaque.}` says "do not enter this body". It buys that with a path
taint, which is the right price for `readSensor()` and the wrong price for
`recordEdge(id)`. `{.symexTransparent.}` says the stronger and, for
instrumentation, *true* thing: the call is void, takes only values, and
touches nothing the SUT can read back — so symex deletes it.

Three judgement calls worth recording:

- **Statement position only.** The parser honours the pragma where Nim's own
  typing already guarantees there is no value to drop. A
  `{.symexTransparent.}` proc whose result *is* used reaches the expression
  arm, which gives it `{.symexOpaque.}` handling instead. An over-claimed
  pragma therefore costs precision, never soundness — and the half of the
  opaque contract it still earns (body not walked) is the half that keeps the
  G3fix `KeyError` closed.
- **Arguments are still parsed**, into the preamble; only their values are
  discarded. The pragma is a promise about the *callee*, not about the
  expressions at the call site: Nim evaluates those regardless, so dropping
  them unparsed would silently delete any effect they carry, and any honest
  degrade an unmodellable argument owes. Both instrumentation shapes parse to
  nothing but a value, so the preamble stays empty in the motivating case.
- **`recordEdge`/`logCmp` were RETAGGED, not double-tagged.** Carrying both
  pragmas would have been a hedge with no owner ("which wins?"). The G3fix
  pin (`tests/tsymex_g3fix_walkergap.nim`) is the safety net that proves no
  route regressed to walking their bodies: it still passes.

## Slice status

| # | Slice | Commit | Nature |
|---|---|---|---|
| 1 | `{.symexTransparent.}`; parser drops the call; instrumentation retagged | `b859b4a` | fix |
| 2 | pin `{.covercmp.}`, `{.cover, covercmp.}`, instrumented-callee | `4c7256d` | pins only |
| 3 | classify the remaining degrade (names the callee) | `0c85b80` | fix (walker 130→131) |
| 4 | an inert opaque call does not taint | `ea21496` | fix (walker 131→132) |
| 5 | nimble registration + version floor pin | `1e91448` | pins only |

### Slice 1 — the floor

`hasSymexPragma(sym, name)` (generalised from `hasSymexOpaquePragma`) +
`hasSymexTransparentPragma`; the statement-position call arm in
`dsl_parser.nim` returns `mkBlock(@[])` — the established no-op — for a
transparent callee; `coverage.nim` declares its own private
`template symexTransparent() {.pragma.}` (it must stay a Z3-free leaf, so it
cannot import `nelli/symex`; the parser matches pragmas purely by NAME, which
is what makes the private copy sufficient); `symex.nim` exports a public
`symexTransparent*` beside `symexOpaque*`.

**No walker version bump.** This is a parse-time change: the IR itself
differs, so `canonicalize(prog)` moves the cache key on its own and no stale
verdict can be replayed.

### Slice 2 — pins, no implementation

All four passed on first run against slice 1. All four were then verified RED
against `ac507c1`'s `src/` (same test file, `git checkout ac507c1 -- src/`),
so they are sensitive pins rather than vacuous ones.

### Slice 3 — the degrade names the call

New classified kind `feOpaqueCallUnmodelled` (sevError), appended at the enum
tail for ordinal stability, sunk into `w.walkDegradeErrors` (whose drain
dedups by message, so N calls to one callee collapse to one entry while two
callees each get named). `fe` and not `we` deliberately: the black-box
decision is the front end's — the parser chose `mkOpaqueCall` — and this is a
construct gap, not a walker fault.

Walker 130→131. Not a verdict change (the status is `sxUnknown` before and
after) but `r.errors` is part of the cached result, so a v130 entry would
replay the old misdiagnosis.

### Slice 4 — the engine proves inertness for an untagged call

`{.symexTransparent.}` is the author's promise. Slice 4 is the engine proving
the same thing for a call nobody tagged, keeping the `mkOpaqueCall` IR and
dropping only the taint. An opaque call is **inert** iff it binds no result
AND every actual argument is plainly value-typed: no `nnkHiddenAddr` (which
IS how Nim passes a `var` formal) and a `typeKind` in a closed allowlist of
`ntyBool`/`ntyChar`/`ntyString`/`ntyEnum`/`ntyRange` and the int/uint/float
families, with `nnkHiddenStdConv`/`ntyVarargs` unwrapped to its `nnkBracket`
elements. `ntyObject`, `ntyTuple`, `ntySeq`, `ntyRef`, `ntyPtr`, `ntyProc`
and `ntyCString` are excluded — a copied object can carry a `ref` field whose
pointee the callee writes, and a `cstring` is a writable pointer. Unrecognised
means not inert.

**The soundness argument, which was measured and not argued.** With no bound
result and nothing writable passed in, the only channel left is a
module-level global. The walker does not model globals AT ALL: a SUT
branching on one already answers `sxUnknown` carrying a raw `KeyError: key
not found: gLimit`, independently of any opaque call
(`scratchpad/bench/probe_163_globals.nim`). So a SUT that could observe such
a mutation has already degraded at its own read site, and dropping this taint
cannot introduce a false verdict. What it forgoes is a callee that never
returns or that raises — a pre-existing, symmetric gap, since `echoAfter`
(echo *after* the branch) already answered `sxRaised` before any of this.
Ordering, not soundness, is what changed.

Five sites: `IRStmt.opaqueInert` + `mkOpaqueCall(..., inert = false)`
(`types.nim`), the predicate + the statement-position call site
(`dsl_parser.nim`), **`emitStmt`'s round-trip** (`dsl_parser.nim` — the
#162-slice-5 trap: the walker never sees the macro-time `IRStmt`, only the
value rebuilt from those `newCall` nodes, so a field omitted there silently
reverts to its default and the tests stay red *identically* to before the
fix), `canonicalize`'s `;inert=` rider, and the walker's
`if stmt.opaqueInert: return paths`.

Walker 131→132. A real verdict change this time.

### Slice 4's RED was verified after the fact

The slice was implemented before its tests were written. Re-checked against
slice 3's `src/` (`git checkout 0c85b80 -- src/`): both positive tests fail
there, with the classified `feOpaqueCallUnmodelled` naming `echo` visible in
the failure output — which incidentally confirms slice 3 end-to-end. The
var-param and ref-arg pins PASS at slice 3, as they must: they assert
behaviour slice 4 deliberately leaves unchanged. They guard the predicate
against over-reach ("void means inert"), not against the base commit.

## Method note — the oracle is executed, not asserted

Inherited from #162. Every symbolic expectation in the test file is paired
with the same computation run for real in the same file: the oracle test calls
all four instrumented SUTs and checks each raises on `Magic` and only on
`Magic`. A taint bug is exactly the shape where a test can encode the engine's
own wrong model and pass.

## Gates run

| Gate | Result |
|---|---|
| `tsymex_163_opaque_transparent`, `c` | 12/12 |
| `tsymex_163_opaque_transparent`, `cpp` | 12/12 |
| `tsymex_phase15_CR2_cachekey`, `c` | 7/7 (v132 pin) |
| `tsymex_g3fix_walkergap`, `c` | 1/1 — the crash pin guarding the pragma plumbing |
| full `sweep.sh` diff vs `ac507c1` | **see below** |

Sweep baseline taken the way #161's handoff prescribes: a worktree pinned to
the base sha with `_deps` and `nim.cfg` **copied in** (they are
milpa-generated and gitignored; without them every test fails to compile and
the log reads 100% `rc=1`). Baseline and current run strictly sequentially —
concurrent `dt-bounded` runs of the same test file clobber one shared binary.

## Surfaced, not fixed here

- **A module-level global read reports `weInternalWalkerFault` carrying a raw
  `KeyError`.** Measured while establishing slice 4's soundness: a SUT
  branching on a module-level `var` degrades with "KeyError: key not found:
  gLimit" classified as a walker fault. This is the SAME unclassified-degrade
  class as #163's second defect, at a different site (`lower(iekVar)`), and
  it is a common enough SUT shape to deserve its own issue. Not filed —
  deliberately left for Corey rather than widening #163.
- The opaque arm is not the only site that sets `w.sawUnknown` bare; the
  `maxCallDepth` bail and the missing-`ProcSig` bail in the same `isCall`
  dispatch have the same shape. The missing-`ProcSig` one is classified in
  practice (`geInstantiationCapped` rides `prog.parseErrors`); the
  `maxCallDepth` one is worth an audit of its own. Not widened into #163.
- #159 (`recordEdge`'s inferred `.sideEffect` makes `{.cover.}` unusable on
  `func`/`noSideEffect` targets) is adjacent but independent — it is about
  Nim's effect system, not symex's taint.

## Current stage — audit complete, remediating all 13 findings

#163's own five slices are landed and green on both backends. The
`/wiring-audit` over the combined surface is COMPLETE (three lenses: A =
#163 pragma/opaque, B = #161/#162 overflow/range, C =
cache-key/CI-reach/ledger-truth). Corey's call: **push, and fix everything
now.**

### Verdict — the surface did NOT close clean

`wiring` is deliberately NOT set to `proven`, and `/code-review` stays
gated. The load-bearing property is reachable and test-proven for what is
pinned, but three gaps of the SAME defect class #162 slice 5 closed are
still open (seq elements, `ref object` fields, char-bounded aliases), and
until the push below nothing had been verified on the platform all three
handoffs say must verify it.

### Done since the audit

- **W1 closed.** `git push -u origin rfc-161-163-symex-defects`. All three
  Windows legs fired on the combined branch for the first time —
  `symex-mingw` (runs 35308512446), `fuzzer-mingw`, `fuzzer-msvc`. Seven
  walker bumps across three issues had until now been verified only in
  local Linux/podman sweeps.

### In flight — four agents, partitioned by file so they cannot collide

| Agent | Findings | Owns |
|---|---|---|
| 1 | W3 char-range alias, W7 enum domain | `dsl_typebridge.nim`, new `tests/tsymex_164_range_domain_reach.nim` |
| 2 | W11 registration, W12 floors, W13 ledger truth | `nelli.nimble`, pin files, handoffs |
| 3 | W5 pragma-fallback pin | `tests/tsymex_163_opaque_transparent.nim` |
| 4 | W2 seq elements, W4 ref-object fields | `runtime.nim`, `runtime_heap.nim`, new `tests/tsymex_164_range_elem_reach.nim` |

**Wave 2, NOT yet started:** W6, W8, W9, W10 all live in `runtime.nim`,
which agent 4 owns — concurrent edits would lose work. They start when
agent 4 lands.

### Three decisions taken during remediation

- **One version bump, not seven.** Every agent is forbidden to touch
  `symexWalkerVersion`, `canonicalize.nim` or the CR2 pin value; the
  control loop lands a single **132→133** at the end documenting every
  semantic change. Seven agents each editing those two files would conflict
  on every commit, and one increment invalidates the cache as completely as
  seven.
- **W2 asserts at READ sites, not via a quantified constraint on the
  backing array.** A `forall` over the seq array would be exact but drags a
  quantifier into every seq query, against the engine's lazy-materialisation
  style. Cost: an element never read stays unconstrained — sound for
  verdicts, NOT for witnesses, so extraction must clamp too. Both halves
  required or the finding is not closed.
- **The W5 pin must be mutation-tested.** A test that merely passes proves
  nothing for an absent-call finding; agent 3 must delete the fallback
  disjunct, watch its test fail, and restore it.

### Remediation progress — 12 of 13 closed, W8 the only one open

| Finding | State | Commit |
|---|---|---|
| W1 never pushed | closed | pushed; CI rounds 1-2 ran |
| W2 seq elements | closed | `a4ec45f` |
| W3 char-range alias | closed | `05f8e01` |
| W4 ref-object fields | closed | `61fca8b` |
| W5 pragma fallback | closed | `7d0ee90` + `d5108de` (mutation-strengthened) |
| W6 variant-disc else arm | closed | `9da19ab` |
| W7 enum domain | closed | `05f8e01` |
| W8 isIntOffset arms | closed | `bd6a013` — fourth attempt; the round-1 "precision only, no crash" characterisation was WRONG (the RED hangs rather than asserting). See its own section. |
| W9 obligation operand | closed | `9068f16` + `1deff68` |
| W10 concolic drain | closed | agent commit + `26f620d` |
| W11/W12/W13 | closed | `a1fc02c`, `9206071`, `7878212` |

Plus `d981a78` (retired the #137 pin #163 supersedes), `1404fb5` (rename +
registration), `c0d61d1` (v133), `1deff68` (v134).

**Walker versions: TWO bumps, deliberately.** v133 covers the five findings
that landed in parallel (W2, W3, W4, W6, W7); v134 covers W9, which landed
after. Folding W9 into 133 would have let a v133 entry replay its false
negative. CR2 pin at `== "134"`; all five `tsymex_163audit_*` suites carry a
numeric floor at `>= 134`.

**W10's fix reached further than the brief.** `ConcolicYieldCounters` had
moved to `concolictaxonomy.nim`, and `foldFlipResult` needed the new field
folded in too — otherwise the counter would have been dropped at campaign
aggregation, the same drop-on-the-way-out bug one level up.

### Old progress table (superseded)

| Finding | State | Commit |
|---|---|---|
| W1 never pushed | closed | pushed; CI round 1 ran |
| W2 seq elements | closed | `a4ec45f` |
| W3 char-range alias | closed | `05f8e01` |
| W4 ref-object fields | closed | `61fca8b` |
| W5 pragma fallback | closed | `7d0ee90` + `d5108de` |
| W7 enum domain | closed | `05f8e01` |
| W11/W12/W13 | closed | `a1fc02c`, `9206071`, `7878212` |
| W6, W8, W9, W10 | wave 2, IN FLIGHT at the time of writing | see below: W6 `9da19ab`, W9/W10 landed in wave 2, **W8 closed `bf6de33` and PINNED `bd6a013`** in review round 8 |

Plus `d981a78` (retired #137 pin, see below) and `1404fb5` (rename +
registration).

### CI round 1 — the push paid for itself immediately

`fuzzer-mingw` ✅, `fuzzer-msvc` ✅, **`symex-mingw` ❌**. The failure was a
REAL regression from #163 slice 4, not a platform quirk:
`tests/tsymex_rectify_effects.nim` asserts that an `echo` ahead of the
target degrades the run to `sxUnknown` — #137's original contract, which
slice 4 deliberately narrowed. Retired the way #162 retired #161's `mul32`
trip-wire: the two pins now assert the new behaviour with the rationale and
the knowingly-forgone part in the file header, and TWO NEW cases were added
that the file never had — a USED opaque result and a `var`-argument call,
both still tainting, both asserting the classified kind names the callee.
Three tests describing a mechanism became five that separate where it
applies from where it does not.

**Process lesson, recorded because it cost the catch:** `sweep.sh` would
have found this locally — the suite is registered — but the current-side
sweep was stopped to free the tree for edits, so the gate covering exactly
this fallout class never ran. Windows caught what Linux was about to. The
suites chosen by hand (`tsymex_163`, CR2, g3fix) could not see it; a
behaviour change to the opaque arm should have pulled in every suite
mentioning `echo`, which a grep would have found in seconds.

Also confirmed from a fresh run: all nine scan-tail suites pass on Windows,
including the six `tsymex_r6_*` that hang forever on Linux/podman.

CI round 2 is running against `d981a78`. **Watch it:** it is the first run
carrying W11's 86 newly-registered suites, which have run in NO CI leg ever.
Reds there are discoveries about pre-existing code, not regressions from
this branch — but verify each against `main` rather than assuming.

### FINAL STATE — both gates green, work complete

**Sweep gate, clean:**

```
unchanged=460 regressed=0 new-failing=0 fixed=0 skip-changed=0 new-ok=6 gone=0
```

All six new suites pass; nothing moved against the `ac507c1` baseline.
(`cur163final.log` vs `base163.log`, full `tests/t*.nim` both sides.)

**CI round 3, clean:** `symex-mingw` ✅ `fuzzer-msvc` ✅ `fuzzer-mingw` ✅
against `26f620d` — both walker bumps, all five `tsymex_163audit_*` suites
and W11's 86 registered orphans, all Windows-verified.

**`wiring` is deliberately NOT set to `proven`.** W8 remains an open gap,
and the audit's own rule is that a surface with a known dark mechanism does
not get asserted proven — the gaps get filed instead. W8 is a precision gap
on an internal representation (no crash, no demonstrated wrong verdict) and
is the cheapest of the thirteen to carry, but it is still open, so the flag
stays honest. Setting it is Corey's call. (`quipu` is also not on PATH in
this environment; the tracker API answered 404 for this project's endpoints
all session.)

**Recommended next:** `/code-review` on the branch. It was gated behind this
audit deliberately — reviewing a surface before knowing whether it is
reachable wastes the round.

### SUPERSEDED — stage notes from while the work was in flight

All 13 findings resolved or recorded: **12 fixed, W8 open**. Nothing left to
implement. Two gates outstanding, and BOTH must be read before
`/code-review` or `wiring = proven`:

1. **CI round 3 — DONE, all three legs GREEN** against `26f620d`:
   `symex-mingw` (41m), `fuzzer-msvc` (36m), `fuzzer-mingw` (10m). That run
   carried both walker bumps, all five `tsymex_163audit_*` suites, and
   W11's 86 registered orphans. Every fix in this remediation is now
   Windows-verified.
2. **Final sweep — THE ONLY GATE LEFT.** At last check 457 of ~465 entries,
   minutes from done:
   `/home/corey/.claude/jobs/4fd5573d/tmp/gate163final.sh` → diff appended
   to `gate163final.out`, current log `cur163final.log`, against the
   COMPLETED 460-entry baseline `base163.log` (pinned at `ac507c1`).
   **Nothing may edit `src/` until it finishes** — `sweep.sh` compiles
   per-test as it runs. Stopping it early once already cost this session the
   `tsymex_rectify_effects` catch, which Windows found instead.

If the sweep diff is clean and `symex-mingw` is green: `/code-review`, then
`quipu set <doc>/wiring proven`. If not, the diff names what moved.

### Still-unfiled defects found along the way (candidates for issues)

- `symexFind` fails to COMPILE for a proc taking an object with a plain enum
  field (no enum witness reader; `symex.nim`). Worse than a degrade.
- `c > 'm'` does not parse for ANY char range (`nnkHiddenSubConv` gap,
  `dsl_parser.nim`) — inline and alias alike. Blunts W3.
- A module-global read reports `weInternalWalkerFault` with a raw `KeyError`
  — same unclassified-degrade class as #163's second defect, different site.
- The `maxCallDepth` bail still degrades unclassified (`runtime.nim:~10236`).
- An un-suffixed int literal above `int32.high` defaults to `int64`, so
  mixing it with `.len` is a hard type mismatch (found building W9's repro).

### CI round 2 — all three legs GREEN, including the 86 new suites

`fuzzer-mingw` ✅, `fuzzer-msvc` ✅, `symex-mingw` ✅ against `d981a78`. That
run carried W11's 86 newly-registered suites, which had run in NO CI leg
ever. I predicted reds ("expect discoveries"); there were none — all 86
passed on Windows first time, as did the retired #137 pin. The three
`tsymex_163audit_*` suites were registered in `1404fb5`, after that push,
so they arrive in round 3.

### W8 — NOT blocked. My blocker was a bad generalisation.

Retracted. The first W8 test SUT did hang at the 600s bound, and a probe
with the range removed hung identically, so I concluded the two arms were
unreachable without fixing a pre-existing engine hang. That conclusion was
wrong, and the error was generalising from ONE recogniser family.

The scan recognisers are several distinct families, and the Linux/podman
sweep skips exactly one of them by name. From the recorded baseline
(`base163.log`):

| suite | family | Linux |
|---|---|---|
| `tsymex_r6_b3_scanpair` | B3 early-return-on-match | **skip** (known hanger) |
| `tsymex_r6_b0_scanlift_bound` | Q1/B0 skip-while-and-clamp | rc=0 |
| `tsymex_r6_b4_readcstring` | B4 accumulating | rc=0 |
| `tsymex_r6_b5_chained` | chained composition | rc=0 |
| `tsymex_r6_b6_optionregion` | option region | rc=0 |

Both the original test SUT and my confirming probe were written in B3's
shape — the single family that is a documented Linux hanger. Three other
families reach the same bare int-offset arm and run fine here.

Rewritten: the bare-offset SUT now uses the **Q1/B0 skip-while** shape
(`while i < s.len and s[i] != ':': inc i; return i`); the tuple SUT keeps
B4's early-return form, which is `tsymex_r6_b4_readcstring`'s own family
and passes locally. The shape constraint is recorded in the test file
itself so nobody re-writes it into B3's shape and rediscovers the "hang".

Lesson worth keeping: a hang under Linux/podman in this repo is a
platform-split hypothesis FIRST (see the `symex-r6-linux-hangs` memory and
sweep.sh's skip list), not a new engine defect — and "one shape in this
family hangs" does not generalise to the family.

**But W8 is still NOT closed, for a better reason: there is no RED.** With
the B0 shape the bare-offset test passes with NO W8 fix applied, so it
pins nothing; the tuple test still hangs (its B4 SUT uses an
early-return-in-loop form structurally close to B3's). Two possibilities,
and they need evidence rather than another shape guess:

  (a) the Q1/B0 path does not route through the `isIntOffset` bare arm at
      all, so the test is vacuous for this finding; or
  (b) W8 is another W6 — already closed incidentally when #162 slice 5 put
      the bounds on `IRType`, since both arms are handed a type that now
      carries them.

**Next step is instrumentation, not shape-guessing:** observe which arm
actually allocates the symbol for a recognised scan return (a parse/walk
trace or a temporary echo in `freshRetSym`), then write the test against
the arm that is really taken. Three shape guesses cost a build cycle each
and produced two wrong conclusions about W8 in one session; stop guessing.

Owner: corey. W8 is a precision gap on an internal representation — no
crash and no demonstrated wrong verdict — so it is the cheapest of the 13
to defer, and the only one still open.

### W6 was real after all

Briefly misreported in-session as a false positive: a test run raced the
fix commit and compiled a tree that already had it. `9da19ab` implements
the skip-the-disjunction fix in BOTH discriminator-domain builders (BV and
promoted-Int) with tests. The audit's reasoning held.

### Resolved: the 20-vs-21 question

Not a regression. `tests/tsymex_162_range_base_width.nim` has 21 `test`
blocks and reports 21/21 from two independent agents with all fixes
applied. Agent 1's "20/20" was a miscount.

### Older notes

Closed: **W1** (push; all three Windows legs fired, `fuzzer-mingw` green),
**W5** (`7d0ee90` + `d5108de`), **W11/W12/W13** (`a1fc02c`, `9206071`,
`7878212`), **W3/W7** (`05f8e01`). Remaining: W2/W4 in flight; W6, W8, W9,
W10 queued behind them in `runtime.nim`; then the single bump.

**W5's pin was strengthened after the fact.** The delivered version used
`probe(): int = 7`; removing the fallback disjunct made the walker descend
into the literal, solve `x + 7 == Magic`, and answer `sxRaised` — a MORE
precise answer, so the test pinned a precision choice rather than the
property the disjunct exists for. `probe` now reads a module-level var, so
removing the disjunct produces `weInternalWalkerFault: KeyError: key not
found: probeState` — the G3fix crash shape. Re-verified by mutation both
ways. Status is `sxUnknown` either way, so the error-KIND assertions are
load-bearing, not decoration.

### OPEN VERIFICATION — do not mark W3/W7 done until resolved

Two agents reported different counts for `tests/tsymex_162_range_base_width.nim`:
agent 2 said **21/21**, agent 1 (running it as non-regression WITH the
W3/W7 `dsl_typebridge` change applied) said **20/20**. The file contains 21
`test` blocks and agent 2's commit added none, so either agent 1 miscounted
or one test stopped running under the enum/char-range change. Re-run it
directly once agent 4 releases the file (both were told to use it as a
gate, and concurrent runs of one test file clobber a shared binary).

### New defects surfaced by W7's work — NOT fixed, candidates for filing

- **`symexFind` fails to COMPILE for any proc taking an object with a plain
  enum field.** Witness reconstruction rebuilds a nominal object via a real
  `nnkObjConstr`, and an enum-typed field's reader is `readUInt8`/
  `readUInt16` (there is no dedicated enum reader), producing a value Nim
  will not implicitly convert to the enum type. A compile failure, not a
  degrade — strictly worse than `sxUnknown`, and it predates this branch
  (independent of `hasRange`). Lives in `symex.nim`, so it was out of the
  agent's scope; the field route was verified via a compile-time
  `classifyFieldType` probe instead.
- **`c > 'literal'` on ANY char-range value hits an `nnkHiddenSubConv` gap**
  in `dsl_parser.nim` → `feUnsupportedExprKind`, for the inline spelling as
  well as the alias. This blunts W3: the alias now classifies correctly, but
  the most natural thing to write about a char range still does not parse.
  The W3 tests use `ord(c) > ord('m')` to sidestep it via the existing
  `ord`-as-identity case. W3 is still worth having (it stops a whole-run
  degrade) but it does not make char ranges usable on its own.

### Sweep gate — half done, deliberately

Baseline at `ac507c1` COMPLETE: `/home/corey/.claude/jobs/4fd5573d/tmp/base163.log`,
460 entries, from a worktree with `_deps`/`nim.cfg` copied in. The current
side was started and then **killed on purpose** — `sweep.sh` compiles
per-test as it runs, so editing `src/` mid-sweep contaminates the log (the
trap #161 recorded). Re-run the current side ONCE against the final tree:

```
/home/corey/.claude/jobs/4fd5573d/tmp/base163   # pinned worktree, keep it
scripts/sweep.sh <tmp>/cur163final.log && scripts/sweep-diff.sh <tmp>/base163.log <tmp>/cur163final.log
```

### Consolidated audit ledger — 13 findings, none fixed

Covers all three issues (the branch is combined, so the audit was too).
Ranked by blast radius of the GAP, not size of the fix. Every row's default
disposition is **wire it**; there are no deletion candidates in the set.

| # | Kind | Finding | Anchor |
|---|---|---|---|
| **W1** | 6 unreachable-by-default | **Nothing was ever pushed.** `origin` has no `rfc-16*` branch; 27 commits unpushed; newest CI run on any branch is the v0.8.0 release, nine days before these commits. All three handoffs declare the `rfc-*` naming exists so `symex-mingw` verifies seven walker bumps — that verification has never run. VERIFIED by me. | `git branch -r`; `.github/workflows/symex-mingw.yaml:118` |
| **W2** | 2 + 7 | **`seq[range[lo..hi]]` elements never receive their bounds.** `ty.hasRange`'s entire runtime consumer set is ONE site. Seq data is a Z3 array via `allocateSeqDataRaw`; elements never reach that arm, and the `isIndex` read lifts without consulting `seqElemTy.hasRange`. False-SAT plus the slice-5 witness-`RangeDefect` crash class, one container over. Directly falsifies this repo's own written claim that seq elements "inherit the constraint through `allocateSym`'s existing recursion". Arrays genuinely do inherit it. | `runtime.nim:2343` (sole consumer) vs `:2452`, `:9284`, `:6863`; claim at `dsl_typebridge.nim:58`, `docs/issue-0162-…:226` |
| **W3** | 2 | **`type Letter = range['a'..'z']` degrades the WHOLE run.** The alias arm guards both bounds `kind in nnkIntLit..nnkUInt64Lit`; `nnkCharLit` is outside it, so the alias falls to `feUnsupportedParamType` → whole-run `sxUnknown`. The inline spelling has no kind guard and works. Exactly the one-route-fixed-one-route-forgotten shape #162 slice 3 existed to kill. VERIFIED by me. | `dsl_typebridge.nim:568` vs `:484` |
| **W4** | 2 + 7 | **Range-typed fields of a `ref object` drop their bounds.** Heap-modelled fields are materialised by `heapSelect` at deref, never by `allocateSym`'s recursion; no heap reader consults `hasRange`. Every slice-5 test uses a plain VALUE object, so the "object field route is covered" row is true of only half the route. | `runtime.nim:2182` / `runtime_heap.nim` vs `docs/issue-0162-…:185` |
| **W5** | 5 | **The `{.symexTransparent.}` soundness story is unpinned.** The expression-position fallback is the whole "over-claimed pragma costs precision, never soundness" argument; delete that disjunct and a used-result transparent callee body-walks into the G3fix `KeyError` shape with NO red test. The public pragma has no test consumer at all — everything green exercises coverage.nim's private copy. | `dsl_parser.nim:3969`, `symex.nim:1103` |
| **W6** | 4 producer-less consumer | **Range-typed variant discriminator + `else:` arm.** Both disc-domain builders cover else-arm ordinals by fanning out over `vDiscTags`, which the non-enum route never populates — so with an `else:` present the disc is pinned to the explicit `of N:` literals and every else path is falsely unreachable, in both modes. | `runtime.nim:2244`, `:12587` vs `dsl_typebridge.nim:304` |
| **W7** | 6 | **Plain enum params/fields get no domain constraint**, declined for a reason #162 itself retired (the guard is signedness-based now). Out-of-domain ordinals are model-reachable; variant discriminators get their disjunction, plain enum values get nothing. VERIFIED by me. | `dsl_typebridge.nim:578` vs `runtime.nim:12648`, `:12652` |
| **W8** | 2 | The two isIntOffset allocation arms ignore `ty.hasRange` that the parameter arm deliberately rescues. | `runtime.nim:12711` vs `:2323`, `:2374` |
| **W9** | 2 | Overflow-obligation dispatch keys on the LEFT operand's stamp only, so `s.len * x` with a stamped `x` raises no obligation. Pre-existing, but it is a hole in the very invariant #161 declares. | `runtime.nim:4690`, `:4694` |
| **W10** | 2 | **The concolic path never drains the degrade sink.** Two top-level `walk()` drivers; `runConcolicCollectImpl` reads neither `w.walkDegradeErrors` nor `w.sawUnknown`. Slice 3's property holds on `symexFind`, not on `concolicFlip`. Diagnostics, not soundness. | `runtime.nim:10159` vs `:13329` |
| **W11** | 2 | 88 test files unregistered (83 `tsymex_*`), including `tsymex_phase16_R16_4_overflow`, `R16_5_overflow_thru_closure`, `R16_2_rangedefect` — the pre-existing pins most adjacent to what #161/#162 changed. They run in no CI leg. | `nelli.nimble` vs `tests/` |
| **W12** | 7 | Version floors: #161 and #162 compare version STRINGS (false red at "1000"); #163 uses `parseInt`. #161 pins `>= "126"` but contains tests needing 127 and 128. All are `>=` (correct); the CR2 `==` pin is correct. | `tsymex_161_…:179`, `tsymex_162_…:191` |
| **W13** | 7 | Ledger/comment truth: three test headers still call `recordEdge`/`logCmp` `{.symexOpaque.}` and say their calls "become `mkOpaqueCall`" (both false since #163 slice 1); the CR2 file's running ledger skipped five of seven bumps (the pin VALUE discipline held, the narrative didn't); #162's "15/15" predates slice 5's 21 tests; #161's follow-up 5 was fixed by #163 on this branch with no note; #163's own "Gates run" table presents the sweep row as a result when it is still open. | `tsymex_g3fix_walkergap.nim:10`, `tsymex_g4_cmpwalk.nim:3`, `tfuzzcmplog.nim:7`, `tsymex_phase15_CR2_cachekey.nim:732` |

**Verified clean, so nobody re-audits it:** both new cache-key chains are
closed end-to-end (`IRType` bounds and `opaqueInert`, producer → emit
round-trip → consumer → canonical form); `feOpaqueCallUnmodelled` is
genuinely emitted; all seven walker bumps carry real recorded reasons;
`emitIRType` is total (the one unthreaded field has a current, accurate
justification); `IRType.==`'s deliberate exclusion was checked against every
memoisation consumer and bites none; `RawResult.obligations` is genuinely
consumed, not dormant; the `mul32` trip-wire is genuinely retired; no error
kind documented as emitted has silently stopped; `opaque: true` is
constructed in exactly one place; no inertness verdict is wrong across the
whole `OpaqueEffectfulProcs` catalog; #163 slice 1's no-bump argument holds
for every in-repo consumer.

### Lens A findings — detail

| # | Kind | Finding |
|---|---|---|
| F1 | partial consumer set | `feOpaqueCallUnmodelled` is pushed mode-independently (`runtime.nim:10159`) but only ONE of the two top-level `walk()` drivers drains it. `runConcolicCollectImpl` (`runtime.nim:13329`) reads neither `w.walkDegradeErrors` nor `w.sawUnknown`, so slice 3's property holds on `symexFind` and not on `concolicFlip`. Diagnostics, not soundness (Track E re-verifies concretely). Wire: surface a taint counter through `ConcolicYieldCounters`, beside `ambiguousBranches`, which already rides that channel. |
| F3 | consumer-less producer | The expression-position fallback (`dsl_parser.nim:3969`) is the whole "an over-claimed pragma costs precision, never soundness" argument — and NOTHING pins it. Delete that disjunct and a used-result transparent callee falls through to body-walking (the G3fix `KeyError` shape) with no red test. The public `symexTransparent*` (`symex.nim:1103`) likewise has no test consumer; everything green exercises only `coverage.nim`'s private copy via `{.cover.}`. |
| F2 | regressed claim | Three test headers still assert `recordEdge`/`logCmp` are `{.symexOpaque.}` and that their calls "become `mkOpaqueCall`" — both false since slice 1: `tsymex_g3fix_walkergap.nim:10`, `tsymex_g4_cmpwalk.nim:3`, `tfuzzcmplog.nim:7`. Tests still pass (a drop is strictly stronger than opacity), but this handoff leans on the g3fix pin as the proof no route regressed, and its header now describes a mechanism never engaged. Comment-only fix. |
| F4 | confirmed, pre-existing | The `maxCallDepth` bail (`runtime.nim:10236`) still sets `w.sawUnknown` bare — the exact shape slice 3 fixed for the opaque arm. Already in "Surfaced, not fixed here"; confirmed still true at this tree. |

### Two corrections to earlier claims in this doc's own lineage

- There is only ONE `runSymexImpl` — the line earlier believed to be a second
  overload is a forward declaration.
- `mkOpaqueCall`'s omission of `retIntOffsetPositions` from `emitStmt` is
  correct **by construction**, not a silent round-trip drop: only the
  `mkCall` producer computes `calleeIntOffsetReturnPositions`, and an opaque
  callee's body is never analysed, so the closed-form proof cannot exist.

Lens A also cleared the third-route question (`opaque: true` is constructed
in exactly one place, `types.nim:3006`, with exactly the two parser call
sites plus `emitStmt`'s preserve-only round-trip) and found no case where
inertness is wrong across the whole `OpaqueEffectfulProcs` catalog
(`echo`/`print`/`writeFile`/`sleep` become inert; the rest are excluded by
`ntyPtr`/`distinct` handles).

## Resume command

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -8 rfc-161-163-symex-defects
tail -40 /home/corey/.claude/jobs/4fd5573d/tmp/gate163final.out   # final sweep + diff
gh run list --branch rfc-161-163-symex-defects --limit 3          # CI round 3
```

Next actions, in order:

1. Collect wave 2 (W6/W8/W9/W10, agent in flight on `runtime.nim`).
2. Land the single walker bump **132→133**: `canonicalize.nim`'s version
   const with a prose paragraph covering every semantic change in this
   remediation (W2, W3, W4, W6, W7, W8, W9 are all verdict changes), the
   CR2 `==` pin value, and a `parseInt(...) >= 133` floor pin in each of the
   three `tsymex_163audit_*` files (none has one — deliberately deferred so
   the bump could land once).
3. Re-run the current-side sweep to COMPLETION against the final tree and
   diff against the completed `base163.log`. Do not stop it early again.
4. Push; read CI round 3.
5. Only then `/code-review`; set `wiring = proven` only if 3 and 4 are
   clean.

Still-unfiled defects surfaced along the way (see sections below): the
enum-field witness COMPILE failure in `symex.nim`, the `nnkHiddenSubConv`
gap that stops `c > 'm'` parsing for any char range, the module-global read
reported as `weInternalWalkerFault` with a raw `KeyError`, and the
`maxCallDepth` bail that still degrades unclassified (W4 of lens A).

---

# Review ledger — `/code-review` round 1 (2026-09-18)

Scope: `main...HEAD` on `rfc-161-163-symex-defects` @ `26418f3` (50 commits,
9 source files, 13 test files). Seven lenses in parallel (correctness×2,
cache-key integrity, security, design, liveness, test quality), then five
adversarial verifiers on every Critical/High. `quipu` is not on PATH, so this
ledger lives here rather than in `docs/rfc/<id>-review.md`.

State: **`reopened`** — round 4 in progress. Corey directed "fix mediums and
lows now too and yes to R11", so the deferred set is now in scope.

CORRECTION to the round-3 close-out: it reported "0 Critical / 0 High
remaining". That was WRONG. **R16 is a High that was recorded and left open**
— round 3 surfaced nothing above Low in the CHANGED SCOPE, and that was
allowed to stand in for the whole ledger. R16 was never fixed and never
explicitly excluded. It is in round 4's scope.

Round 4 scope: R16 (High), R7-R14, R18-R23, and W8 from the wiring audit,
with R11's abstraction as the structural spine (approved). Sequencing is
dictated by file ownership: `runtime.nim` carries R8, R9, R10, R11, R12,
R16, R22 and W8, so those serialize; the `dsl_parser.nim`/`dsl_typebridge.nim`
cluster (R7, R13, R18, R19, R23) runs alongside. R11 lands FIRST as a
behavior-neutral refactor, because W8 and R8 then become one-line fixes on
top of it rather than two more hand-written instances of the same bug.

Previous state was: **`floor`** — 3 rounds. Mandate was Critical+High, then re-review to
the floor; R15 (a pre-existing Critical found mid-loop) was added by explicit
decision. Round 3 surfaced nothing above Low in either lens, so the loop
terminated. Mediums and Lows recorded as deferred, not fixed.

Closed: R1 `e1ea4bb`, R2 `6f2e0ed`, R3 `e5dd226`, R4 `c253007`, R5 `1e78fe5`,
R6 `d6483d2`, R15 `365b8bb`, R17 `ae6ebaf`, R20-comment `8d732ba`, plus the
single walker bump `c2e621f` (134 -> 135).
Deferred: R7-R14 (round 1), R18-R23 (round 2), and W8 from the wiring audit.

Round 3 also re-verified every row marked `fixed` against the actual code —
no row overstates what its commit does.

Commits land on the branch; nothing pushed without approval.

## Findings

| id | sev | status | file:line | finding | verdict |
|----|-----|--------|-----------|---------|---------|
| R1 | Critical | fixed `e1ea4bb` | `runtime.nim:10268-10269`, `dsl_parser.nim:1565-1626` | inert opaque call never lowers `stmt.cargs`, so an argument's raise-fork is dropped AND the taint that used to cover for it is gone. `echo(a div b)` → `sxSat` with witness `b==0`; real Nim raises `DivByZeroDefect` before the target. **Regression from slice 4.** | CONFIRMED |
| R2 | Critical | fixed `6f2e0ed` | `dsl_typebridge.nim:621-632` | enum domain arm: floor hardcoded `0'i64` (no `minOrd` tracked) excludes negative ordinals; and `bits` sized from member COUNT not ordinal magnitude, so `bvule(bv8, 300)` truncates mod 256 to `<= 44`. Both → false `sxUnsat`. Arm was `unranged` (sound) before this branch. **Regression from W7.** | CONFIRMED (a)+(b); (c) unsigned-suffix literal REFUTED empirically — `getImpl` normalizes every ordinal to `nnkIntLit` incl. negatives, so the narrow guard always matched. Guard widened anyway, defensively. |
| R3 | High | fixed `e5dd226` | `runtime_heap.nim:546-748` (sel. `:727`); `runtime.nim:6574-6622` | ref-to-variant ARM field: no `bvRangeConds` at the `isArmField` select (false `sxSat`), and no witness clamp in the `itVariant` pointee arm (`RangeDefect` in caller's process). W4 fixed the generic deref arm only. | CONFIRMED |
| R4 | High | fixed `c253007` | `runtime.nim:6229-6244` | `extractTableEntries` never clamps to `tabValTy` range, while all three sibling extractors do. Commit `a4ec45f` mirrored the CONSTRAINT side for Table and not the CLAMP side. Worsened by `collectTableLitKeys` being a static whole-body scan not gated to the winning path. Unaudited 14th finding in the W2/W4 family. | CONFIRMED |
| R5 | High | fixed `1e78fe5` | `tests/tsymex_161_overflow_obligation.nim` (whole file) | zero executed-Nim oracle blocks (vs 13 in `tsymex_162`, 4 in `range_elem`); every `sxRaised`/`sxSat` assertion is backed only by a comment. Verified by count. | CONFIRMED (count) |
| R6 | High | fixed `d6483d2` | all 8 new suites | concolic mode (`wmFollowConcrete`) untested for every new mechanism — `concolic` appears in `tsymex_163audit_w10.nim` only (10 refs; 0 in the other seven). Shared walker code, and the mode the fuzzer uses. Verified by count. | CONFIRMED (count) |
| R7 | Medium | fixed `24b9da6` | `dsl_parser.nim:7892-7912` | statement-position `{.symexTransparent.}` drop is unguarded by `isInertArg` (applied to the opaque sibling 8 lines later). A transparent proc writing through a `var` arg has the write deleted → false `sxUnsat`. `var` pointee never havoc'd. nelli's own 5 `coverage.nim` call sites are value-only, so shipped instrumentation cannot trip it. | CONFIRMED, High→Medium |
| R8 | Medium | fixed `a47852e` | `runtime.nim:6551-6573` | W4's witness clamp iterates only `pointee.fieldNames` — a ranged subfield two levels down is populated by recursion at a deeper dotted path and never clamped. | unverified |
| R9 | Medium | fixed `b13d484` | `runtime.nim:13497-13501` | W10's `walkDegradeCount` reads only `w.walkDegradeErrors`, not the `loweringDegradeErrors` threadvar that `runSymexImpl` also drains — a concolic collect hitting an unmodelled string op reports `0`, indistinguishable from clean. | unverified |
| R10 | Medium | fixed `d3fc8c2` | `runtime.nim:10282-10289`; `dsl_parser.nim:3958-3980` | `feOpaqueCallUnmodelled` emits identical text for "never tagged" and "tagged transparent but result used in expression position" — for the latter it advises the pragma the user already applied. | unverified |
| R11 | Medium | fixed `a663589` | 7 sites (`runtime.nim:2360,9401,9306`; `runtime_heap.nim:895`; `runtime.nim:6267,6410,6764`) | the range assert/clamp invariant is re-derived by hand per backing-store shape. R3 and R4 are the 8th and 9th instances. No structural signal that a new materialization path owes the constraint. | unverified (design) |
| R12 | Medium | fixed `06335b2` | `runtime.nim:2254-2269` vs `:12703-12758` | discriminator-domain decision computed independently in the BV and promoted-Int builders; W6 had to fix both. | unverified (design) |
| R15 | Critical | fixed `365b8bb` | `dsl_parser.nim:2470` | **enum constant embedded by DECLARATION INDEX, not ordinal.** `parseExpr`'s `nnkSym` arm (#141 resolver) returns `mkIntLit(int64(i - 1))`, the 0-based loop position, never reading `nnkEnumFieldDef`'s real value. For `enum roLess = -1, roEqual = 0, roGreater = 1`: `x == roLess` -> `sxSat` with witness `0` (= `roEqual`, which does NOT equal `roLess` in real Nim — a false witness); `x == roGreater` -> `sxUnsat` for a trivially reachable value (false negative). Shifts EVERY arm by one; invisible whenever ordinal == position, which is why dense-enum tests never caught it. **PRE-EXISTING (from #141), not a regression of this branch.** Found while measuring whether R2 closed its own repro. | CONFIRMED by measurement |
| R16 | High | fixed `9e48761` | `runtime.nim` `runConcolicCollectImpl` param binding | **concolic param binding ignores declared width/signedness.** Every `cbDrawLinked`/`cbConcretized`/`cbTransformLinked` scalar is built as an idealized non-wrapping `Z3Int` (`mkIntVar`); `p.ty.width`/`signed`/`hasRange` are never consulted. Demonstrated: `addU8Gate(a, b: range[0'u8..255'u8])` on the real trace `a=200,b=100` genuinely wraps to 44 and takes the `if` arm (confirmed under `wmExplore`), but `concolicCollect` reports `branchTrace[0].armTaken == -1` — the OPPOSITE arm — because `concreteBranchOutcome` evaluates under exact arithmetic. `pcSatByConcreteInputs` stays `true`: it checks the model against itself, never against the real execution. A wrong `branchTrace` feeds a `concolicFlip` G2 solve. **PRE-EXISTING, not a regression of this branch. This is the mode the FUZZER uses.** Found by R6. | CONFIRMED by measurement |
| R13 | Low | fixed `24b9da6` | `dsl_parser.nim:1507-1520` | by-name pragma matching fails SAFE for `symexOpaque` (extra `sxUnknown`) but UNSAFE for `symexTransparent` (call vanishes). Doc comments present both as equally low-risk. | note |
| R14 | Low | pinned `960da7b` | tests | untested: range lower boundary (`lo`, `lo-1`) — every tested range starts at 0; inert-allowlist exclusions beyond `var`/`ref`; whole-program wrap-scan ban; opaque call placed AFTER the target (pre-existing). | note |

## Verified clean (recorded so a later round need not re-derive)

- **Cache-key integrity.** Every semantic `IRStmt`/`IRType` field enumerated
  against `canonicalize.nim`; the four new ones render, the un-rendered
  pre-existing ones are witness-only or pure functions of already-keyed data.
  No separator ambiguity. `feOpaqueCallUnmodelled` is not serialized anywhere,
  so tail-append is safe. v133/v134 cover every verdict-changing hunk; W10
  correctly did not bump. All 94 nimble registrations resolve, no duplicates.
- **#163's load-bearing property is genuinely live.**
  `tsymex_163_opaque_transparent.nim:21,29-51` imports `nelli/coverage`,
  applies the REAL `{.cover.}`/`{.covercmp.}` macros to actual procs, and runs
  `symexFind` with an oracle. Not a hand-applied pragma on a synthetic proc.
- `feOpaqueCallUnmodelled` rides all four verdict branches (`runtime.nim:13163`,
  `13174-13182`, `13184-13186`); both degrade sinks drain in `runSymexImpl`.
- `emitStmt`/`emitIRType` round-trips all four new IR fields.
- `abstraction.nim` interval arithmetic sound; failure direction (`none` = ⊤)
  can only cost a redundant fork, never soundness.
- No Z3 FFI lifetime/refcount defects; `coverage.nim`'s fuzzer path is a
  pragma rename only, masking logic byte-for-byte unchanged.
- 496 untracked binaries in `tests/` are gitignored build artifacts; tree clean.

## Concolic reachability (established by R6 — reframes the R6 finding)

`ConcolicParamBinding` binds ONLY scalar `itInt`/`itBool` top-level params —
no seq, Table, ref or object — and a local `new()` zero-writes its fields
(Cluster H Step C) rather than leaving them free. So R3, R4, W2 and #161
cannot diverge by mode: there is no way to bind an unconstrained ranged
container param in a concolic walk at all. R1's headline property is also
unobservable — `ConcolicCollectResult` has no raised-verdict channel.
What IS reachable and is now pinned: `{.symexTransparent.}`/`{.cover.}`
instrumentation under concolic walk (the fuzzer's own path), and R1's
inert-call non-degrade. The remaining mode risk is R16.


## Round 2 (re-review of the round-1 fixes)

Three lenses over `26418f3..HEAD`: security, correctness, liveness+design.
Liveness and security returned no Critical/High. Correctness returned one
High (R17), verified adversarially and confirmed.

**Liveness verdict — all five source fixes are live end-to-end from a real
entry point**, and R3/R4/R15 each do genuine WITNESS REPLAY (read the value
back, cast to the declared type, prove no `RangeDefect` / prove it satisfies
the comparison). R15's suite notes explicitly that a `status`-only check
would have passed against the broken code. All six new suites registered
exactly once; no orphans; no stray artifacts; bump consistent with CR2 pin.

| id | sev | status | file:line | finding |
|----|-----|--------|-----------|---------|
| R17 | High | fixed `ae6ebaf` | `runtime.nim:6657-6668`, comment at `:6608-6610` | **R3 was incomplete.** The active-arm override overwrites Part B's clamped value with an unclamped `heapSelect`, justified by a comment claiming such a field "was read and is therefore range-safe". FALSE: `currentVariantHeaps = path.heaps` (`:7307`) is populated by the WRITE arm too (`runtime_heap.nim:1244,1252-1254`, byte-identical key), and the write arm asserts no range at all — its `allocateSym` proto conds land in a discarded `scratchPC`. A write-only ranged arm field reconstructs unclamped. Verdict `sxSat` is CORRECT; only the witness is illegal. |
| R18 | Medium | fixed `81040e5` | `dsl_typebridge.nim:678`, `dsl_parser.nim:2505` | tuple/string-valued enum fields (`enum a = (1, "x")`) fail the `nnkIntLit..nnkUInt64Lit` guard in BOTH ordinal loops, so both silently fall back to the positional counter. The two agree with each other (no witness/domain mismatch) but both are wrong vs real Nim ordinals — the same defect class R2/R15 fixed, for a value-node shape their guard does not recognise. Fails silently. |
| R19 | Medium | fixed `81040e5` | `dsl_parser.nim:2469-2479` | R15's retained `getType` fallback: if `getTypeInst` does not resolve (generic/aliased contexts), the shared loop's `nnkEnumFieldDef` check is never true from that path — per R15's own diagnosis — so every field silently reverts to pre-fix positional behaviour with no error, warning or degrade. Produces a wrong constant rather than failing loudly. Trigger conditions not enumerated or tested. |
| R20 | Medium | fixed `8d732ba` + pinned `960da7b` | `dsl_typebridge.nim:621-624` | R2's own comment still claims `promoteSound` "closes that door on its own" — true before the fix, when enums were always unsigned. R2 derives `signed := minOrd < 0`, so a negative-ordinal enum param now satisfies `hasRange and signed and fitsBVWindow` and takes the Z3Int promotion path **in the default `isOptimised` mode**, untested. No wrong verdict found through it. A false "this can't happen" comment describing a path the same commit made reachable. |
| R21 | Medium | pinned `960da7b` | `tests/tsymex_163rev_enum_domain.nim` | R2 is live and tested for TOP-LEVEL enum params only. Array element, seq element, and enum-typed variant discriminator are untested (the W6 discriminator test uses a range-ALIAS discriminator, not an enum one). Mechanism shares `allocateSym`'s recursion so is plausibly correct, but nothing exercises it. Object-field position correctly out of scope (pre-existing compile failure). |
| R22 | Medium | fixed `e09a286` (local site only) | engine-wide; only `RangeDefect` fork is `runtime.nim:8387` | **assignment-time `RangeDefect` is unmodelled.** Storing an out-of-range plain int into a `range[lo..hi]` field raises in real Nim; the engine forks `RangeDefect` only for float->int conversion. Surfaced by R17's analysis. Deliberately NOT fixed as part of R17: modelling the write as a CONSTRAINT would silently make a genuine `RangeDefect` unreachable, which is worse than the false witness it would cure. The faithful fix is a raise fork at the assignment. PRE-EXISTING. |
| R23 | Low | fixed `81040e5` | `dsl_parser.nim:2506-2513` | R15's loop `continue`s before advancing `nextOrdinal` for an unexpected enum-body node kind, whereas the classifier's loop always advances — desyncing the two "MUST agree" loops. No live repro on current Nim (children are consistently `nnkSym`/`nnkEnumFieldDef`); latent against a future Nim or macro-generated enum. |

### Design (round 2)

R11's duplication grew exactly as predicted: this round added 1 assert site
and 3 clamp loops, two of which are byte-for-byte copies of the `itTuple`
loop. Current totals: **5 assert sites, 6 clamp sites/loops.** The named
abstraction — `rangeCondsIfNeeded(v, ty)` beside `bvRangeConds`, and
`clampWitnessField(w, path, fty)` — would collapse them, and makes the
still-open **W8 a one-line fix** (`pcOut.add rangeCondsIfNeeded(v, ty)`)
rather than a special case. Recommend also collapsing R2's and R15's
mirrored ordinal loops into one `enumFieldOrdinals(enumBody)` in
`dsl_typebridge.nim` (already imported by `dsl_parser.nim`): mirroring by
written discipline is what R15 WAS.


## Round 3 (re-review of R17 + R20)

Two lenses over `c2e621f..HEAD` (correctness+security, liveness). **Nothing
above Low.** Explicit verdicts: R17's clamp correct and complete; signed/
unsigned routing matches its siblings; no walker bump owed (witness-only —
it adds no solver assertion and cannot change a verdict, so a stale cache
entry still holds a correct `sxSat`); R20's corrected comment factually
accurate against `promoteSound`'s actual conjunction and `types.nim:1962`.

R17's clamp reuses the SAME `fieldPath` local that `extractLeaf` wrote
rather than re-deriving the string, so write and clamp cannot drift.
R3's Part A and Part B confirmed intact — R17 is additive, not a bypass.
All seven `tsymex_163rev_*` suites registered exactly once, all carrying
the `>= 135` floor pin. No stray artifacts.

## Note on R2 / R15

R2 is correctly closed: the solver-enforced DOMAIN for a negative-ordinal enum is
now right, verified independently via `ord(x)`. But R2's headline repro
(`x == roLess`) is not delivered end-to-end, because R15 breaks the comparison
itself in a different file and a different code path. Recording R2 as "closes
the domain half" rather than claiming the repro works.

## Note on W8

R3, R4 and R11 are the same family as W8 (the open `isIntOffset` gap): a
declared range not reaching one particular materialization path. R11 is the
structural fix; W8 becomes one more instance rather than a special case.

---

# Current state — /code-review round, 2026-09-18

**Stage:** `/code-review` on the combined #161-#163 surface. Review loop is at
**`floor`** (3 rounds, 0 Critical / 0 High remaining). The ONLY thing still
outstanding is the final full-suite sweep gate, which was running when this
was written.

**Branch:** `rfc-161-163-symex-defects`, HEAD `8d732ba`. **NOT PUSHED** — the
last push was `26418f3`, so all ten review commits below are local only.
Pushing needs Corey's approval.

**Review commits, in order:**

```
1e78fe5  test  R5  -- oracles for the overflow suite (0 -> 6 oracle blocks)
e1ea4bb  fix   R1  -- inert opaque calls assert their arguments' defect forks
6f2e0ed  fix   R2  -- enum domains carry their true min, max and width
e5dd226  fix   R3  -- ref-to-variant arm fields reach their declared bound
c253007  fix   R4  -- table values reach their declared bound in the witness
365b8bb  fix   R15 -- enum constants embed their ordinal, not position
d6483d2  test  R6  -- pin the new mechanisms under concolic walk
c2e621f  chore     -- single walker bump 134 -> 135 for five verdict fixes
ae6ebaf  fix   R17 -- a written-not-read arm field clamps in the witness too
8d732ba  docs  R20 -- correct a soundness comment this round made untrue
```

**Seven new suites**, all registered in `nelli.nimble`, all pinned `>= 135`:
`tsymex_163rev_{inert_argfork, enum_domain, variant_armfield, table_elem,
enum_ordinal, concolic_modes, armfield_write}`.

**Open forks awaiting Corey:**

1. **Push the branch?** Ten commits, unpushed. CI has not seen any of them.
2. **`wiring = proven`?** Still withheld. W8 remains open, and rounds 1-3 added
   more gaps in the same family (R18-R23).
3. **File the unfiled defects?** Now eight, listed below and in the sections
   above: the five from the #163 work, plus R22 (assignment-time `RangeDefect`
   unmodelled), the `nnkHiddenCallConv` gap (`echo(intExpr)` fails to parse at
   all — found while building R1's repro), and R16 (concolic param binding
   ignores width/signedness, wrong `armTaken`, in the mode the FUZZER uses).
4. **Take the R11 abstraction?** Round 2 costed it concretely: 5 assert sites,
   6 clamp sites, and it makes the open W8 a one-line fix. Plus collapsing
   R2/R15's mirrored ordinal loops into one `enumFieldOrdinals`.

**Resume commands:**

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -11
tail -40 /home/corey/.claude/jobs/4fd5573d/tmp/sweepfinal2.out   # final gate
grep -c . /home/corey/.claude/jobs/4fd5573d/tmp/cur163final2.log # progress /460
scripts/sweep-diff.sh /home/corey/.claude/jobs/4fd5573d/tmp/base163.log \
                      /home/corey/.claude/jobs/4fd5573d/tmp/cur163final2.log
```

Baseline is the SAME `base163.log` (460 entries, pinned worktree at `ac507c1`)
the previous gate used, so the diff is comparable to the one recorded above.
An earlier run of this sweep was aborted at 149/460 and parked as
`cur163rev.aborted.log` — it predates R17/R20 and must not be used.

**Next step after the gate:** report the diff. If `regressed=0`, the review is
done and the decisions above are Corey's. If anything regressed, it belongs to
this round and gets a fresh slice.

## Round 4 progress

| finding | commit | note |
|---|---|---|
| R11 | `a663589` | `rangeCondsIfNeeded` + `clampWitnessField`; 10 sites collapsed (5 assert + 5 clamp). Two clamp sites deliberately left: `extractSeqElements`/`extractTableEntries` clamp a bare `int64` before the map key exists, so routing them through the helper would mean inserting a throwaway entry to patch it. Behavior-neutral, 7 suites green. Honest caveat from the agent: the helpers make the obligation cheap and obvious but nothing MECHANICALLY forces a new site to call them — a lint/CI gate would be needed for that. |
| R18/R19/R23 | `81040e5` | Single source of truth `enumFieldOrdinals*(enumBody): seq[(string, int64)]` in `dsl_typebridge.nim`, consumed by BOTH the classifier and `parseExpr`'s `nnkSym` arm. R18 RED confirmed by stashing src and watching `Mixed(r.witness[0])` raise `RangeDefect` (real domain 5..7, engine said 0..2). R19: new `feEnumOrdinalUnresolved` degrade rather than the provably-wrong positional guess. R23: hard macro-time `error()` at the single site. **Agent caught and fixed a regression it introduced itself** (first R19 attempt degraded every non-enum symbol reaching the general `nnkSym` arm; the neighbour suites caught it, bisected with `git stash`). |

**Verdict-affecting and owed the next central bump:** R18 (tuple-valued enum
domains and constants), W8 + R8 (in flight), R7 (in flight).
| R7/R13 | `24b9da6` | Statement-position `{.symexTransparent.}` now gated on `isInertOpaqueCall`; a non-inert callee falls through to opaque handling, which taints — fails SAFE (`sxUnsat` -> `sxUnknown`). New `feTransparentArgNotInert` degrade names the broken promise, because the generic opaque message tells the user to apply the pragma they already applied. Doc comment corrected: it had claimed "an over-claimed pragma costs precision, never soundness", which was false until this fix. Agent caught its own flawed ref-arg test (trivially satisfiable pre-fix) and redesigned before trusting the RED. |
| R8 | `a47852e` | New `clampWitnessFieldsDeep` walks a field's TYPE the same way `extractFromSymVal` walks the matching VALUE, so nested dotted keys match the extraction's own convention. RED deterministic across two runs: `value out of range: 0 notin 10 .. 20`, raised inside `symexFind` while building the witness. |
| W8 | `bf6de33` | **UNPINNED — landed on consistency grounds, honestly labelled.** Instrumentation finally explained two prior failed attempts: `bvRangeConds` dispatches on `v.kind` and silently returns `@[]` for `svInt`, which is exactly what the `isIntOffset` arms allocate — so the "obvious" one-line fix would have compiled and done NOTHING. Required extending `rangeCondsIfNeeded` with an `svInt` branch (Z3Int comparisons). Both scan shapes reaching these arms still hang on Linux/podman (reconfirmed, 2 cycles); the one terminating shape never reaches the path. No test is registered for it anywhere. |

**Process:** `git stash` proved unsafe with concurrent agents — one lost staged
content, another disturbed a sibling's uncommitted `runtime.nim`. Switched to
isolated worktrees for A/B. Recorded as a memory.
| R16 | `9e48761` | New `concolicScalarPromotesSoundly` — shares `promoteSound`'s core argument (unsigned never promotes; narrow signed only with a range fitting the BV window) but carves out width-64 signed. Justified: `promoteSound`'s extra "proven range even for plain int" requirement exists to bound `wmExplore`'s fork cost, not for soundness, and reusing it literally would push every existing concolic test onto BV for no gain. RED was a three-way disagreement (oracle vs `wmExplore` vs `wmFollowConcrete`) on both uint8 wrap and int8 overflow; plain `int` agreed pre-fix and is untouched. |

### New findings from round 4 (reported by fixing agents; all closed in round 8)

Status column reconciled in round 10 — R24/R25/R26 read `open` here long after
`9d1d8e3` closed them, which is the exact bookkeeping rot the standing lenses
caught three separate times this session. The closure records are further down,
in the round-8 fix table.

| id | sev | status | file:line | finding |
|----|-----|--------|-----------|---------|
| R24 | Medium | fixed `9d1d8e3` | `runtime.nim` `runConcolicFlipImpl` / `materializeConcolicModel` | G2 flip reads a solved value off `drawVars[i].zi`, but a param R16 now binds as BV has `env[p.name]` as a FRESH BV pinned by concrete equality, deliberately never bridged to `.zi` (avoiding the `int2bv`/`bv2int` non-termination hazard this codebase flags elsewhere). A flip targeting a branch over such a param solves the wrong variable and reads back an uninformative draw. **R16 widened the set of params this applies to.** No test exercises `concolicFlip` on a non-`int` scalar, so nothing regresses today. |
| R25 | Low | fixed `9d1d8e3` | `runtime.nim`, `cbTransformLinked` BV branch | Concretizes rather than staying symbolic (same int2bv avoidance), sacrificing flip-ability for that param. Unexercised — `tsymex_g6_transform_binding.nim` uses plain `int`. |
| R26 | Medium | fixed `9d1d8e3` | `runtime.nim`, concolic Z3Int binding | A concolic-bound signed param on the Z3Int route carries no `ziWidth`/`ziSigned` stamp, so `overflowCondInt`'s raise obligation never fires on a concolic path at ANY width. Pre-existing #161 gap, out of R16's scope (`ConcolicCollectResult` has no raised-verdict channel to expose it anyway). Documented in code and in the suite header. |
| R9 | `b13d484` | Concolic counter now unions BOTH degrade sinks, each deduped in its own `HashSet` — deliberately matching `runSymexImpl`'s existing per-sink rule so the two drivers agree. RED: a `cmpString` lowering degrade (no `WalkCtx` in scope, threadvar-only) read `walkDegradeCount == 0`, indistinguishable from clean. |
| R10 | `d3fc8c2` | New `feTransparentResultUsed` for the expression-position over-claim route, extending R7's parse-time mechanism rather than adding a parallel one. Message names the real cause (statement-position-only) instead of advising the pragma the caller already applied. |
| R12 | `06335b2` | Pure `discriminatorDomain*(ty)` — dropped the suggested `hasElse` param since `VariantArm.isElse` is already on `ty.vArms`, collapsing a third duplication where both callers re-derived it. Agent VERIFIED the two builders were genuinely equivalent (Nim's case-exhaustiveness guarantees the explicit `of` ordinals equal the full tag set when there is no `else`) rather than assuming. Behavior-neutral. |
| R14/R20/R21 | `960da7b` | Characterization tests, **all passed first try** — no hidden bug behind any of the gaps. R21: array element, seq element and enum-typed discriminator all behave as the covered top-level-param case. R20: `isExact` and `isOptimised` agree on negative-ordinal enums (the newly-reachable `promoteSound` route). R14: non-zero and NEGATIVE range floors pinned (`lo` reachable, `lo-1` not); all seven untested inert-allowlist exclusions still degrade; whole-program wrap-scan ban confirmed not per-variable; opaque-after-target asymmetry recorded. Found a language boundary, not an engine gap: Nim rejects a negative-ordinal discriminator outright. |
| R22 | `e09a286` | New `forkAssignRangeCheck`: an out-of-range assignment into a ranged LOCAL now forks a `RangeDefect` raise and narrows the survivor, discharging provably-in-range cases against `#161`'s `ziIvl` interval machinery first (measured ~33ms vs ~716ms on a 20-deep redundant chain). Scoped to the local-variable site by instruction. **Remaining sites, not covered:** plain object field write through a ref; variant arm field write through a ref; seq/array element write; `var`/`out` parameter reassignment (not populated by `isLet`). |

**Ledger-truth note:** the round-5 liveness lens caught this R22 row still reading
`open` after `e09a286` had fixed it — the same regressed-invariant class these
lenses exist to police, in my own bookkeeping. Corrected here.

## Round 5 (re-review of round 4) — one High, introduced by round 4 itself

Two lenses (correctness; security+liveness) plus an adversarial verifier.

**W8's risk question, answered and closed.** W8 extended the SHARED
`rangeCondsIfNeeded` with an `svInt` branch while being itself unpinned — the
worry was that ten other sites now calling that helper might silently change
verdicts. They cannot: every one of those sites reaches the helper through
`bvVar` / `liftBV` / `heapSelect`, all of which produce BV kinds for `itInt`,
so the `svInt` arm is unreachable there. It fires only at W8's own two arms
and at R22's `forkAssignRangeCheck`. Usefully, that means W8's shared code IS
exercised — `assignOutOfRange`'s `range[0..100]` params promote to `svInt`
under the default `isOptimised`, so R22's suite drives the branch even though
W8's own site stays dark.

| id | sev | status | file:line | finding |
|----|-----|--------|-----------|---------|
| R27 | High | fixed `ccb3334` | `runtime.nim:7693` (field), `:9365-9368` (isLet), `:9415` (isAssign) | **R22's `localRangeTypes` is keyed by bare source name on a walk-global `WalkCtx`, while `Env` is per-`Path`.** `isLet` inserts for a ranged local and DELETES for a same-named non-ranged one, with no scope check; `walk` shares one `w` across `isIf` arms, across `walkBlock` statements, and into inlined callee bodies (`pushFrame`/`popFrame` save only `w.frame`). Direction 1: a sibling-branch shadow deletes the entry, so a later assignment to the OUTER ranged local skips the check silently — no fork, no degrade — a false `sxSat`. Direction 2: a callee's ranged local survives `popFrame`, so a caller's unrelated same-named variable is checked against a stale range and Z3 satisfies `not inRangeCond` — a phantom `sxRaised`. Short shared names across inlining (`i`, `n`, `x`, `result`) make this ordinary. **Introduced by round 4.** |

**The repo had already solved this.** `dsl_parser.nim:5964-6000` (the N28 fix)
documents the identical hazard — "a nested-scope SHADOW local sharing a
formal's printed name collides both ways" — and resolves it by true symbol
identity (`sameSym`/`containsSym`) instead of flattened names. It was applied
to the int-offset collector's `HashSet[string]` and never to this table. The
preferred remedy is therefore the established one: attach the declared
`IRType` to `isAssign` at parse time by symbol identity and delete the
walk-time table, rather than scoping the table.

**Also from round 5, not defects:** `maxFrontierSize` defaults to 0 =
unbounded, and R22's `ziIvl` discharge is defeated whenever the RHS involves
any unconstrained value (`ziIvl` is `none` for anything not built from
`bAdd`/`bSub`/`bMul` of interval-carrying operands), so a ranged loop counter
forks per iteration. Not a new exhaustion class, but R22 widens an existing
one onto a common Nim idiom. Recorded, not fixed. And the three new
`SymexErrorKind` members reach the user on every `symexFind` verdict branch
but NOT through `concolicCollect`, which never reads `prog.parseErrors` at all
— a pre-existing structural gap in that API surface, not introduced here.

**R27 fixed, `ccb3334`** — took the deeper shape: `IRStmt.isAssign` gained
`aty`, resolved at PARSE time via `classifyType`/`getTypeInst` on the target's
true `nnkSym`, and `WalkCtx.localRangeTypes` is deleted. Both RED directions
confirmed deterministic before the fix (direction 2 required the caller's `v`
to be a FORMAL — an `isLet`-declared same-named local would itself clear the
stale entry and mask the bug). Round-trip and canonicalization both verified
with quoted evidence: `emitStmt` emits `mkAssign(..., emitIRType(s.aty))`
(`dsl_parser.nim:576-578`, with a new `nil` guard at `:369-374`) and
`canonicalize`'s `isAssign` arm renders `;aty=`. Other `mkAssign` call sites
(seq/table/string rebinds, synthesized loop counters) pass `nil` unchanged —
their receivers are never `itInt`. No collision hazard of this class remains.

Walker bumped **136 -> 137** for R27: `aty` is a new semantic `IRStmt` field
participating in the cache key, and both directions were verdict changes.

## Round 6 (re-review of R27) — clean, plus one narrowing caught

Two lenses. All four correctness verdicts affirmative: `aty` round-trips
through `emitStmt` for every shape, canonicalization is complete and
unambiguous (`canonicalize(IRType)` renders `"Ty<nil>"` distinctly, no
separator clash with the `;aty=` rider), the 136->137 bump is sufficient, and
both R27 directions are STRUCTURALLY closed — `grep localRangeTypes` finds
only doc comments, no live read or write of any name-keyed table remains.
Security clean. Liveness confirmed R27's test uses the required FORMAL-
parameter shape for direction 2 (an `isLet`-declared same-named local would
have cleared the stale entry and masked the bug). Ledger audit clean,
including the six retroactive `open` -> `fixed` corrections.

| id | sev | status | file:line | finding |
|----|-----|--------|-----------|---------|
| R28 | Medium | fixed `663759f` | `dsl_parser.nim` scan recognizers (~5125, ~5294, ~5303, ~5514, ~5523) | **R27 narrowed coverage.** Three scan-idiom recognizers synthesize a closed form and call `mkAssign` directly, bypassing the dispatch R27 wired `aty` into, so the closed-form counter write carried `aty = nil`. Under R22's flat name-keyed table these HAD been covered — the lookup was oblivious to the producing call site. B6 unaffected (re-parses through the ordinary path). |

**R28's fix needed a prerequisite nobody predicted.** Instrumentation showed
the recognizers could not match a ranged counter's loop AT ALL: Nim wraps a
`range[lo..hi]` counter in `nnkHiddenStdConv` at every plain-`int` use, while
the shape matchers required a bare `nnkSym`. The loop fell through to
unrecognized before the `aty` gap could matter — so the `aty` fix alone would
have been DEAD CODE. R28 also applies `unwrapHidden` in the three matchers'
counter extraction and in `counterAdvancesByOne`'s `<i> = <i> + 1` branch
(its `inc <i>` sibling already did it). Does not widen recognition; lets an
already-intended ranged counter reach the existing gate. Five scan suites run
green (`tsymex_q1_scanlift`, `tsymex_retest_c6_tuple_chain`,
`tsymex_r6_b4_readcstring`, plus `tsymex_r2_scanbound` and
`tsymex_r6_b5_chained` as insurance, since the unwrap touches shared helpers).

Walker bumped **137 -> 138** for R28.

## Round 7 (re-review of R28) — no High

`unwrapHidden` verified identity-preserving: it strips only
`nnkHiddenDeref`/`nnkHiddenAddr`/`nnkHiddenStdConv`
(`dsl_parser.nim:4848-4868`), excludes `nnkConv` and calls, and `sameSym`
still requires true `nnkSym` binding identity — so peeling a passthrough
wrapper cannot turn a different variable into a false match. A wrongly
recognized loop would be the serious failure here (its real semantics get
replaced by a synthesized closed form), and that is ruled out. B6 confirmed
untouched: no direct `mkAssign`, does not consume `counterAdvancesByOne`.
The six new `aty` sites match R27's shape and gating. Bump correct.

| id | sev | status | finding |
|----|-----|--------|---------|
| R29 | Medium | **resolved empirically, inert** | Idiom 1's bracket-index identity check (`tryMatchScanIdiomShape`, `dsl_parser.nim:5019`) is NOT unwrapped, while the structurally identical checks in idioms 2 and 3 are (`:5241`, `:5420`, both predating R28). If live this would block recognition for a ranged counter and silently fall back to the hang-prone k-unroll path, making R28's idiom-1 fix dead code. **Settled by the sweep:** `tsymex_163rev_scan_counter_range` passes (exit 0), and its idiom-1 case asserts a POSITIVE `sxRaised(RangeDefect)` — which cannot pass unless idiom 1 is recognized AND carries `aty`. Bracket indexing is compiler magic accepting any Ordinal, so no `nnkHiddenStdConv` is inserted there, unlike the generic `<`. Worth a one-line comment recording why idiom 1 needs no peel; no code change owed. |
| R30 | Low | fixed `4e01f98` | `inc`/`dec`'s `aty` gate (`dsl_parser.nim:8031`) tests `hasRange` without the `itInt` check its five siblings use. Functionally equivalent (a `hasRange` type always classifies `itInt` here), cosmetic, predates R28. |

---

# Current state — /code-review, end of round 7

**Stage:** review loop complete through round 7. Every finding raised across
seven rounds is closed, pinned, or explicitly recorded as deferred with a
reason. The last gate — the full-suite sweep — was at 424/473 when this was
written; read its result before trusting any completion claim.

**Branch:** `rfc-161-163-symex-defects`, HEAD `e1a6b57`. **NOT PUSHED.** The
last push was `26418f3`; everything since is local. CI has seen none of it.

**Walker:** 134 -> **138**, in four bumps, one per round of verdict changes
(135 round 1, 136 round 4, 137 round 5, 138 round 6). Each bump's doc comment
in `canonicalize.nim` names the findings it covers and their verdict
directions, and states what was deliberately NOT bumped for and why.

**Rounds:** 1 (13 findings) -> 2 (R17 + six deferred) -> 3 (clean) ->
4 (the deferred set + R11 abstraction, by Corey's direction) -> 5 (R27, a
High introduced by round 4) -> 6 (R28, a narrowing introduced by R27) ->
7 (clean; R29 settled empirically).

**Resume commands:**

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -30
tail -40 /home/corey/.claude/jobs/4fd5573d/tmp/sweepr6.out    # final gate
grep -c . /home/corey/.claude/jobs/4fd5573d/tmp/cur163r6.log  # progress /473
scripts/sweep-diff.sh /home/corey/.claude/jobs/4fd5573d/tmp/base163.log \
                      /home/corey/.claude/jobs/4fd5573d/tmp/cur163r6.log
```

Baseline is the same `base163.log` (460 entries, pinned worktree at
`ac507c1`) every gate this session has used. `tsymex_snd3_loopdegrade`
(exit 137, timeout) is byte-identical in that baseline — pre-existing, not a
regression.

**Open forks, all Corey's:**

1. **Push?** ~25 unpushed commits across four review rounds.
2. **`wiring = proven`?** Still withheld. W8 is closed but UNPINNED, and
   R24/R25/R26/R29/R30 plus R22's four uncovered assignment sites remain.
3. **File the unfiled defects?** Now eleven: the five from the #163 work,
   R22's remainder, `nnkHiddenCallConv` (`echo(intExpr)` fails to parse),
   R24, R25, R26, and `maxFrontierSize` defaulting to unbounded.
4. **A lint gate for the R11 invariant?** R11's own agent noted the helpers
   make the obligation cheap and obvious but nothing MECHANICALLY forces a
   new materialization site to call them. This bug family has now recurred
   six times (W2, W4, R3, R4, R17, W8). A grep-based CI check would end it.

## Final gate — the sweep found a real regression, and a phantom

`unchanged=459 regressed=1 new-failing=0 new-ok=24 gone=0`, plus
`unregistered=2 missing=2` in the drift (missing had been 0 all session).
Both investigated; neither was a soundness problem, and both are now closed.

| id | sev | status | finding |
|----|-----|--------|---------|
| R31 | Medium | fixed `<this commit>` | **`tsymex_r6_n36_raise_class_audit` regressed (0 -> 1).** It is a SOURCE-SCANNING audit that pins exact inventory counts of marked raw-`raise` sites in the engine's hazard zone. Round 4's R16 added exactly one new site — `runtime.nim`'s `bvEqConst`, reached when concolic scalars began binding as BV. It is correctly marked `[raise-audited: category-c: BV-only call sites (runConcolicCollectImpl's own useBV guard pre-selects a BV kind)]`, i.e. unreachable from a live path. The trip-wire did its job: it demanded adjudication of an inventory change rather than flagging an unmarked hazard. Counts moved 75 -> 76 and 78 -> 79 with the reasoning recorded in the test, not silently. Suite now 14/14 green, verified directly. |
| R32 | Low | fixed `<this commit>` | **The drift report's two "registered but MISSING on disk" entries were phantoms** — `alpha` and `value must be >= 0`. `scripts/sweep.sh` extracted registered suite names by grepping quoted strings out of `nelli.nimble`'s `test` task WITHOUT stripping comments, so two explanatory comments this round added (`# a = (1, "alpha")`, `# ... "value must be >= 0" ...`) were scraped as suite names. Fixed at the source — the extractor now strips `#` comments before matching — and the two comments were de-quoted as well. Verified: 482 registered, 0 phantoms, 0 missing. Worth noting the drift file's own header says it is "generated and therefore cannot lie"; it could, and did. |

**Gate status, stated precisely.** The full 484-entry sweep completed against
the same `ac507c1` baseline every gate this session used. It reported ONE
regression; that suite is now fixed and verified green in isolation (14/14).
The three files changed after the sweep — the audit test's count constants,
two `nelli.nimble` comments, and `scripts/sweep.sh`'s drift extractor —
cannot affect any other suite's result: no product source was touched. So
the effective gate is `unchanged=459 regressed=0 new-ok=24`, with the caveat
stated plainly rather than claiming a clean full run I did not re-execute.
`tsymex_snd3_loopdegrade` (exit 137, timeout) remains byte-identical in the
baseline — pre-existing, not a regression.

---

# Round 8 — the "fix everything" sweep

Corey's correction: *"I told you to fix everything why are there still
witheld and open things and things you're trying to file instead of
fixing?"* — correct, and the narrowing was mine. Round 7 closed the
review's own findings and then reclassified the remainder as filing
material and a withheld flag. Three categories were choices, not blockers:
open findings I recommended filing (R24/R25/R26/R30), R22's four
un-attempted assignment sites, and the unfiled engine defects found
during the review. W8's pin I called blocked, but R28 had since made
terminating scan-shaped SUTs writable. `wiring = proven` follows from the
rest closing; it was never a separate judgement.

## Landed this round

| finding | commit | note |
|---|---|---|
| R11 lint gate | `25740b0` | `tests/tsymex_r11_range_invariant_audit.nim` — source-scanning audit over `runtime.nim` + its five `include`d siblings, pinning direct calls to the RAW primitives (`bvRangeConds`, `clampToDeclaredRange`) that the R11 helpers wrap. Both primitives are module-private, so that file list is EXHAUSTIVE, not heuristic. Pins 8 sites (1 `bvRangeConds`, 7 `clampToDeclaredRange`), has a two-way self-test so the scanner cannot rot, and documents the six-instance history (W2/W4/R3/R4/R17/W8) so the next person to trip it understands why it exists. Deliberately narrow: it does NOT try to prove "this materialisation site's caller eventually calls the helper" — that needs control flow a text scan lacks. **It went red on its first live test**, catching two new unmarked `bvRangeConds` calls a concurrent agent had written into `runConcolicCollectImpl`. |
| `nnkHiddenCallConv` | `b307aef` | `echo(intExpr)` failed to parse AT ALL (`feUnsupportedExprKind ... nnkHiddenCallConv`) — any SUT echoing a non-string was unanalysable. Fixed by reusing the existing `$`-conversion lowering (`iekIntToStr`/`iekRuneToStr`), NOT a blind unwrap: the result sits in a string-typed slot and unwrapping to the bare int would corrupt the sort. **This revalidates R1's original repro**, which had to be retracted for not parsing: the new suite asserts `echo(a div b)` and confirms the `DivByZeroDefect` inside the echoed expression still forks. |
| char-range comparison | `b307aef` | `c > 'm'` for `c: range['a'..'z']` failed to parse (`nnkHiddenSubConv`; the int-range analogue uses the already-handled `nnkHiddenStdConv`). Joined to the blind-passthrough arm — sound because a subrange shares its base type's representation — WITH a domain-preservation test proving the unwrap does not bypass the range constraint (`c > 'z'` stays `sxUnsat`). |
| R30 | `4e01f98` | `inc`/`dec`'s `aty` gate now matches its five siblings (`itInt and hasRange`). Consistency only. |
| R29 | `3dcde1d` | Comment recording why scan idiom 1 needs no hidden-conv peel: Nim's `[]` is compiler magic over any Ordinal, unlike the generic `<`. |

## Coordination owed

The R11 audit will go RED the moment the concolic agent (R24/R25/R26)
commits, because of its two new `bvRangeConds` calls in
`runConcolicCollectImpl`. Adjudicate them the way the raise audit's
75->76 was adjudicated — inspect, then either an inline
`# [range-invariant: <reason>]` marker or an `allowedSites` entry plus
bumping the pinned `bvRangeConds` count 1 -> 3. Do NOT just re-count.

## Still in flight

- R24/R25/R26 — the concolic/fuzzer-path gaps.
- W8's pin, fourth attempt, using R28's terminating scan technique.

## Still queued (this round is not finished)

On `runtime.nim`, after the concolic agent lands:
- **R22's four remaining assignment sites** — plain object field write through
  a ref, variant arm field write through a ref, seq/array element write,
  `var`/`out` parameter reassignment (the last is not populated by `isLet`, a
  distinct plumbing gap).
- **`maxFrontierSize` defaults to 0 = unbounded** (`types.nim:1903`), which is
  what lets R22's fork multiplicity accumulate on a ranged loop counter.
- **module-global read** reports `weInternalWalkerFault` with a raw `KeyError`
  instead of a classified degrade.
- **`maxCallDepth` bail** still degrades unclassified.
- **enum field witness COMPILE failure** (`symex.nim`) — `symexFind` fails to
  compile for a proc taking an object with a plain enum field, because the
  witness reader emits `readUInt8`/`readUInt16` which Nim will not implicitly
  convert into the enum-typed field. This also unblocks R21's untested
  object-field position.
- **un-suffixed int literal above `int32.high`** defaults to `int64`.

Then: a final central version bump covering every verdict-affecting fix of
this round, a re-review, the final sweep, and `wiring = proven`.

**Resume:**

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -40
grep -c "^| R" docs/issue-0163-opaque-call-taint.handoff.md
scripts/sweep.sh <out>.log && scripts/sweep-diff.sh \
  /home/corey/.claude/jobs/4fd5573d/tmp/base163.log <out>.log
```

Baseline remains `base163.log` (460 entries, pinned worktree at `ac507c1`).

## Round 8 progress — the queue is nearly empty

| item | commit(s) | note |
|---|---|---|
| **W8 PINNED** | `bd6a013` | Fourth attempt, and it corrects the round-1 characterisation. W8 was called "a precision gap on an internal representation; no crash, no wrong verdict." **Wrong.** The pre-fix RED did not fail an assertion — it HUNG and was killed at the 300s bound. The range assertion is load-bearing for TERMINATION: without it Z3 reasons through the full call's Sequence-theory equality instead of short-circuiting on a trivial `p > 1000` vs `p in [0,1000]` contradiction. The blocker that defeated three prior attempts also dissolved on its own: scan-shape non-termination no longer reproduces on current HEAD, because R22/R27/R28 landed in between. Instrumentation confirmed B3 fires the bare arm, B4 the tuple arm, both `hasRange=true`, both terminating in seconds. |
| R24/R25/R26 | `9d1d8e3` | New `ConcolicCollectResult.drawOverrides` so the flip solves the variable the binding actually used — option (a), no `int2bv` bridge. R24 RED: a `uint8` flip materialised `int(0)` instead of `int(201)`. R26: `ziWidth`/`ziSigned` now stamped on concolic Z3Int params, verified by reading `obligationLog` directly (empty pre-fix, `odLive` post). R26's obligation is confirmed NOT observable through `ConcolicCollectResult`/`ConcolicFlipResult` — no raised-verdict channel exists; wiring one needs `fuzz.nim` orchestrator work. Recorded, not silently implied. |
| R11 audit's first live catch | `aad62dd` | The gate went red on a real change within minutes of existing. **Adjudicated, not re-counted:** R24/R25's two new `bvRangeConds` calls bound a BV against the concolic TRACE node's recorded per-draw interval (`node.intC.min/max`), NOT the type's declared range, so `rangeCondsIfNeeded` (which reads `ty.rangeLo`/`ty.rangeHi`) is the wrong helper by construction. Both call lines carry an inline `# [range-invariant: concolic-trace-interval]` marker (the scanner checks the CALL LINE only, not preceding lines — learned the hard way), inventory 1 -> 3, and the test title updated so it does not misdescribe its own assertion. |
| **R22 fully closed** | `bf403e8` `5322221` `37618d0` `895b312` `404df8d` | All four remaining sites. **Site 4 needed NO code change** — R27's parse-time `aty` resolution is indifferent to whether the target symbol came from an `isLet`, a `var` local, or a formal, so `var`/`out` param reassignment was already covered. Round 5's deeper fix paid an unanticipated dividend. **And building site 3's precision test found a pre-existing crash:** `storeSeqElem`'s `itInt` arm read `val.bv8/16/32/64` with no `svInt` handling, so under the DEFAULT `isOptimised` semantics — where a ranged param promotes to `svInt` for #161's machinery — writing that value into ANY int-family seq element crashed the walker (`weInternalWalkerFault`), ranged or not. Fixed with its own RED (`37618d0`). Cost checked after every site; no blow-ups. Both audits stayed clean with no adjudication needed. |
| enum-field witness reader | `d71da9e` | `symexFind` could not COMPILE for a proc taking an object with a plain enum field. This also unblocks R21's untested object-field position, so R2's and R18's enum-domain work is finally verifiable there. |
| hidden widening conversion | `678c6ce` | The int-literal-width item, which reproduced as a hidden widening conversion losing its operand's real width. |
| `maxFrontierSize` default | `991b0ff` | Was 0 = unbounded, the one incremental per-statement cap; it is what let R22's fork multiplicity accumulate on a ranged loop counter. |

## Still in flight

- The two raw-degrade classifications: module-global read (currently
  `weInternalWalkerFault` + a raw `KeyError`) and the `maxCallDepth` bail
  (currently unclassified). **The first is not cosmetic** — #163 slice 4's
  inertness soundness argument rests on "a SUT reading a global has already
  degraded at its own read site", which is only trustworthy if that degrade
  is a real classified decline rather than an env-lookup miss escaping as an
  engine fault.
- The enum/types/symex agent's own final report (its three commits are in).

## Then, to close round 8

1. One consolidated `symexWalkerVersion` bump (138 -> 139) covering every
   verdict-affecting fix of this round: R22's sites 1-3, the `storeSeqElem`
   prerequisite, both parser gaps (`b307aef`), R24/R25/R26, the enum-field
   witness reader, the widening-conversion fix. Update the CR2 `==` pin and
   raise the floor pins in the suites whose behaviour depends on round-8
   semantics. Several test comments were corrected to say a bump IS owed
   (`908b786`) — do not re-derive that.
2. A re-review round over `a581225..HEAD` (standing security, design,
   liveness lenses).
3. The full sweep against `base163.log` (460 entries, pinned at `ac507c1`).
4. `wiring = proven` — a consequence of the above, not a separate judgement.
   `quipu` is not on PATH but DOES run as a git hook here, so find the
   invocation the hook uses rather than assuming it is unavailable.

**Resume:**

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -45
scripts/sweep.sh <out>.log && scripts/sweep-diff.sh \
  /home/corey/.claude/jobs/4fd5573d/tmp/base163.log <out>.log
scripts/dt-bounded.sh c tests/tsymex_r11_range_invariant_audit.nim 300
scripts/dt-bounded.sh c tests/tsymex_r6_n36_raise_class_audit.nim 300
```

Both audits are now permanent gates and will fire on any future range-primitive
or raw-raise change — that is the point. Adjudicate, never re-count.

## Round 8 — the last three items

| item | commit | note |
|---|---|---|
| int-literal width | `678c6ce` | **Far worse than my own note said.** I had recorded it as "un-suffixed int literal above `int32.high` defaults to `int64`" — a vague width remark. It is a FALSE-SAT SOUNDNESS BUG: `proc f(a: int32) = (if a > 3_000_000_000: symexTarget("hit"))` is unsatisfiable for every `int32`, and `symexFind` returned `sxSat` with witness `a = -1294967295` — the literal truncated into the narrow width and wrapped negative. Real Nim inserts a widening `nnkHiddenStdConv` which the engine was not honouring. Fixed by routing genuine width changes through the existing `mkConvIntWidth` machinery; same-width hidden conversions (subrange strip, `nnkHiddenAddr`) untouched. |
| enum-field witness | `d71da9e` | `IRType` gained `enumName*`, populated by `classifyType`'s enum arm, consumed by `emitTyAndReader` to wrap the raw reader as `EnumName(...)`. Round-trips via a new `withEnumName` in `emitIRType`; canonicalized as `:e[...]` by default (mirroring `itTuple.objectName`); excluded from `IRType.==` (mirroring `nominalId` — the walker never reads the name). **Unblocks R21's object-field position**, so R2's and R18's enum-domain work is finally verifiable there, including negative-ordinal and sparse enums as object fields. Also corrected a collateral test that assumed a raw-int witness; it is now honestly typed. |
| `maxFrontierSize` | `991b0ff` | Measured, not guessed: instrumented `walkBlock` across ~20 heavy/branchy suites, largest observed frontier **16** (`tsymex_r6_n9_variant_budget`). Default set to **256** — 16x headroom, matching a precedent value already used in `tsymex_phase7_assertcovered`. `0` remains the documented opt-out. The existing prune already degrades honestly via `beBudgetExhausted`; no change needed there. |
| `maxCallDepth` classified | `0c85a13` | Was an unclassified degrade — `sxUnknown` with no named reason, so "raise your call-depth budget" was indistinguishable from "the engine cannot model your program". `beBudgetExhausted` already existed and fit exactly (same family as the `maxLoopUnwind`/`maxFrontierSize` uses), so no new enum member. Message now names `maxCallDepth=N` and the remedy. NOT verdict-affecting: the `sxUnknown` already happened; only the kind riding it changed. |
| module-global read | `7182801` | Diagnosed and RED-confirmed: `lower`'s `iekVar` arm does a bare `env[e.vname]`, so an unbound name lets Nim's `Table` throw `KeyError`, which escapes as `weInternalWalkerFault` — the engine's "I have a bug" backstop — for what is actually an unmodelled-feature decline. The first attempt was blocked because `types.nim` was sibling-owned; it is free now and the fix is in flight with `feGlobalReadUnmodelled` appended at the enum tail. |

## New fact worth recording

`tests/tsymex_snd3_loopdegrade.nim` **hangs past 300s on unmodified HEAD** and
is NOT one of the six documented `tsymex_r6_*` Linux hangers. This is the
exit-137 entry every sweep this session has reported and that I repeatedly
characterised as a "pre-existing failure, byte-identical in the baseline" —
accurate as far as it went, but it is specifically an undocumented HANG, which
belongs in the same ledger as the six known ones.

## Round 8 closed

- **module-global read** `7182801` — landed. Note the implementing agent
  DECLINED the implementation this brief specified. I said to raise
  `SymexClassifiedDegradeError` at the `iekVar` site, matching the nearest
  textual precedent. It checked where that precedent actually sits: every
  remaining raw `raise` in `runtime.nim` is verified-unreachable, at the
  pre-walk param boundary, or caught one frame away. `iekVar` is none of
  those — it fires inside `lower()`'s own recursion on every ordinary global
  read, arbitrarily deep. A raw `raise` unwinding through nested `walkBlock`
  frames is silently swallowed by the C-backend goto-exception unwind (the
  documented N31/N36 class), leaving `sawUnknown` unset and enabling a FALSE
  `sxUnsat`. Following my brief would have reintroduced that bug class for
  global reads. It used the `loweringDegradeErrors` threadvar sink instead,
  added no `raise`, and both audits stayed green unchanged.
- **Consolidated bump 138 -> 139** `0f16e47` — landed, covering R22 sites 1-3,
  `storeSeqElem`, the widening-conversion false SAT, both parse gaps,
  R24/R25/R26, the enum-field witness reader (a new canonicalized `IRType`
  field, which mandates a bump on its own) and `maxFrontierSize`'s default.
  NOT bumped for the `maxCallDepth` classification or the module-global
  decline — both attribution-only.
- Seven round-8-dependent suites raised to a `>= 139` floor; earlier suites
  keep the floor their own behaviour requires.

## Round 9 (re-review of round 8) — no findings above Low

Security and liveness both clean. Two corrections it made to MY framing:
- The fork-multiplication worry I carried through several briefs does not
  hold. `forkAssignRangeCheck` takes one input `Path` and returns exactly one
  survivor; the out-of-range sub-path is terminal via `discard routeRaise`.
  A ranged assignment in a loop NARROWS the same path's `pc` each iteration,
  it does not double the frontier. Real multiplicative growth comes from
  ordinary `if`/`case` forks, pre-existing and already bounded.
- `maxFrontierSize`'s prune always sets `sawUnknown` and records
  `beBudgetExhausted`, so it cannot yield a truncated `sxUnsat` — the failure
  mode I was most worried about.

R21's object-field position is confirmed genuinely unblocked end-to-end:
the new suite runs `symexFind` on objects with negative-ordinal and sparse
enum fields and replays the witness, rather than checking the classifier.

## Remaining to close

1. ~~Consolidated bump **138 -> 139**~~ DONE (`0f16e47`) covering the verdict-affecting set: R22
   sites 1-3 + the `storeSeqElem` prerequisite, both parser gaps (`b307aef`),
   R24/R25/R26, the enum-field witness reader, the widening-conversion
   soundness fix, `maxFrontierSize`'s default, and the module-global decline if
   its agent judges it verdict-affecting. Move the CR2 `==` pin and raise floor
   pins in the round-8-dependent suites. Test comments were already corrected
   to say a bump IS owed (`908b786`) — do not re-derive.
2. Re-review over `a581225..HEAD` (standing security, design, liveness).
3. Full sweep vs `base163.log` (460 entries, pinned at `ac507c1`).
4. `wiring = proven`. `quipu` is not on PATH but DOES run as a git hook here —
   find the hook's invocation rather than assuming it is unavailable.

## Round 9 findings — two, both against round 8

Correctness/cache-key lens verified the highest-consequence items clean:
`enumName` round-trips for all four enum positions (they all route through the
same `classifyType`), is canonicalized as `:e[...]`, and is correctly excluded
from `IRType.==` on the same precedent that already excludes `hasRange`.
`maxFrontierSize` cannot yield a truncated `sxUnsat` — the prune sets
`sawUnknown` and records `beBudgetExhausted` before truncating. R22's three
new sites are consistent with the original. The widening fix never injects a
conversion where none belongs.

| id | sev | status | finding |
|----|-----|--------|---------|
| P2 | High | fixed `c74c04b` | **The widening-conversion fix is narrower than its own commit message claimed.** It engages `mkConvIntWidth` only when BOTH sides pass `isIntFamilyName` — a closed set of plain int spellings (`int`, `int8..64`, `uint`, `uint8..64`, `byte`, `char`). `valueTypeName` reads `getTypeInst`, which for a NAMED range alias or an enum reports that alias/enum name, so the gate fails and the code falls back to the old blind pass-through. Traced consequence: no `iekConvIntWidth` is inserted, `probeProto` returns the operand's native narrow width, and `coerceIntLit` truncates the oversized literal mod 2^n — the identical false SAT, for a different declared-type spelling. Proposed repro: `type SmallCount = range[0'i32..100]; proc f(a: SmallCount) = (if a > 3_000_000_000: symexTarget("hit"))`. **Not a regression** (the pre-round-8 pass-through was equally broken), but I asserted the class was closed and it is not. In flight: verify by experiment first (the lens could not compile), fix by reusing `rangeBaseType`/`enumOrdBitsNeeded` rather than a second name-based rule, and correct the v139 doc claim either way. |
| P6 | Medium | fixed `7405283` | **My bump rationale contradicted itself.** v139's doc listed the module-global decline among changes NOT warranting a bump ("pure error attribution — the `sxUnknown` already happened") while the same comment explained that the raw `raise` it replaced "would have left `sawUnknown` unset and enabled a false `sxUnsat`". Both cannot hold. The old code was a bare `env[e.vname]`, which RAISES; the fix changes control flow to close that N31/N36-class false-`sxUnsat` hazard, which is verdict-affecting by definition. Harmless in practice — the 138->139 bump covers it anyway — but had it shipped alone the stated reasoning would have shipped a verdict-changing fix unbumped, which is the exact failure this protocol exists to catch. The `maxCallDepth` exclusion stands: it adds a message beside an already-present `sawUnknown`. |

**Pattern worth naming:** round 9 is the third time this session a lens caught
a stale or wrong CLAIM in my bookkeeping rather than a defect in the code — the
`open`-after-landing row, the "no bump owed" comments, and now a
self-contradictory bump rationale. The code has held up better than the record
of it.

## Remaining to close

1. P2: confirm-or-refute by experiment, fix if real, correct the v139 claim.
2. If P2 lands a fix, bump 139 -> 140.
3. Full sweep vs `base163.log` (460 entries, pinned at `ac507c1`).
4. `wiring = proven`.

## P2 resolved — and the repro I proposed was wrong

`c74c04b`. The top-level-param repro I wrote into the brief
(`proc f(a: SmallCount)`) was **REFUTED**: it already returned `sxUnsat`.
#161's `promoteSound` independently lifts any signed, proven-range top-level
parameter to Z3's unbounded Int theory at allocation, so BV truncation never
applies there. The AST premise held (the wrapped operand's `getTypeInst`
reports `"SmallCount"` and fails `isIntFamilyName`), but the consequence did
not — at that position.

Pushing on adjacent positions found the real bug: a range-alias **object
field** (`r.f: range[0'i32..100'i32]` vs an oversized literal) returned false
`sxSat` with witness `f = 0`, and an enum/range-alias **local** the same. Fixed
by reading width and signedness off the `outerTy`/`innerTy` `IRType`s that
`classifyType` already computes — reusing `rangeBaseType` /
`enumOrdBitsNeeded` rather than adding a third name-based rule.

One carve-out was found empirically, not by design: routing a
`promoteSound`-promoted param through `mkConvIntWidth` regressed a correct
`sxUnsat` to `sxUnknown`, because `lowerConvIntWidth` hard-asserts a raw-BV
operand. `isPromoteSoundEligibleParam` leaves exactly that shape on the
untouched identity path.

## A FAMILY, not three bugs — worth recording as such

Four related false-SAT defects have now surfaced, all the same root shape: **a
value carrying a narrower width than its expression's declared type, so an
oversized literal truncates mod 2^n and wraps into range.**

1. plain `int32` param vs an oversized literal — `678c6ce`
2. range-aliased object field — `c74c04b`
3. range-aliased local — `c74c04b`
4. `ord()` of an enum, which identity-passes at the ENUM's narrow lifted width
   instead of `ord`'s declared native-`int` return — IN FLIGHT

`tests/tsymex_163rev_int_literal_width.nim` is now the flagship pin for the
whole family and should stay that way; a fifth instance belongs there too.
The positions that are NOT affected are worth knowing: a signed proven-range
top-level param is covered by `promoteSound`, and unsigned range-alias params
and native-width `ord()` were already sound for orthogonal reasons documented
in that test file.

## Remaining to close

1. The `ord()` fix (family member 4), in flight.
2. One bump **139 -> 140** covering `c74c04b` and the `ord()` fix. Both are
   verdict-affecting (each closes a real false SAT). Move the CR2 `==` pin and
   raise the floor pin in `tsymex_163rev_int_literal_width.nim`.
3. Full sweep vs `base163.log` (460 entries, pinned worktree at `ac507c1`).
   `tsymex_snd3_loopdegrade` is an undocumented HANG on unmodified HEAD — expect
   its exit-137 and do not read it as a regression.
4. `wiring = proven`. `quipu` is not on PATH but DOES run as a git hook here;
   find the hook's invocation rather than assuming it is unavailable.

**Resume:**

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -50
grep -n 'symexWalkerVersion\* = ' src/nelli/smt/canonicalize.nim
scripts/dt-bounded.sh c tests/tsymex_163rev_int_literal_width.nim 300
scripts/sweep.sh <out>.log && scripts/sweep-diff.sh \
  /home/corey/.claude/jobs/4fd5573d/tmp/base163.log <out>.log
```

## Round 9 closed

| item | commit | note |
|---|---|---|
| family member 4 — `ord()` | `710e9dc` | `ord()`'s magic intercept re-derived its result width from the ARGUMENT (an enum at its narrow `enumOrdBitsNeeded` width) instead of the `Call` node's own correct native-`int` classification — discarding the right answer one level up. Subtle because the enclosing `HiddenStdConv` and the `Call` node's types already AGREE at native width, so the widening arm saw no mismatch and recursed straight past. `ord(c) > 3_000_000_000` on a 3-member enum returned `sxSat` witness `cGreen` (real `ord(cGreen) == 1`). Confirmed and fixed at six positions: param, local, object field, `char`, non-comparison binding, arithmetic. `isPromoteSoundEligibleParam` was factored into ONE shared proc for this site and `c74c04b`'s rather than duplicating the carve-out — closing the drift risk directly. |
| bump 139 -> 140 | `284734d` | Covers `c74c04b` and `710e9dc`, both real false SATs. The doc comment records them as members of the width-truncation family, with the unaffected positions and why. |
| collateral regression from `d71da9e` | `90531ae` | **Round 8's enum-witness fix broke three suites' COMPILATION.** Making the witness honestly enum-typed is correct, but `tsymex_rectify_variants`, `tsymex_phase11_walker` and `tsymex_phase6_case` still compared it against `ord(x).uint8`/`.uint16`. The enum agent fixed one such suite when `d71da9e` landed and missed these. All three now use the idiom that commit established (`ord(r.witness[0]) == ord(x)`), assertion strength unchanged. The corpus was then swept for further instances — none; the remaining suspicious matches are plain `uint8` params or already-enum casts that are now no-ops. The third file was found by that sweep, not by the report, and would otherwise have read as a regression. |

## State

Branch `rfc-161-163-symex-defects`, HEAD `90531ae`, **NOT PUSHED** (last push
`26418f3`). Walker **140**, in six bumps across nine review rounds. The final
full sweep is RUNNING — read its result before believing any completion claim:

```
tail -34 /home/corey/.claude/jobs/4fd5573d/tmp/sweepr9.out
grep -c . /home/corey/.claude/jobs/4fd5573d/tmp/cur163r9.log   # progress /484ish
```

Baseline is the same `base163.log` (460 entries, pinned worktree at `ac507c1`)
every gate this session used. Expect `tsymex_snd3_loopdegrade` exit 137 — it is
an UNDOCUMENTED HANG on unmodified HEAD, not a regression, and distinct from the
six known `tsymex_r6_*` Linux hangers.

## Remaining

1. Read the sweep. If anything regressed, it belongs to this round.
2. `wiring = proven`. `quipu` is not on PATH but DOES run as a git hook here —
   find the hook's invocation rather than assuming it is unavailable.
3. Corey's call: push (~40 unpushed commits, zero CI exposure).

## Open, recorded, not closed

- **R26's observability** — `ziWidth`/`ziSigned` are stamped and
  `obligationLog` populates on a concolic path, but `ConcolicCollectResult` /
  `ConcolicFlipResult` have no raised-verdict channel, so it cannot surface.
  Wiring one needs `fuzz.nim` orchestrator work.
- **The three parse-time error kinds do not reach `concolicCollect`**, which
  never reads `prog.parseErrors`. Pre-existing structural gap in that API.
- **`tsymex_snd3_loopdegrade`** hangs on unmodified HEAD; belongs in the same
  ledger as the six known hangers.
- **`tn45probe` / `tprobe_n45stats`** remain unregistered (pre-existing drift).

## Gate status checkpoint

Final sweep still RUNNING at this refresh: **306 entries** recorded,
completion marker present: no.
Nothing below is a completion claim — read the gate before treating round 9 as
closed:

```
tail -34 /home/corey/.claude/jobs/4fd5573d/tmp/sweepr9.out
grep -c . /home/corey/.claude/jobs/4fd5573d/tmp/cur163r9.log
```

If the waiter was lost, re-arm it by polling for the `SWEEP_COMPLETE` marker in
`sweepr9.out` — **gate on the marker, never on `pgrep`**. Two separate traps bit
this session: a waiter grepping for `sweep.sh` matches its own argv and never
exits, and the sweep's real parent is a `run_one` driver whose argv never
contains `sweep.sh`, so pattern-killing it misses (`ps -eo pid,ppid,args` and
walk the ppid chain instead).

If the sweep died mid-run, discard the partial log and re-run from scratch
against the same baseline — a partial log must never be diffed as if complete.
The previous aborted attempt is parked as `cur163rev.aborted.log` for exactly
that reason.

Expected in the result, neither a regression:
- `tsymex_snd3_loopdegrade` exit 137 — an UNDOCUMENTED hang on unmodified HEAD.
- `unregistered=2` (`tn45probe`, `tprobe_n45stats`) — pre-existing drift.
  `missing` should be **0**; if it is not, check for a quoted string inside a
  `nelli.nimble` COMMENT being scraped as a suite name (fixed once already this
  session, and the drift extractor now strips comments).

---

# GATE FAILED — 15 regressions. Round 9 is NOT closed.

```
unchanged=445  regressed=15  new-failing=0  new-ok=34  gone=0
```

The 15 that passed in the `ac507c1` baseline and fail now:

```
tsymex_tot1_totality_corpus          tsymex_phase15_CR3_CR4_CR6_float
tsymex_phase15_g10_smoke             tsymex_phase2_overflow
tsymex_r6_r3_svint_overflow          tsymex_retest_c3_bitwise_guard
tsymex_r6_a1_variantlit              tsymex_phase2_bv_arith
tsymex_phase15_F5_probeproto         tsymex_p2b_refobjconstr_expr
tsymex_r6_a4_construct_interactions  tsymex_phase15_g7_static_param
tsymex_phase15_C2_staticparams       tsymex_cr9c_intrep
tsymex_p2a_objconstr_expr
```

**Signature** (confirmed on three): a DEFINITIVE verdict became `sxUnknown`.
`probeproto`'s `int32(f) + 5 == k` expected `sxRaised`, got `sxUnknown`;
`phase2_overflow`'s "isExact finds the BV-only witness" and `cr9c_intrep`'s
"bv32 vs bv32 arithmetic" both expected `sxSat`, got `sxUnknown`. Safe
direction — no unsoundness — but a broad COMPLETENESS regression: the engine
used to reach a verdict and now declines.

**Hypothesis tested and REFUTED, do not repeat it.** `maxFrontierSize`'s
default (0 = unbounded -> 256, `991b0ff`) matches the signature exactly, since a
frontier prune degrades via `beBudgetExhausted`. I set the default back to 0 and
all three still failed identically. Not the cause. Default restored to 256.

**Prime suspects**, from the failing names clustering on int width /
representation (`bv_arith`, `intrep`, `probeproto`, `svint_overflow`,
`bitwise_guard`, `overflow`, `int32(f)`) and object/variant construction
(`objconstr`, `refobjconstr`, `variantlit`, `construct_interactions`,
`staticparams`): the three width-conversion commits `678c6ce`, `c74c04b`,
`710e9dc`. The strongest lead is that `c74c04b`'s own report documents
`lowerConvIntWidth` HARD-ASSERTING a raw-BV operand, and that routing a
promoted `svInt` param through it regressed a correct `sxUnsat` to `sxUnknown`
— the same failure direction as all 15. Its `isPromoteSoundEligibleParam`
carve-out may simply be too narrow.

A bisect-and-fix agent is in flight with instructions to BISECT from
`e1a6b57` (the last gate that was clean apart from one adjudicated item)
rather than guess, and a hard constraint: the 15 must pass again WITHOUT
reopening the four false SATs those commits closed
(`tests/tsymex_163rev_int_literal_width.nim` must stay green). If those two
goals genuinely conflict, it is to STOP and report both repros — that trade is
my call, not its own. It is also explicitly forbidden from adjusting the 15
suites' expectations to make the sweep green; if a specific expectation is
genuinely now wrong it must argue that per-suite against a real-Nim oracle.

**Nothing in this session is closed until this is resolved and a clean sweep
runs.** The round-8/9 fixes are real and their pins are green in isolation, but
the branch as a whole currently regresses 15 suites against its own baseline.

## Gate failure diagnosed and closed — all 15

**First bad commit, by bisect (not guess): `678c6ce`.** Trail:
`e1a6b57` PASS -> `d71da9e` PASS -> `678c6ce` **FAIL** (both probes).

**Mechanism.** Nim gives an un-suffixed integer literal a provisional `int`
(64-bit) type, then inserts a NARROWING `nnkHiddenStdConv` when it sits beside
a narrower operand — the `2` in `x * 2` for `x: int32`. `678c6ce`'s new gate
could not distinguish that from a genuine narrowing of a VARIABLE (the real
unmodelled case it targeted) and declined the whole expression
(`declineIntWidthConv`), forcing `sxUnknown`. A literal beside any
`int8`/`int16`/`int32` operand is everywhere, which is why 15 suites moved.
Fixed at `64ed929` by recognising the wrapped operand is a LITERAL before the
width check runs — narrowing or widening a literal is always
representation-safe, and `parseExpr`'s literal arm carries no width tag anyway.
That ordering also sidestepped a second crash: a concept-constrained generic
reaches that arm with `typeKind == ntyNot`, as unresolvable as `ntyNone` but
missed by the file's standing `!= ntyNone` guard.

**A second, pre-existing bug surfaced by the causal chain** (also `64ed929`):
six object-constructor decline arms returned a dangling `mkVar(freshSynth(...))`
— a reference into an env slot nothing binds. Reading it raised `KeyError`,
which the C-backend's nested-`walkBlock` unwind silently swallowed (masked, not
sound). #163's OWN module-global fix (`7182801`) closed that swallow and
surfaced the dangling reference as a real crash one level down. Routed all six
through the existing `unsupportedFieldPlaceholder` idiom, and hardened
`isVariantField`'s walker arm to degrade in-band (new
`seVariantFieldOnDeclinedCtor`) instead of `doAssert false`.

**The 15th: `maxFrontierSize`, and my own error.** I told the bisect agent the
frontier cap was "not your suspect" because I had tested three suites with the
default set back to 0 and all three still failed. That was true of those three
and I over-generalised it to all fifteen. The agent escalated it back rather
than accepting my framing: A4-3b carries 66 live paths past the 256 cap and the
prune turned a genuine UNSAT into `sxUnknown`. Reverted at `90caaa1` — see that
commit and the test header for why the cap's ORIGINAL justification was already
dead (R22's forks return one survivor; they never multiplied the frontier) and
what the bar is for proposing a non-zero default again (measure across the whole
corpus, not a sample).

**No bump owed** for `64ed929` or `90caaa1`: every affected verdict was already
`sxUnknown` one way or another, and the revert restores a pre-existing default.
Walker stays at **140**.

## Round 10 — the gate re-run, and it is clean

```
pass=486 fail=2 (of which timeout-killed=1) skip=6 total=494
unchanged=459 regressed=1 new-failing=0 fixed=0 skip-changed=0 new-ok=34 gone=0
unregistered=2 missing=0
```

Logs: `cur163r10.log` / `sweepr10.out` (baseline `base163.log`, pinned at
`ac507c1`). **The whole symex surface is clean** — 34 new suites passing, zero
regressions among them, and the round-9 diagnosis holds up under the full gate
rather than the 15-suite sample that found it.

**`regressed=1` is `tparallelcheck`, and it is not ours.** The proof is not an
argument from plausibility: `sweep3.log`, dated **2026-08-28**, fails it — three
weeks before this branch's first commit (`3ce1dfd`, 2026-09-17). Across the ten
recorded sweeps in the job tmp it has failed three and passed seven, on
unrelated code states. It passes 15/15 in isolation and 3/3 under six-way
podman load.

The mechanism is a designed-in flake, found by reading rather than by
re-running: `tests/tparallelcheck.nim`'s racy-counter test asserts
`r.outcome in {otFalsified, otFlaky}` — that a read-modify-write race **will be
observed** inside the budget. That is an assertion about the OS scheduler. On a
box running six containers the two threads time-slice instead of interleaving,
the window between `racyInc`'s read and its write never straddles a context
switch, every history is linearisable, and the catch silently does not happen.
The test's own comment (`:127`) claims it mitigates this with "many repetitions
per plan + many examples + **jitter**"; `:147` passes `maxJitter = 0`. Being
fixed in this round — a gate test nobody can read is not a gate.

`tsymex_snd3_loopdegrade` exit 137 is byte-identical to baseline.

## Round 10 — closing the "open, recorded, not closed" list

That list existed because round 8 reclassified work as filing material, which
was the wrong call and was corrected. Round 10 closes it out.

- **R26's observability + the parse-error gap are ONE hole, not two.**
  `runConcolicCollectImpl` already drains both degrade sinks into
  `counters.walkDegradeCount` (W10/R9) and then throws away the two richest
  parts of the same story: `obligationLog` (which `9d1d8e3` confirmed populates
  `odLive` on a concolic path) and `prog.parseErrors` (which that driver never
  reads at all). Both are being landed on `ConcolicCollectResult` as a
  diagnostics channel, mirroring `SymexResult.obligations` — IN FLIGHT at this
  refresh; the closing sha goes here, and until it does this bullet is a plan,
  not a result. **Deliberately NOT built:** a
  raised-verdict channel through to `fuzz.nim`. The fuzzer executes every seed
  against the real SUT and observes an actual crash directly, so that channel
  would be a producer with no live consumer — the exact defect class the wiring
  audit exists to catch. Recorded as a decision, not left as a silent omission.
- **`tn45probe` / `tprobe_n45stats` — verified registerable, registration
  pending** (`nelli.nimble` is held by the in-flight agent above). Both were
  run first and confirmed to terminate and pass WITHOUT `-d:symexQueryStats`,
  so the default suite gains no hang: `tprobe_n45stats` skips itself when the flag is
  absent, `tn45probe` runs its k=2 trip-wire and reports `sxUnknown` in seconds.
  `tn45probe` also lost its deprecated `withSymexSettings` builder for the
  partial-literal form RFC-0010 introduced. The drift report's `unregistered`
  count now measures real gaps instead of two known probes.
- **`tsymex_snd3_loopdegrade`** — under diagnosis this round, by measurement.
  The standing hypothesis is unbounded PATH growth, not unbounded unwinding: a
  symbolic-length string loop whose guard degrades to a fresh unconstrained
  bool forks both ways every iteration, and `maxFrontierSize` is back to 0.

## Round 10 — bookkeeping reconciled

Three ledger rows read `open` long after their fixes landed (`R24`/`R25`/`R26`
at `9d1d8e3`, `R30` at `4e01f98`) and the round-4 findings header still said
"none fixed"; `W8` read "OPEN — no RED" after `bd6a013` pinned it. All
corrected in place. This is the fourth time this session a stale status has had
to be caught — the ledger rots faster than the code does, and the standing
lenses are the only thing that has reliably found it.

**`nelli.nimble`'s test-task comments carried two stale claims**, both fixed:
`tsymex_163rev_frontier_default`'s comment still said "Default now `256`,
measured…" after `90caaa1` reverted it to 0, and
`tsymex_163rev_degrade_classification`'s said its item 1 "is NOT implemented —
it needs a new `SymexErrorKind`, and `types.nim` is sibling-owned this session",
both halves of which stopped being true when `7182801` landed
`feGlobalReadUnmodelled`.

## Round 10 — `wiring = proven` has no address, and that is the answer

`quipu` is not on `PATH`; it runs via `core.hookspath` (`~/.config/git/hooks`)
and its CLI is `/home/corey/.local/share/uv/tools/quipu/bin/python3 -m
quipu.cli`. But **#161–163 are issue-scoped handoffs, not RFCs** — `quipu
roadmap` lists eight documents and none of them is this work. There is no
`<doc>/wiring` or `<doc>/review` address to set, so the skill's propagation step
terminates in this ledger. Recorded here rather than left looking like pending
work, which is what it looked like for two rounds.

## Remaining

1. Corey's call on pushing. `origin/rfc-161-163-symex-defects` exists (CI rounds
   1–2 ran against it) but HEAD is **67 commits ahead** of it and 117 ahead of
   `main`, so the current tip has had no Windows verification. The earlier
   "~45 unpushed commits, zero CI exposure" line was stale in both halves.


## Round 10 re-review — the lenses turned my own standard back on me

Three standing lenses on the round-10 scope (`9bd6cc0`, `e7f0ed4`, `9330fa8`,
`d39fcc8`). Security: **clean**, with coverage named — it verified the threadvar
mechanics (reset -> walk -> read, no yield point; `runConcolicFlipImpl`'s two
sequential collects each reset) and then checked reachability under real
concurrency, finding that `fuzzworker.nim:772-785` documents `parallelCheck` as
this library's ONLY `createThread` caller and every `fork()` as preceded by a
thread census. One pre-existing Low recorded, not fixed:
`ConcolicCollectResult.drawVars: seq[SymVal]` already carries Z3 handles across
the public result boundary; round 10 does not widen it.

| id | sev | status | finding |
|----|-----|--------|---------|
| T1 | High | fixing | **The diagnostics channel `9bd6cc0` added is itself a producer with no consumer on the production path.** `concolicCollect` has ZERO call sites in `src/`; the only production caller of `runConcolicCollectImpl` is `runConcolicFlipImpl`, which calls it twice and forwards only `.counters`. `.obligations`/`.parseErrors` are computed on every real flip and dropped. Both lenses found it independently. |
| T2 | High | fixing | **`maxJitter` structurally cannot catch an intra-op race, and `parallel.nim:339-340` overclaims that it can.** `spinJitter` is a counted no-op loop (nanoseconds vs a 1-15ms quantum) spent BEFORE `applySUT`, so no value of `maxJitter` widens a read-modify-write window inside one op. `e7f0ed4`'s `sleep(1)` is doing all the work; its `maxJitter = 50` is decorative. |
| T3 | High | fixing | **`tprobe_n45stats` is registered but structurally inert.** Its whole body is behind `when not defined(symexQueryStats)`, and nothing in the repo ever sets that define — not `nelli.nimble:730`, not any workflow, not any script. Registering it moved `unregistered` to 0 while leaving its instrumentation ungated in every venue. |
| T4 | Medium | open | ~10 hand-copied `HashSet[string]` dedup-by-`.msg` blocks in `runSymexImpl`'s tail (`runtime.nim:13374`-`13512`), plus two more added by round 10 at `:14219`/`:14222`. `obligations`/`abstractions` are declared verbatim on three types with three copies of the same doc. Wants one `dedupByMsg` helper and one shared diagnostics sub-object. |
| T5 | Medium | folded into T1 | `parseErrors` is passed, not enforced: `runSymexImpl` forces `sxUnknown` via `capForcedUnknown` for a `sevError` decline; the concolic path has no verdict to force and no wiring to anywhere a decision is made. |

**T1's rationale was wrong in a specific way worth recording.** The commit
justified not building a raised-VERDICT channel (the fuzzer sees real crashes
directly) and then reused that as cover for shipping the diagnostics
undrained. The Liveness lens separated the two correctly: the diagnostics
report something a crash CANNOT — a parse decline that left part of the program
unmodelled — and the values were already in scope for free at the one
production call site. The fix threads them into the live chain
`ConcolicFlipResult.collectCounters` -> `foldFlipResult` -> `CampaignStats
.concolicYield`, which is returned to the caller on `FuzzReport.stats` at campaign end [CORRECTED round 11 -- see below].

**Decision recorded so it is not re-litigated:** admission is NOT gated on a
parse decline. A decline means the SYMBOLIC model is incomplete, but the
materialized seed is still a real input executed for real against the SUT, so
refusing it would cost coverage and buy no soundness. Count it, surface it,
admit it.

## Round 10 — `tsymex_snd3_loopdegrade` diagnosed, and my hypothesis was wrong

I proposed unbounded path growth. **Refuted by measurement.** `VmRSS` held flat
(43228 -> 43612 -> 43740 KB) across 2+ minutes of sustained CPU — nothing like
2^k forking; `maxLoopUnwind=1` still hangs; and BOTH backends hang identically,
so it is not the backend-divergence class the file exists to pin. A frontier cap
would not even have applied: there is no frontier growth to cap.

**It is one Z3 query grinding.** `queryRLimit=1` terminates promptly with
`sxUnknown` (so Z3 is reached and rlimit enforcement works — not a Nim-level
loop); `queryRLimit=20_000_000` (this repo's own `defaultConcreteBranchRLimit`
precedent) still fails to conclude. That evidence is rlimit-based, i.e. Z3
logical steps rather than wall time, so it survives the core-starvation problem
recorded below.

**Only `sutEqualityLoopGuard` (SND-3-6) hangs** — the one test whose purpose is
proving the fix does NOT touch equality guards. SND-3-1 through SND-3-5 all pass
in seconds. The byte-identical SUT also exists as a PASSING test
(`R1B-while-4`, `tests/tsymex_r1b_shortcircuit_oob.nim`), which points at solver
runtime variance tied to per-binary state rather than a defect unique to this
source. `types.nim`'s `maxFrontierSize` doc already recorded the
non-termination; these measurements confirm its framing.

**Disposition — not the agent's recommendation as given.** It proposed
skip-listing the file. Skip-listing the FILE also retires five live soundness
pins for a real false-`sxUnsat` fix, and a skip-list entry quietly covering more
than it claims is exactly the `trequiresinit` incident. SND-3-6 moves to its own
file and only that file is skip-listed, with the measurements and the
`R1B-while-4` cross-reference in its header. Pending: `nelli.nimble` and
`scripts/sweep.sh` are held by an in-flight agent.

## Round 10 — two orphaned test runs had been stealing a third of the box

Found while reading a sub-agent's incidental note (it reported them as idle;
they were not). `scratchpad/bench/probe_163_w8hang` at **89.1% of a core for 1d
11h**, and `tests/tsymex_163rev_intoffset_range` at **87.9% for 19h** — on a
6-core host. Both reaped (`podman stop` for the one whose container was still
live and visible; a direct process-tree kill for the other, whose podman root
was `/tmp/podman-corey/storage` and so was invisible to the default
`podman ps`).

**What this does and does not invalidate.** Every wall-clock figure this session
was measured on a box missing a third of its cores, including the round-10
sweep. A clean sweep under starvation is a CONSERVATIVE pass — starvation makes
timeout kills likelier, not less likely — so `regressed=1` stands, and it makes
`tparallelcheck`'s contention flake MORE explicable, not less. The snd3
conclusion stands on rlimit (logical steps), not wall clock. The final sweep
will run on a healthy box.

**Tooling finding, recorded not fixed:** `scripts/dt-bounded.sh`'s own header
describes preventing exactly this orphan mode. It did not. One orphan's
container was still `Up 19 hours`; the other's was gone while its `nim`/binary
processes lived on. That file is held by an in-flight agent.

## Round 10 fix table

| id | sev | sha | what closed it |
|----|-----|-----|----------------|
| T1 + T5 | High | `8b244d7` | `ConcolicYieldCounters` gains `obligationsLive` and `parseDeclines`, populated in `runConcolicCollectImpl` beside the existing `walkDegradeCount` and folded by `foldFlipResult` — so they ride the live chain to `CampaignStats.concolicYield`, returned to the caller on `FuzzReport.stats` at campaign end [CORRECTED round 11 -- see below]. Liveness proven through the real path, not by field existence: assertions drive `concolicFlip` and then `foldFlipResult`, plus a two-call test proving the fold ACCUMULATES rather than overwrites. The counter rides every flip outcome including `cfoUnmodelable`, because `collectCounters` is assigned before `targetBranchIndex` is consulted. `parseDeclines` uses `capForcedUnknown`'s exact `sevError` predicate. The `.obligations`/`.parseErrors` seqs stay as the detail view behind a live count — a legitimate role, unlike being the only surface. No bump (140). |
| T2 | High | `5d93568` | `spinJitter` spends its budget on real `sched_yield`/`SwitchToThread` syscalls instead of a user-space no-op spin. **Unit kept, mechanism changed**, so no caller's numbers need reinterpreting and `maxJitter = 0` still costs nothing. New `parallelJitterPoint*(n = 1)` lets a SUT perturb INSIDE an op without touching `LinOpDef.applySUT`'s signature. The overclaiming doc ("the differentiating feature vs. uninstrumented racy testing") is gone. Agent tested removing `racyInc`'s `sleep(1)` and measured **9 catches in 10** on between-op jitter alone — so the sleep stays, with that measurement recorded in the code rather than an assumption. |
| T3 | High | `233c7d1` | A per-file extra-defines table in BOTH `nelli.nimble`'s test task and `scripts/sweep.sh` (each commenting the other so they cannot silently diverge), plus an optional trailing args parameter on `dt-bounded.sh` that leaves its three existing callers alone. Proof is the difference, not the pass: WITHOUT the define the suite still prints `[SKIPPED] requires -d:symexQueryStats`; WITH it, all three assertions run and pass (`rlimit=7360`/`9369` on sat, `rlimit=10` on unsat, `ASSERTS small=1 big=6`). Nothing needed weakening. The `skip()` branch stays — a legitimate safety net, since the instrumentation symbols are compiled out without the flag and a bare `nim c -r` would otherwise hard-error. |
| T6 | High | `13b8998` | **A finding against T2's own fix.** `parallelJitterPoint` shipped with zero callers, referenced only in comment prose — "exercised by documentation" is not liveness, and the same commit's docs RECOMMENDED it over a hand-rolled sleep, so we were advertising a mechanism nothing had demonstrated. Settled by measurement with removal on the table: **20/20 idle and 10/10 under six-core saturation, all `otFalsified`**, with `maxJitter: 0` in the new test so the intra-op hook is the only perturbation. Better than between-op jitter's 9/10, because placing the yield at the race boundary lands it in the window every time. Reliable, so the recommendation stands — now cited to the test. Real caller at `tests/tparallelcheck.nim:161`. |
| T4 | Medium | in flight | The ~12 copies of the dedup-by-`.msg` idiom. Guardrails in the brief: per-sink dedup stays the default (the existing per-sink rule is deliberate, `runtime.nim:14159-14173`), and Part B does NOT proceed if consolidating the three `obligations`/`abstractions` declarations would rewrite every caller — `SymexResult.obligations` is public API chapulin reads, and "consumers report, don't drive" is not licence to break field access for tidiness. |

## Round 10 — SND-3-6 split, and what the sweep got back

`1e1a735`. `tsymex_snd3_loopdegrade` was a 900s timeout kill in every sweep this
session, which cost the gate five live soundness pins — SND-3-1 through SND-3-5
pin a real false-`sxUnsat` fix and pass in SECONDS. Only `sutEqualityLoopGuard`
hangs, so only `tsymex_snd3_6_equality_loop` is skip-listed.

Verified rather than assumed, in both directions: the parent now passes in
seconds, and the split file still hangs (killed at 180s), so the skip-list entry
is honest rather than covering a test that quietly started passing. A scoped
sweep reports `pass=1 skip=1 fail=0`, `unregistered=0 missing=0`.

The skip list gained a RULE alongside the entry — each entry names its own
reason and covers exactly the suite that hangs, with the `trequiresinit`
incident cited as why. That is the trap this change was one decision away from
walking into.

## Round 10 — a claim of mine that needed narrowing

"Drift is zero in both directions" is true and narrower than it sounded. The T3
agent established that **`nimble test` is invoked by no CI leg at all** (an
existing comment in `symex-mingw.yaml` says so outright), and `symex-mingw`'s
derived corpus pulls only `tsymex_*`-prefixed names, which excludes both
probes. So registering a file in `nelli.nimble` buys agreement between the list
and the filesystem, plus `nimble test` locally — it does NOT buy CI coverage.
On Linux the real gate is `sweep.sh`, which sweeps the filesystem and now
carries the defines table too. On Windows the two probes run nowhere.

Renaming them `tsymex_*` would pull them into the derived corpus, and the
per-suite define mechanism already exists there (`-d:symexCiLeanB5`,
`symex-mingw.yaml:396-403`). **Recommended, deliberately not done:** it is a
change to a Windows leg that cannot be verified without pushing, and guessing at
unverifiable CI edits is how the last CI saga started.

## Round 11 — the lenses caught a false claim of mine, and a CI gap I got backwards

Three standing lenses on the round-10 FIX commits. Two of the three briefs
deliberately re-audited claims *I* had made, on the principle that a claim is
not evidence. Both audits found something.

### L1 (Critical) — "user-visible at campaign end" was false

I justified T1's fix with the chain `ConcolicFlipResult.collectCounters` ->
`foldFlipResult` -> `Orchestrator.concolicYield` -> `CampaignStats
.concolicYield` -> "reported to the user at campaign end", and I verified every
hop EXCEPT the last. The lens checked it: **nothing in the repo renders
`FuzzReport`/`CampaignStats`.** No `echo`, no `$` operator, no serializer; the
only proc taking a `FuzzReport` is `exportCrashes`, which writes
`report.irCrashes` bytes and never touches `concolicYield`. The only readers
anywhere are `check report.stats.concolicYield...` assertions in tests.

So T1 moved the dormancy one hop rather than closing it. The claim was asserted
as settled fact in two places (`tests/tsymex_163rev_concolic_flip_width.nim:65`
and this handoff), which is worse than the gap itself.

**The mitigation, stated without hiding behind it:** every OTHER field of
`CampaignStats` is in exactly the same position. The library returns a
`FuzzReport` and the caller decides what to print, which is a legitimate design
for a library — the two new counters are precisely as reachable as
`drawsSymbolicated` and the other eight. That makes the CLAIM the defect rather
than the wiring. Closing it means correcting the wording AND giving
`CampaignStats` a renderer, which makes the whole struct usable instead of just
these two fields.

`foldFlipResult` itself was confirmed genuinely live: `fuzz.nim:1695` sits in
`tryConcolicBridge`, reached from the main mutation loop in the public
`fuzz*[T]` (`fuzz.nim:2305`) whenever `assist.bridge != nil` — the path
`fuzzConcolic` expands to. Not test-only.

### L5 (High) — I got SND-3-6's Windows exposure exactly backwards

Round 10 reasoned carefully about `tn45probe`/`tprobe_n45stats` being EXCLUDED
from `symex-mingw`'s derived corpus for lacking a `tsymex_` prefix, and
recorded that honestly. It did not notice that the split file has the OPPOSITE
problem: `tsymex_snd3_6_equality_loop` IS `tsymex_*`-prefixed, so
`derive-ci-suites.ps1` pulls it into the corpus, and that script's
`$skipReasons` was `[ordered]@{}` — completely empty.

An ordinary sharded corpus job has **no per-suite timeout** (only the job-level
60 minutes) and no per-suite isolation. A hang there burns the full hour and
takes every suite queued behind it in that shard with it, unattributed —
exactly the "runner lost communication, no logs" failure that scan-tail's
per-suite job isolation exists to prevent, and which this repo has already
lived through once. The round-10 diagnosis found the hang **backend-invariant**
(identical on `c` and `cpp`), so there is no reason to assume mingw fares
better, and nobody has checked.

Fixed by adding the entry to `$skipReasons` with its reason and its retirement
condition (run it on a real Windows runner and show it terminates). The
script's own guard — skip-listed suites must exist in `nelli.nimble`'s task —
is satisfied, and the corpus floor (150) is unaffected at 361 registered
`tsymex_*` suites. `pwsh` is not on this host, so this is a data entry into a
guarded table rather than an executed verification; it is fail-SAFE (it removes
a suite from the corpus, it cannot add untested behaviour).

My round-10 commit said "verified in both directions". That was true of the
Linux sweep only.

### Resolved, not a defect

**`parallelJitterPoint` is NOT the same class as the concolic dead end**, and
the lens was explicitly asked to apply the standard consistently rather than
grant an exemption. The distinction holds: `obligations`/`parseErrors` needed a
consumer inside nelli's OWN orchestrator, and that consumer existing nowhere
was a real internal-wiring gap. `parallelJitterPoint` is instrumentation meant
to be called from EXTERNAL SUT code, like `symexTarget` and `{.cover.}` — a
`src/`-internal call site could not exist by design. Exported via `nelli.nim`,
proven by test. Legitimately live; merely unproven in the wild, which is the
ordinary state of a new library primitive.

### Round 11 open findings

| id | sev | source | finding |
|----|-----|--------|---------|
| L1 | Critical | liveness | Above. Correct the claim in two places AND render `CampaignStats` so the chain terminates somewhere a person can see. |
| D5 | High | design | `foldFlipResult` sums each field with a hand-written `+=`, now eight of them. This is round 10's OWN defect class one layer downstream — "producer exists, consumer must remember to wire it". `fieldPairs` makes future scalar fields sum automatically and compile-fail on an unhandled type. |
| D1 | High | design | The two-copy defines table is guarded by a comment, not a mechanism. The repo solves this shape twice already — `sweep.sh`'s own drift block (`comm -13`/`comm -23`) and `derive-ci-suites.ps1`, which ELIMINATES one hand-list and asserts set-equality, failing loudly. I used neither. |
| D2 | High | design | `parallelJitterPoint` asks a SUT author to hand-place a harness call at the byte offset they already suspect is racy. The codebase's instrumentation idiom is pragma decoration (`{.cover.}`, `{.covercmp.}`, `{.symexTransparent.}`), which rewrites a whole body without the author locating anything. The proc should be the primitive a pragma is built on, not the recommended surface. |
| D3 | Medium | design | The two new dedup helpers hand-roll the SAME `HashSet` loop independently — 12 copies became 2, not 1. And the deeper duplication the finding pointed at (eight sinks, each with its own union, guard and six-line comment) is untouched. Seven of the eight `if len > 0:` guards are now DEAD (the helper no-ops on empty) while the eighth site was correctly de-guarded — applied mechanically rather than as a rethink. |
| L4 | Low/Med | liveness | The "20/20 idle, 10/10 saturated" and "9 in 10" figures now baked into `parallel.nim`'s docs describe one-time manual experiments. The shipped test is a SINGLE seeded run and cannot regression-detect a drop in that rate, while the doc asserts the figure as "measured, not hopeful". |
| S1 | Low | security | `dt-bounded.sh`'s `$3` splice is unquoted. Every current caller passes a hardcoded literal (all traced), so nothing exploits it — but RFC-0002's L1 closed this exact class for `$test_file` in the SAME script, and `233c7d1` reopened it for a new parameter. Quote it defensively. |

## State at this refresh — round 11 fixes in flight, round 10 gated GREEN

**HEAD `ab7b9e0`. Walker 140. 117 commits ahead of `main`, 67 ahead of
`origin/rfc-161-163-symex-defects`. Not pushed.**

### The gate finally came back clean

```
pass=489 fail=0 (of which timeout-killed=0) skip=7 total=496
unchanged=459 regressed=0 new-failing=0 fixed=1 skip-changed=0 new-ok=36 gone=0
unregistered=0 missing=0
## FIXED (1)
  c tests/tsymex_snd3_loopdegrade.nim   137 -> 0
```

Logs `cur163r11.log` / `sweepr11.out` against baseline `base163.log`. This
gates ROUND 10 — the tree at `4374abe`; `ab7b9e0` after it touched only docs
and `derive-ci-suites.ps1`, no Nim. First `fail=0` of the session. The
`fixed=1` is the SND-3-6 split recovering five soundness pins the gate had
been losing to a timeout kill every run. The seven skips are the six r6
hangers plus SND-3-6, each now carrying its own documented reason. Also the
first sweep run on a box with all six cores (see the orphan-reaping entry).

### Four agents in flight, disjoint files

| agent | finding | files |
|---|---|---|
| campaign renderer + generic fold | L1 (Critical), D5 (High) | `fuzz.nim`, `concolictaxonomy.nim`, `tsymex_163rev_concolic_flip_width.nim`, `tsymex_163rev_concolic_diagnostics.nim` |
| defines-table sync + skip hygiene + quoting | D1 (High), D4 (Med), S1 (Low) | `scripts/sweep.sh`, `scripts/dt-bounded.sh`, `scripts/derive-ci-suites.ps1`, `nelli.nimble` |
| jitter pragma + doc-figure honesty | D2 (High), L4 (Low/Med) | `src/nelli/parallel.nim`, `tests/tparallelcheck.nim` |
| finish the dedup refactor | D3 (Medium) | `src/nelli/smt/runtime.nim` |

Each brief carries an explicit escape hatch, because three times this session
the valuable outcome was an agent REFUSING the task as framed: if `fieldPairs`
cannot work, propose what achieves compile-time safety instead of leaving a
"remember to wire it" comment; if the pragma proves unreliable, ship the
measurement and NOT the recommendation; if a sink site does not fit the
template, that is worth more than a tidy refactor; and verify the new
defines-table sync check by deliberately diverging the tables, because a sync
check nobody has watched fail is not known to work.

### Resume command

If interrupted before the agents report, re-read this doc and check what
landed:

```
git log --oneline ab7b9e0..HEAD
git status --porcelain
```

Then, once all four are in, re-gate and run round 12's lenses:

```
T=/home/corey/.claude/jobs/4fd5573d/tmp
nohup setsid bash -c "scripts/sweep.sh $T/cur163r12.log > $T/sweepr12.out 2>&1; \
  scripts/sweep-diff.sh $T/base163.log $T/cur163r12.log >> $T/sweepr12.out 2>&1; \
  echo SWEEP_COMPLETE >> $T/sweepr12.out" &
```

Gate the waiter on the `SWEEP_COMPLETE` marker, never `pgrep` (a waiter that
greps for the sweep matches its own argv and never exits). Expect `skip=7`.
Note `scripts/sweep.sh` is itself a fix target this round — do not edit it
while a sweep is executing, and re-verify the filtered-sweep behaviour after
the scripts agent lands.

### Open, for Corey

1. **Push.** 67 commits of CI-invisible history, including all seven walker
   bumps from 134 to 140.
2. **`quipu setup`** — `quipu check` warns the ingest hooks are not fully
   wired (`post-merge`/`post-rewrite` missing, `pre-push` stale), so "a push,
   merge or rewrite here may never reach the configured hub, silently". This
   matters more than usual with a push pending. Not run unasked: it installs
   repo-local wiring.
3. **Recommended, deliberately not done:** rename `tn45probe`/`tprobe_n45stats`
   to `tsymex_*` so `symex-mingw`'s derived corpus picks them up. They run in
   no CI leg today. It is a change to a Windows leg that cannot be verified
   without pushing, and guessing at unverifiable CI edits is how the last CI
   saga started.

### Standing note on the loop

Eleven rounds. The last three have each been findings against the PREVIOUS
round's own fixes — round 10 closed round 9's regressions; round 11 found that
round 10's headline fix moved dormancy one hop instead of closing it, that its
refactor left seven dead guards and two copies of the loop it was
deduplicating, and that its test split opened a Windows CI exposure while the
commit claimed both directions verified. The lenses are earning their keep
(three of my own errors today), but the loop has not yet reached a floor.

## Round 11 fix table — all six closed

| id | sev | sha | what closed it |
|----|-----|-----|----------------|
| L1 + D5 | Critical / High | `c765a3f` | `formatCampaignSummary*(CampaignStats): string` in `fuzz.nim` (named proc, not `$` — `engine/render.nim`'s `renderReport` is the precedent for composite report types), plus `$` for four taxonomy types; all sixteen fields, enum/table iteration in declared order so output is deterministic; NOT called from the fuzz loop (a library must not print unbidden). `foldFlipResult`'s nine hand-written `+=` lines became a `fieldPairs` fold with a real `{.error.}` arm. The table field keeps its explicit per-key merge including the `byConstruct` side effect, with a test proving it survived. `ConcolicFlipCounters` deliberately untouched — it already iterates its enum exhaustively, which is the array-safe pattern, not the hazard. |
| D1 + D4 + S1 | High / Med / Low | `27055ba` | Chose ELIMINATION over detection: `sweep.sh` parses `nelli.nimble`'s table instead of keeping a copy, exit 2 if the block is absent. Verified by first REPRODUCING the silent divergence (renamed the define in `nelli.nimble` only, watched `tprobe_n45stats` print `[SKIPPED]`), then reverting. `stale_skiplist=N` added to the drift report, verified with an injected bogus entry. `dt-bounded.sh` passes extra args as argv elements; verified adversarially (`-d:foo;touch /tmp/PWNED` created nothing). |
| D2 + L4 | High / Low-Med | `1881473` | `{.jitterPoints.}` macro pragma following `{.cover.}`'s structure; caught the race 20/20 idle and 10/10 contended with no sleep and no hand-placed call. Every catch-rate figure now notes it is a one-time measurement at the introducing commit, naming the single-seeded test that actually guards the catch per sweep. |
| D3 | Medium | `450ba6b` | Shared `iterator dedupedByMsg` backs both helpers (iterator, not a materialised seq, so the count path does not copy strings); `drainSinkUnion` template collapsed 7 sites; **8** dead guards removed — one more than the review enumerated. Two sites correctly NOT forced into the template (one WalkCtx-only, one threadvar-only). |

## Round 12 — gate GREEN, and an operational error of mine

```
pass=489 fail=0 (of which timeout-killed=0) skip=7 total=496
unchanged=459 regressed=0 new-failing=0 fixed=1 skip-changed=0 new-ok=36 gone=0
unregistered=0 missing=0 stale_skiplist=0
```

Integrity checked independently: 496 log lines / 496 unique suites / 496 files
on disk.

**I briefly reported `gone=1` and "the gate silently dropped a test". That was
wrong and the cause was mine.** My first launch used a shell variable that did
not survive into the backgrounded chain; instead of dying cleanly it left a
SECOND sweep running against the same output log. The waiter fired on the first
`SWEEP_COMPLETE` and diffed a log the other run was still filling — a 495-line
snapshot and a phantom `gone=1`. No defect in `sweep.sh`.

**Carried caveat:** two concurrent sweeps means two runs compiling the same
test files, which is the documented same-file-clobber hazard. Clobbering
produces failures rather than false passes, and `fail=0` across 489 suites
makes a false green unlikely — but the round-12 fixes need a gate anyway, and
THAT run must be a single clean instance and is the authoritative one. Launch
sweeps with absolute paths, never a shell variable.

## Round 12 findings — open

| id | sev | finding |
|----|-----|---------|
| L12-1 | High | `sweep.sh`'s new nimble parser silently drops a key/value pair that is LINE-WRAPPED inside the block (`grep -oE` is per-line). **Reproduced** on a throwaway file: block found, no exit 2, entry vanishes with zero errors — the suite then reverts to its `[SKIPPED]` stub, indistinguishable from a clean run. The change that eliminated the divergence bug reintroduced it by another route. Reordering, trailing `#`, and blank lines are all handled correctly; only an intra-pair line break defeats it. |
| L12-2 | High | `{.jitterPoints.}` is a SILENT NO-OP on any proc with one top-level statement (`body.len <= 1` returns unchanged) — and `inc(c.count)` / `c.count += 1` is the natural shape for the very race class it targets. The shipped proof splits read and write into two statements so boundaries exist, and so structurally cannot demonstrate the compound-assignment idiom. Compiles clean, documented as the recommended surface, does nothing, says nothing. |
| Q2 | High | `c765a3f` fixed hand-maintained field enumeration and then wrote THREE more: `$`(ConcolicYieldCounters) (9 names), `formatCampaignSummary` (16), and the completeness test (16 again, as a runtime substring check rather than a structural guard). `fieldPairs` was already in hand. Also: `renderReport` — the cited precedent — is an `OutputFormat` enum WITH a real JSON arm; the new renderer reproduces only its text mode, so a caller wanting structured logging must re-parse a pretty string. |
| Q3 | High | The pragma does not recurse into `if`/`while`/`case` bodies, so a read-modify-write inside a loop — arguably the commoner shape — gets zero instrumentation and no diagnostic. `{.cover.}`'s `instrumentNode` already exists as a working recursive walker to follow. Compounds with L12-2: the pragma currently works only on flat multi-statement bodies. |
| Q5 / L12-3 | Medium | The fold excludes the table field BY TYPE while `name` is already bound in the loop. A second future `Table[WalkerConstructKind, int]` field — the taxonomy's own natural per-construct idiom, already used once — would silently hit `discard` instead of the `{.error.}` arm. Name-based exclusion is strictly more precise. |
| C7 | Medium | `sweep.sh:242-247` builds space-delimited quadruples for `xargs -n4`, assuming no field contains whitespace — while `dt-bounded.sh`'s doc, added in the SAME commit, advertises `"-d:foo -d:bar"` as supported. First use of that advertised capability shifts every subsequent row's fields for the rest of the batch, silently. Not a regression (the old table had the same assumption) but the commit created the mismatch. |
| Q1 | Medium | The parser checks only that the extracted block is non-empty. Its sibling `derive-ci-suites.ps1` throws below a sanity FLOOR, so a regex matching too little fails loudly there and silently here. |
| Q6 | Low | `drainSinkUnion` references `w` as a free identifier resolved at each call site rather than taking it as a parameter. Safe today (all 7 sites are inside `runSymexImpl` with no shadowing — verified), but in a 14.7k-line file a future extraction yields "undeclared identifier `w`" pointing at the template definition. |

Also confirmed CLEAN this round, with coverage named: the `450ba6b` refactor
(hygiene, all 8 removed guards genuinely dead, no `dst`/`src` aliasing at any
site), the `fieldPairs` fold mutating in place rather than a copy (checked
against Nim's two-arg `fieldPairs` at `lib/system/iterators.nim:337` AND by
confirming the test starts from zero so a copy-fold would be caught), the
pragma never inserting AFTER the final statement (so an implicit-`result`
expression return cannot be corrupted), `dt-bounded.sh`'s `read -ra` producing
a genuinely empty array, and `stale_skiplist` reading the same single array the
sweep consults.

**L12-4, and it corrects my framing rather than the code:** `formatCampaignSummary`
has no non-test callers — but the cited precedents `renderReport`/`repro` have
none either, so "a caller-invoked renderer is a legitimate terminus" is this
codebase's actual convention, not special pleading. The accurate record is that
**round 10's public `FuzzReport.stats` field is what closed L1** (a caller could
always read `report.stats.concolicYield.collect.obligationsLive` unaided); the
renderer is convenience, unproven in the wild. I have asserted "the chain now
terminates visibly" in three consecutive rounds and been wrong twice.

## Resume

Round 12's eight findings are NOT yet dispatched. Next step is a fix round over
them, then a SINGLE-INSTANCE gate:

```
nohup setsid bash -c 'scripts/sweep.sh /home/corey/.claude/jobs/4fd5573d/tmp/cur163r13.log \
  > /home/corey/.claude/jobs/4fd5573d/tmp/sweepr13.out 2>&1; \
  scripts/sweep-diff.sh /home/corey/.claude/jobs/4fd5573d/tmp/base163.log \
  /home/corey/.claude/jobs/4fd5573d/tmp/cur163r13.log \
  >> /home/corey/.claude/jobs/4fd5573d/tmp/sweepr13.out 2>&1; \
  echo SWEEP_COMPLETE >> /home/corey/.claude/jobs/4fd5573d/tmp/sweepr13.out' &
```

Absolute paths only. Confirm no other sweep is running first
(`pgrep -af dt-bounded` and check `podman ps`), and before reading the result
verify `wc -l` on the log equals the on-disk count.

## Open, for Corey — unchanged

1. **Push.** 67+ commits of CI-invisible history, all seven walker bumps
   134->140.
2. **`quipu setup`** — ingest hooks not fully wired (`post-merge`/`post-rewrite`
   missing, `pre-push` stale); a push may never reach the hub, silently.
3. Recommended, not done: rename the two N45 probes `tsymex_*` so
   `symex-mingw`'s corpus picks them up. Unverifiable without pushing.

## Convergence note

Twelve rounds. Rounds 10, 11 and 12 each found real defects in the PREVIOUS
round's fixes: round 11 found round 10's headline fix moved dormancy one hop;
round 12 found round 11's parser reintroduced the bug it eliminated (by a new
route) and its pragma silently does nothing on the commonest race shape. The
lenses are finding genuine things — including four errors of mine across the
two rounds — but this is not yet converging on a floor, and each round's fixes
are themselves a new surface. Worth a decision about whether to keep fixing or
stop at the green gate and file the remainder.

## PUSHED — 2026-09-19, and CI is running for the first time on this work

`git push origin rfc-161-163-symex-defects` -> `26418f3..5056b46`, **86
commits**. Corey's call, given directly.

All three Windows legs triggered on the push (the `rfc-*` branch naming did
its job): `symex-mingw` (35472097655), `fuzzer-mingw` (35472097646),
`fuzzer-msvc` (35472097640). This is the **first CI exposure for every walker
bump from 134 to 140** and for all of rounds 8-12. Prior runs on this branch
(2026-09-18, at `26418f3`) were all green: symex-mingw ~41m, fuzzer-msvc ~36m,
fuzzer-mingw ~10m.

A background watcher is armed on all three.

**Caveat recorded at push time:** the `quipu` pre-push hook is the one
`quipu check` reports STALE, so this push may not have reached the hub. The
commits are on GitHub regardless — it is the tracker that may be unaware.
`quipu setup` repairs it; not run, it installs repo-local wiring and that is
Corey's to authorise.

**What CI is now exposed to that no Linux gate covers:** the six
`tsymex_r6_*` suites skip-listed on Linux but historically GREEN on
symex-mingw, and `tsymex_snd3_6_equality_loop`, which `ab7b9e0` added to
`derive-ci-suites.ps1`'s `$skipReasons` precisely so it would NOT run
unprotected in a sharded corpus job. That skip entry has never executed
before; if the run reports a corpus-count change or a `throw` from
`derive-ci-suites.ps1`'s sanity block, that entry is the first thing to look
at.

## Round 12 fixes — four agents dispatched, disjoint files

| agent | findings | files |
|---|---|---|
| harden the defines parser | L12-1 (High), Q1 (Med), C7 (Med) | `scripts/sweep.sh`, `scripts/dt-bounded.sh`, `scripts/derive-ci-suites.ps1`, `nelli.nimble` |
| fix the pragma's silent no-op | L12-2 (High), Q3 (High) | `src/nelli/parallel.nim`, `tests/tparallelcheck.nim` |
| generic renderer + name-based fold | Q2 (High), Q5/L12-3 (Med) | `src/nelli/fuzz.nim`, `src/nelli/smt/concolictaxonomy.nim`, `tests/tsymex_163rev_concolic_*` |
| explicit `w` parameter | Q6 (Low) | `src/nelli/smt/runtime.nim` |

Load-bearing instructions in those briefs, recorded so a resumed session does
not soften them:

- The parser must make a **silently-partial parse impossible** — robust
  multi-line parsing AND a count floor, since they catch different failures.
- **C7 must resolve in one honest direction:** carry multi-token values safely
  (NUL-delimited records) or stop advertising the capability and reject it
  loudly at parse time. A documented capability that silently corrupts the
  gate is not an acceptable end state.
- The pragma must **never silently decline**: after recursing the way
  `{.cover.}` does, zero insertions anywhere must produce a compile-time
  warning naming the proc and the reason.
- The pragma must **preserve the never-insert-after-the-final-statement
  property at every newly-recursed level** — a body's last expression can be
  the implicit `result`, and appending there changes the return value. Round
  12 verified that property held at the top level; recursion is where it can
  be lost.
- If nested instrumentation proves unreliable, **report the measured rate and
  do not claim otherwise in the docs**. A documented 14/20 is a good outcome;
  a 14/20 documented as reliable is the defect being fixed.

## Resume

1. Collect the four agents. Each owes a measured proof, not an assertion.
2. Read CI: `gh run list --branch rfc-161-163-symex-defects --limit 3`. A red
   leg here is more informative than anything the Linux gate can say — it is
   the first Windows verification of 86 commits.
3. Then the authoritative gate, **single instance, absolute paths** (the
   round-12 double-launch is recorded above):

```
nohup setsid bash -c 'scripts/sweep.sh /home/corey/.claude/jobs/4fd5573d/tmp/cur163r13.log \
  > /home/corey/.claude/jobs/4fd5573d/tmp/sweepr13.out 2>&1; \
  scripts/sweep-diff.sh /home/corey/.claude/jobs/4fd5573d/tmp/base163.log \
  /home/corey/.claude/jobs/4fd5573d/tmp/cur163r13.log \
  >> /home/corey/.claude/jobs/4fd5573d/tmp/sweepr13.out 2>&1; \
  echo SWEEP_COMPLETE >> /home/corey/.claude/jobs/4fd5573d/tmp/sweepr13.out' &
```

Before reading its result, confirm no second sweep is running and that
`wc -l` on the log equals the on-disk test count.

## Open, for Corey

1. **`quipu setup`** — now the only blocking item. Hooks unwired; the push
   above may not have reached the hub.
2. Recommended, not done: rename the two N45 probes `tsymex_*` so
   `symex-mingw`'s corpus picks them up. Unverifiable without pushing — though
   now that the branch IS pushed, this is cheaper to try than it was.
3. **The convergence question, still unanswered.** Rounds 10, 11 and 12 each
   found real defects in the previous round's fixes. Round 13's lenses will
   run against round 12's fixes. Whether to keep looping or stop at a green
   gate and file the remainder is Corey's call; the mandate says keep fixing,
   so that is the default in progress.

## Round 13 — in progress

Scope: `5056b46..HEAD`, i.e. round 12's own four fixes (`3dea487`, `da8855b`,
`ec0733d`, `b1e2eb1`) plus the coupled `derive-ci-suites.ps1` / `nelli.nimble`
surface. The premise is the one the last three rounds established: **a fix is
a new surface.** Rounds 10, 11 and 12 each found a real defect in the previous
round's fixes, so round 12's fixes get audited exactly as the code they
replaced was.

Four lenses dispatched in parallel, all `sonnet`, all **read-only** — the
round-13 sweep owns this working tree and a concurrent `dt-bounded.sh` on the
same test file clobbers one shared binary. The briefs say so explicitly.

| lens | primary targets |
|---|---|
| Security | word-splitting/injection through the new `nelli.nimble` parse; gate integrity as a security property (can it silently under-test and still report pass?); macro insertion into `try`/`finally`/effect-annotated procs; TOCTOU from the real `sched_yield` |
| Design & ergonomics | is `derive-ci-suites.ps1` now the *third* copy of the test/defines mapping, i.e. the same defect one hop over? is `{.jitterPoints.}` a faithful member of the `{.cover.}`/`{.symexOpaque.}` family? is `when name == "..."` a stringly-typed coupling a rename breaks silently? |
| Liveness | end-to-end producer/consumer traces for `obligations`/`parseErrors`, `obligationsLive`/`parseDeclines`, the new `toJson`, `formatCampaignSummary`, `{.jitterPoints.}` in `src/` vs only `tests/`, whether the zero-insertion warning can actually fire, and whether `$skipReasons` is consulted or merely declared |
| Correctness | hand-simulate the defines parser against the real `nelli.nimble` (empty value, absent value, trailing comment on the last entry, `#` inside a value) — a 4-field record misalignment runs test N with test N+1's defines and still reports pass; node-kind gaps in the pragma's recursion (`nnkStmtListExpr`, `nnkIfExpr`, expression-`case`, `nnkDefer`, `finally` semantics); `fieldPairs` merge completeness; template re-evaluation of the now-explicit `w` |

The liveness brief carries one correction forward deliberately: an earlier
round claimed `CampaignStats` was "user-visible at campaign end" and that was
**false** — nothing rendered it. The brief tells the lens to re-derive the
current state from the code and inherit neither the claim nor its retraction.

Gate and CI for this round are running concurrently; see below.

### Round 13 findings — consolidated after adversarial verification

Two verifications moved severity in BOTH directions, which is the point of
running them.

| id | sev | source | anchor | finding |
|---|---|---|---|---|
| R13-1 | High | Security | `scripts/sweep.sh:255` | Round 12's "never a silent no-op" guarantee is a compile-time `warning`, but the gate runs `dt-bounded.sh ... >/dev/null 2>&1`. The warning lands on discarded stderr — the mechanism built to stop silent under-instrumentation is itself silent under the only harness that runs it. |
| R13-2 | High | Correctness | `src/nelli/parallel.nim:390-441` | `nnkDefer` undispatched: a read-modify-write race inside `defer:` gets zero jitter points, silently, because the warning fires only on a zero TOTAL count. |
| R13-3 | Med (was High) | Design | `src/nelli/fuzz.nim:912` | `toJson` dispatches `float` by type forty lines below the sibling documenting why `float` must be matched by name. |
| R13-4 | Med | Design | `concolictaxonomy.nim`, `fuzz.nim` | ~12 near-identical enum-walk loops, each duplicated across its text and JSON sibling. `fieldPairs` closed "forgot a field", not "forgot a renderer". |
| R13-5 | Med | Security + Correctness | `scripts/sweep.sh:158-172` | Count floor admits a wrong-but-same-cardinality parse: a value containing `\"` truncates yet still yields one match. Found independently by two lenses. |
| R13-6 | Low (was Med) | Correctness + Design | `src/nelli/parallel.nim:364-371` | `nnkWhenStmt` has `nnkDefer`'s gap, and the doc's rationale is wrong — it conflates `when`-as-expression with `when`-as-statement. `coverage.nim:266` already does it right. Latent: no current target uses `when`. |
| R13-7 | Low (was High) | Design | `nelli.nimble:19-22` | "Single source of truth" overreads its scope. No live collision; `symexCiLeanB5` is a CI-timeout lever, not a correctness gate. |
| R13-8 | Low | Security | `scripts/sweep.sh:128` | `sed` range lacks an end-anchor check; a reformatted `}.toTable()` runs to EOF. |
| R13-9 | Low | Security | `scripts/sweep.sh:146` | A legitimate `#` in a value hard-aborts the sweep. Fail-safe, but a plausible edit bricks the gate. |
| R13-10 | Low | Design | `scripts/sweep.sh:211-213` | The drift extraction parses the same fragile file with no sanity check, while its sibling three paragraphs up now has one. |

**Liveness: clean.** Every mechanism traced to a live producer and consumer.
It also re-derived the `CampaignStats` question from source and landed on the
accurate reading rather than inheriting either the old false claim or its
retraction.

**R13-1, R13-2 and R13-6 are one defect, not three.** An allow-list of node
kinds plus a total-count-only warning produces silent partial instrumentation
*by construction*. Round 12 added six arms; round 13 found two missing. Adding
two more guarantees round 14 finds a third. The fix is therefore shape-level:
add the arms, but also warn on ANY undispatched statement-holding node kind so
future gaps report themselves, and upgrade the zero-insertion case from
`warning` to `error` — because R13-1 proves a warning is invisible to the gate,
and the build is the one channel the gate cannot discard.

### A lead worth more than the finding that produced it

Verifying R13-7 turned up a mechanism nobody in this review had considered:
Nim auto-loads a per-file `<test>.nim.cfg`, and **three `tsymex_*` suites
already use it** to carry a correctness-critical define
(`-d:symexTestInjectWalkerFault`) straight through the Windows corpus job with
no parser at all. The entire `extraDefines` table, its shell parser, the count
floor, the NUL transport and the `dt-bounded.sh` plumbing — the subject of
findings across rounds 11, 12 and 13 — may exist to do what Nim already does
natively. An agent is testing whether that whole mechanism can be deleted,
including git archaeology on whether `.nim.cfg` was considered and rejected
for a stated reason. Not touched yet; it changes the gate.

### Gate discipline — a self-inflicted error, recorded

The round-13 gate was launched and then, while it ran, fix agents were
dispatched that edit `src/nelli/parallel.nim` and `src/nelli/fuzz.nim`. Since
`sweep.sh` compiles each test from the WORKING TREE as it reaches it, and
those modules are transitively imported by nearly every test, the run splits
into "compiled before the edits" and "compiled after". That result is not
noisy, it is uninterpretable — and a partially-valid log reading as a real
result is precisely the round-10 mistake.

The run was killed at 220/496 and its artifacts renamed
`cur163r13.CONTAMINATED.log*`. **Order the loop gate-then-fix, or fix in a
worktree.** Killing it also needed the process GROUP of the original `setsid`
wrapper: `kill` on the `xargs -P6` pool PID orphans its in-flight
`bash -c run_one` children to init, which keep launching fresh `dt-bounded.sh`
runs and make the sweep look alive after it was killed.

The authoritative round-13 gate runs AFTER round 13's fixes land, against a
quiet tree.

## CI — all three Windows legs GREEN on `5056b46`

| leg | run | duration | result |
|---|---|---|---|
| `fuzzer-mingw` | 35472097646 | 9m53s | success |
| `fuzzer-msvc` | 35472097640 | 36m59s | success |
| `symex-mingw` | 35472097655 | 45m37s | success |

This closes the open question the push was taken for. It is the **first
Windows verification of 86 commits**, covering every walker bump from 134 to
140 and all of rounds 8-12. Specifically exercised, and now known good:

- the six `tsymex_r6_*` suites that `scripts/sweep.sh` skip-lists on Linux
  (see the `symex-r6-linux-hangs` memory) — they run for real only here;
- `derive-ci-suites.ps1`'s `$skipReasons` entry for
  `tsymex_snd3_6_equality_loop`, added at `ab7b9e0` and **never executed
  before this run**. No corpus-count change and no `throw` from the sanity
  block, so the entry parses and filters as intended.

`symex-mingw` at 45m37s is up from 41m18s on 2026-09-18 at `26418f3`, which is
within the noise of a hosted runner and consistent with the corpus having
grown by the round 8-12 suites.

## `.nim.cfg` supersedes `extraDefines` — verified, and being implemented

The investigation returned WORKS with no blocking reason, and the archaeology
is the part that matters:

- The `.nim.cfg` precedents (`505354c`, `85603f5`, `a0bfeff`) predate
  `extraDefines` by ~2 months, and `docs/rfc/0001-chapulin-hardening.handoff.md:926`
  documents `505354c` establishing exactly this pattern — including the
  `.gitignore` gotcha, already handled by the `!tests/*.nim.cfg` negation at
  `.gitignore:14`.
- `extraDefines` arrived in `233c7d1`, whose own message says it mirrors "the
  existing per-suite define precedent in **symex-mingw.yaml**" — i.e. it was
  modeled on a CI workflow's inline conditional rather than on this repo's own
  older sibling-file convention.
- **`.nim.cfg` was never considered and never rejected.** No stated reason
  exists anywhere in the record. Six findings across rounds 11-13 (D1, D4, S1,
  L12-1, Q1, C7) all repaired bugs *inside* the table and its parser; none
  asked whether the table should exist.

Every invocation path was audited and is path-based, so the sibling cfg
applies: `dt.sh:16`, `dt-bounded.sh:39`, `sweep.sh:255`, `dt-crosswin.sh:33-40`,
`nelli.nimble:750`, `symex-mingw.yaml:253-256,405-408`, both `fuzzer-*` main
loops. The only `--skipProjCfg --skipParentCfg --skipUserCfg` in the repo is
one unrelated step compiling `tests/tz3free_probe.nim`.

So **R13-5, R13-8, R13-9 and R13-10 are closed by deletion, not by patching** —
they are all findings in the parser being removed. A bonus defect closes with
them: today a bare `scripts/dt.sh c tests/tprobe_n45stats.nim` silently
compiles the `skip()` stub, because only `sweep.sh` and `nimble test` pass the
define; after the change every invocation path gets the real assertions.

Not expressible by `.nim.cfg`: `symex-mingw.yaml:399-402`'s `-d:symexCiLeanB5`,
which must be ON in the container nimble task and OFF on the mingw leg. That
is a third, separate mechanism, untouched by this change and correctly so.
(Nim's cfg format does support `@if`/`@end` if a future entry needs backend or
OS variance without a third mechanism.)

## Round 13 fix agents — three dispatched, disjoint files

| agent | findings | files |
|---|---|---|
| jitterPoints completeness | R13-1 (macro side), R13-2, R13-6 | `src/nelli/parallel.nim`, `tests/tparallelcheck.nim` |
| renderer name-vs-type + dedup | R13-3, R13-4 | `src/nelli/fuzz.nim`, `src/nelli/smt/concolictaxonomy.nim`, `tests/tsymex_163rev_concolic_diagnostics.nim` |
| `.nim.cfg` migration + gate diagnostics | R13-5, R13-8, R13-9, R13-10, R13-1 (gate side) | `nelli.nimble`, `scripts/sweep.sh`, `scripts/dt-bounded.sh`, `tests/tprobe_n45stats.nim{,.cfg}` |

Load-bearing instructions recorded so a resumed session does not soften them:

- The pragma fix must be **shape-level, not two more arms**: warn on ANY
  undispatched statement-holding node kind, so future gaps report themselves.
  Round 12 added six arms and round 13 found two missing; a third round of
  whack-a-mole is the failure mode to avoid.
- The zero-insertion case becomes an **error, not a warning** — R13-1 proves a
  warning is invisible to the gate, and the build is the one channel the gate
  cannot discard. If that breaks an existing annotated proc, fix the proc; do
  not weaken the error back.
- The self-reporting warning added above must **stay** a warning — a partially
  instrumented proc is still useful.
- The renderer agent must **audit the siblings**, not just fix the `float`
  instance: the bug class is type-dispatch where the sibling uses name-dispatch.
- The renderer refactor must not over-abstract; a helper with eight boolean
  parameters is worse than two clear loops. Report what was deliberately left
  duplicated.
- Gate diagnostics must **surface, not escalate**: the suite is not green on a
  good day and the contract is "what moved against a baseline". Warnings that
  fail the gate would break that contract.
- New tests for the pragma are probabilistic: report the **measured** rate,
  never an unmeasured claim of reliability.

### Round 13 fixes — landed

| sha | findings | what landed |
|---|---|---|
| `8454a94` | R13-2, R13-6, R13-1 (macro side) | `nnkDefer` + `nnkWhenStmt` arms; self-reporting fallback; zero-insertion upgraded `warning` -> `error` |
| `e244a4e` | (found BY the new fallback) | `nnkPragmaBlock` arm — `{.cast(gcsafe).}: <body>` |
| `73d7a80` | (found BY the new fallback) | `nnkStaticStmt` moved to a deliberate exclusion; two exclusion categories separated |
| `6ab0691` | R13-3 | `toJson(CampaignStats)` matches `execsPerSec` by name; `float` out of the generic bucket |
| `491b3c1` | R13-4 | `renderEnumCounts`/`renderFloatSeq` shared by both renderers; 16 loops collapsed |
| `afb261c` | R13-5, R13-8, R13-9, R13-10 | `extraDefines` deleted; `tests/tprobe_n45stats.nim.cfg` |
| `d3da227` | R13-1 (gate side) | sweep captures and surfaces compiler warnings |

AST shapes were confirmed with `macros.dumpTree` at every step rather than
recalled, and every probabilistic test reports a MEASURED rate: `defer` 20/20,
`when` 20/20, `{.cast(gcsafe).}` 20/20, each over 20 distinct seeds.

**The self-reporting fallback justified itself immediately.** It was added so
that future missing node kinds would report themselves instead of waiting for
a review round. Within minutes it found `nnkPragmaBlock`, then `nnkStaticStmt`,
then a fifth kind. Round 12 added six arms by hand and round 13's lenses found
two missing; the mechanism then found three more on its own. That is the
difference between a fix and another turn of whack-a-mole.

**The durable result is a three-way classification**, not an arm count. A
maintainer meeting a new node kind now picks one:
- `jitterNestedCallableKinds` — wrong *attribution*: a separate callable's own
  body, instrumenting it misattributes.
- `jitterCannotExecuteAtRuntimeKinds` — cannot *execute* there. Currently just
  `nnkStaticStmt`, proven by the real compiler error (`cannot 'importc'
  variable at compile time; sched_yield`) — `parallelJitterPoint` wraps a
  syscall and Nim's CTFE VM cannot run it. Instrumenting is actively wrong,
  not merely pending.
- otherwise it warns, and the warning now states that meaning explicitly
  rather than saying "unhandled" (which is true of the exclusions too).

`parallelJitterPoint` was confirmed genuinely `gcsafe` before the pragma-block
arm was added — a plain non-cast `{.gcsafe.}: parallelJitterPoint()` block
compiles, so the compiler *proves* it rather than merely accepting a cast.
Inserting into `{.cast(gcsafe).}` therefore cannot launder a real effect
violation, because there is none to launder.

### Open for Corey — a genuine fork, not a gap

**Trailing-block calls (`withLock lock: <body>`).** The fallback warns on
`nnkCommand`/`nnkCall` carrying a trailing `nnkStmtList`. This was deliberately
NOT force-classified into either exclusion set, and the reasoning is sound: a
trailing block's body belongs to whatever macro or template receives it, which
an `untyped`, pre-expansion macro cannot inspect. Instrumenting is sound for
`withLock` specifically and unsound in general — a macro that pattern-matches
its block's exact shape would break.

It matters because `withLock` is plausibly the **commonest** real shape for a
concurrency SUT, i.e. exactly what `{.jitterPoints.}` exists for. The options:

- (a) leave it warning — safe, honest, and what ships today;
- (b) instrument the trailing blocks of a known allow-list of concurrency
  macros (`withLock` and friends) — targeted and safe, but a stringly-typed
  macro-name allow-list;
- (c) blanket-instrument trailing blocks — unsound.

(c) is out. Between (a) and (b) the answer turns on how much unsoundness risk
is worth the coverage of the common shape, which is a scope/risk call rather
than something the quality bar decides. Recorded rather than chosen.

### Newly surfaced by the gate fix, NOT a round-13 regression

Making the gate stop discarding compiler stderr revealed that **every test in
the tree compiles with roughly 14-23 warnings** — `UnusedImport` and
`Deprecated`, attributed to real files under `src/nelli/` (`engine.nim`,
`targeting.nim`, `dsl_parser.nim` among them). Order 8000 warnings in total.
Always present, always thrown away.

This breaks the R13-1 fix as first delivered: burying one actionable
`{.jitterPoints.}` warning in eight thousand is not materially better than
discarding it. The correction in progress makes warnings **delta-based, on the
same footing as pass/fail** — which is this repo's existing gate contract
(`CLAUDE.md`: the suite is never green on a good day, so the gate is what
MOVED against a recorded baseline, never "the sweep passed"). Warnings have
the same character: never zero, so the total is a trend and the delta is the
gate. That requires a canonical, order-stable sidecar or the diff rots on
line-number churn.

The breakdown by category is being collected to decide what the debt IS:
`UnusedImport` is a cosmetic chore, but `Deprecated` warnings naming our own
`src/` APIs would be real rot and a finding in its own right. Not being fixed
in this round either way.
