+++
type    = "rfc"
id      = "0016"
title   = "RFC — native-parity hardening: the walker agrees with the compiled program, or declines"
state   = "in-progress"
wiring  = "unproven"
review  = "unreviewed"
profile = "rfc-flow@6"
blocked_by = ["0005"]
size = "l"
value = "high"

[[item]]
id       = "exit-criterion"
title    = "What exit criterion closes an open-ended RFC tracked by findings rate?"
question = "Should RFC-0016 close on §3.3's proposal (work list empty, 500 fuzzer CPU-hours with no new soundness finding in the last 250, and a release cycle with no consumer soundness finding), or on a different criterion?"
state    = "resolved"
owner    = "corey"
kind     = "design"
reversible = "reversible"
recommendation = "exit-criterion.A"
lean     = "A gives a stated, measurable bar that shrinks only when search stops finding things; the figures are a starting point and can be revised without changing the shape."
choice = "exit-criterion.B"
reason = "Corey 2026-11-06: close on an empty work list only; no fuzzer-hours or quiet-cycle bar"

[[option]]
id    = "exit-criterion.A"
of    = "exit-criterion"
title = "§3.3's proposal: empty work list, 500 fuzzer CPU-hours with none new in the last 250, one quiet release cycle"
cost  = "About two weeks of the 12-core worker per window, and it waits on the fuzzer (slice D1) existing."

[[option]]
id    = "exit-criterion.B"
of    = "exit-criterion"
title = "Work list empty only"
cost  = "Cheap and familiar, but it is the RFC-0005 bar, whose list grew by remainders and never shrank."

[[item]]
id       = "upstream-reports"
title    = "File the three upstream reports in §5.6?"
question = "Should the Nim raise-path destroy, the Z3 mk_unique check and the Z3 spacer pob_queue::reset invalid read be filed upstream now, or held?"
state    = "resolved"
owner    = "corey"
kind     = "risk"
reversible = "one-way"
recommendation = "upstream-reports.B"
lean     = "File the Nim and spacer reports, which have reductions; hold mk_unique until S8cj reduces it, since the sort did not reproduce it at e497dcf."
choice = "upstream-reports.B"
reason = "Corey 2026-11-06: file the Nim raise-path destroy (UPS-01) and the Z3 spacer pob_queue::reset invalid read (UPS-03); hold mk_unique (UPS-02) until S8cj reduces it"

[[option]]
id    = "upstream-reports.A"
of    = "upstream-reports"
title = "File all three now"
cost  = "The mk_unique report has no reduction yet and may not reproduce."

[[option]]
id    = "upstream-reports.B"
of    = "upstream-reports"
title = "File the two with reductions; hold mk_unique for S8cj"
cost  = "A second decision later for mk_unique."

[[option]]
id    = "upstream-reports.C"
of    = "upstream-reports"
title = "Hold all three"
cost  = "Upstream fixes, which nelli and nim-z3 both work around today, do not start."

[[item]]
id       = "fork-c-clean-replay"
title    = "RFC-0005's fork (c): a gated clean replay as a safety net for clean-path sxSat (INF-02)"
question = "Should a clean-path sxSat also be replayed natively, gated by a setting, so that a false sxSat on a clean path is caught at verdict time?"
state    = "resolved"
owner    = "corey"
kind     = "design"
reversible = "reversible"
recommendation = "fork-c-clean-replay.A"
lean     = "The blockers were trusted verdicts on clean paths; a replay gate would have refuted the false sxSat half of them, at a run-time cost a setting can switch off."
choice = "fork-c-clean-replay.B"
reason = "Corey 2026-11-06: no clean-path replay setting; rely on native pins and the differential fuzzer"

[[option]]
id    = "fork-c-clean-replay.A"
of    = "fork-c-clean-replay"
title = "Add it, off by default, on in nelli's own suites and the differential fuzzer"
cost  = "Replay runs the SUT at verdict time on clean paths too: effects and wall time for whoever turns it on."

[[option]]
id    = "fork-c-clean-replay.B"
of    = "fork-c-clean-replay"
title = "Do not add it; rely on native pins and the fuzzer"
cost  = "A false sxSat on a clean path reaches a consumer unless a pin or the fuzzer finds the shape first."

[[item]]
id       = "fromcache-field"
title    = "Remove the always-false SymexResult.fromCache, or keep it?"
question = "SymexResult.fromCache is never true, because symexFind has no cache (WA-11). Should 0.10.0 remove the field, a breaking change, or keep it documented as always false until a symexFind cache exists?"
state    = "resolved"
owner    = "corey"
kind     = "design"
reversible = "one-way"
recommendation = "fromcache-field.A"
lean     = "Removing it breaks every caller that reads it and gives no user anything, since it already reads false; keep it until a symexFind cache gives it a producer, or remove it then if that cache never comes."
choice = "fromcache-field.B"
reason = "Corey 2026-11-06: remove SymexResult.fromCache in 0.10.0 with a migration note; the release breaks the API anyway and the field has no producer"

[[option]]
id    = "fromcache-field.A"
of    = "fromcache-field"
title = "Keep it, documented as always false, until a symexFind cache exists"
cost  = "A field with no producer stays in the public type, which the zero-tech-debt rule counts as dormant substrate; its doc must stay accurate."

[[option]]
id    = "fromcache-field.B"
of    = "fromcache-field"
title = "Remove it in the next minor (0.10.0), with a migration note"
cost  = "A compile break for every reader of the field, for no change in what any program observes."

[[claim]]
id    = "fromcache-field.c1"
of    = "fromcache-field"
text  = "No code path sets SymexResult.fromCache to true; its doc says it is always false because symexFind takes no ExampleDatabase."
basis = "read"
ev    = ["src/nelli/smt/types.nim#/fromCache\\*: +bool/", "src/nelli/symex.nim#/macro symexFind\\*/"]

[[claim]]
id    = "fromcache-field.c2"
of    = "fromcache-field.A"
text  = "The cache-hit flag users can read is SymexFinding.fromCache, which symexFindAllWitnesses sets on a hit, so keeping the SymexResult field costs no user a signal."
basis = "read"
ev    = ["src/nelli/engine/types.nim#/fromCache\\*/"]

[[decision]]
id       = "D-0016-1"
state    = "settled"
title    = "RFC-0016 closes when the §5 work list is empty: every item fixed with native pins, or its decline recorded with the reason it stays. No fuzzer-hours window and no quiet-release-cycle bar"
resolves = ["exit-criterion"]

[[decision]]
id       = "D-0016-2"
state    = "settled"
title    = "No gated clean-path replay. A false sxSat on a clean path is caught by native pins and the differential fuzzer (D1), not at verdict time"
resolves = ["fork-c-clean-replay"]

[[decision]]
id       = "D-0016-3"
state    = "settled"
title    = "File UPS-01 (Nim raise-path destroy) and UPS-03 (Z3 spacer pob_queue::reset invalid read), the two with reductions; hold UPS-02 (mk_unique) until S8cj reduces it"
resolves = ["upstream-reports"]

[[decision]]
id       = "D-0016-4"
state    = "settled"
title    = "Remove SymexResult.fromCache in 0.10.0 with a migration note (INT-39). That release breaks the API anyway, and the field has no producer"
resolves = ["fromcache-field"]

[[decision]]
id       = "D-0016-5"
state    = "settled"
title    = "Wave 1 (the seven clean false verdicts of §5.0) ships as 0.9.2, after the /architect rounds on §8-§13"

[[decision]]
id       = "D-0016-6"
state    = "settled"
title    = "Tracking is about twenty quipu rows plus the generated universe ledger (§8.2), not one row per cell"

[[decision]]
id       = "D-0016-7"
state    = "settled"
title    = "--mm:refc is refused by name at symexFind macro time (admitBuild, §8.3), not modelled"

[[decision]]
id       = "D-0016-8"
state    = "settled"
title    = "Int-offset soundness (N24, #166, #169) is owned by RFC-0014; RFC-0016 carries a pointer row only"

[[decision]]
id       = "D-0016-9"
state    = "settled"
title    = "No signed-wrap setting: C undefined behaviour is an outcome the build profile defines (K10, §9)"

[[slice]]
id    = "D1"
title = "Differential fuzzing harness (§4, §10): K8a skeleton with one family in Wave 2, families from the admission tables in Wave 4"
state = "pending"

[[slice]]
id    = "W1"
title = "Wave 1 / 0.9.2 (§11): K9a pin helper, then W1-a..W1-g (13 slices) fix the seven clean false verdicts of §5.0; W1-z integrates and gates the release"
state = "pending"

[[slice]]
id    = "W2"
title = "Wave 2 (§11): CI-A/CI-B Linux legs, K9 pin helper, ADM-1 admission spike, K1a universe ledger with ratchet, K7 Survivors type, K8a fuzzer skeleton"
state = "pending"

[[slice]]
id    = "W3"
title = "Wave 3 (§11): admission tables K2-K6 and K10 undefined behaviour as an outcome, each shrinking the K1 allowlist"
state = "pending"

[[slice]]
id    = "S8cg"
title = "Batch-7 integration findings (items 2, 3, 4, 5, 7, 8): var openArray view copied at the call, read-only later arguments, ti_tuple and bb_rep_sym_empty_hit exact again, index call through a proc value, timing"
state = "pending"

[[slice]]
id    = "S8ch"
title = "S8cc's remainder: address of a global in a walked callee, unsafeAddr of a by-value array formal"
state = "pending"

[[slice]]
id    = "S8ci"
title = "S8by's item 3 reopened: a term order that earns its cost, r4_strip back to S8bm, configdefaults_depth under 60 s, wide factoring decided again"
state = "pending"

[[slice]]
id    = "S8cj"
title = "S8by's process-level findings: thread-history spend; Z3 5.1's mk_unique check on wide factoring"
state = "pending"

[[slice]]
id    = "S8ck-r"
title = "S8ck after item 1: nim-z3 leaks, Z3Ast hooks, nim-z3 suite on Z3 5.1, leak gate that fails on invalid access, examples in nim-z3 CI, spacer reduction, generated hooks on the raise path"
state = "pending"

[[slice]]
id    = "S8co"
title = "S8cf's remainder: auto-possession, ignore_skip_arg, detect_repeat on the JIT, SKIP:NAME counts, (*ANY) under the JIT scan, replace and count gaps, unbounded refutation past the safe length"
state = "pending"

[[slice]]
id    = "S8cp-r"
title = "S8cp items 4-8: rc=139 of p7, n42 on cpp, stack size off Linux, declined shapes, declined magics"
state = "pending"
[[slice]]
id    = "rv0005-lows"
title = "The RFC-0005 code review's open Lows (INT-28 to INT-38): replay child hardening, cache-key coverage, replay and settle policy, fuzzer-path liveness, design cleanups, exit-group guards, finding-collector edges, precision probes, cache hygiene"
state = "pending"
+++

# RFC — native-parity hardening: the walker agrees with the compiled program, or declines

- **Status:** in-progress — opened 2026-11-02 when Corey split RFC-0005.
  RFC-0005 ends at the 0.9.0 tag, once every open soundness item that is
  worse than `main` (6cbfe8f) is fixed. Everything else moves here: soundness
  items with the same severity as `main`, precision gaps, crashes and hangs
  that match `main`, CI and test-time work, and the exact models behind the
  declines RFC-0005 added. Nothing was dropped. This RFC is open-ended: it has
  no fixed slice list, and it is tracked by the rate of new findings (§3). The
  exit criterion is §3.3: the work list empty (Corey, 2026-11-06, item
  `exit-criterion`), measured as §12 defines it. **Revised 2026-11-06 by
  `/architect` round 1:** a read-and-probe of the whole walker surface found
  seven clean false verdicts no row named (§5.0), so §8-§13 add a closure
  design (one admission mechanism, a generated universe ledger, undefined
  behaviour as an outcome) and a slice order; round 2 the same day reshaped
  admission into per-axis verbs, corrected §9 (shifts are defined), split
  Wave 1 into slices with RED specs, and reconciled §5 against head.
- Category: symex
- Size: L
- Value: high
- **Depends on:**
  - RFC-0005 (branch-scoped-degrade / soundness channels) — hard. Every item
    here is defined against RFC-0005's soundness channels, its decline
    lattice and its replay, and most of the moved slices are based on its
    channel branch. Work may start before the tag (S8cm is already running);
    an item that lands before the tag keeps its RFC-0005 row and is closed
    here by a native re-pin at the tag head.

**Path convention.** As in RFC-0005: bare `runtime.nim`, `types.nim`,
`canonicalize.nim`, `dsl_parser.nim` mean `src/nelli/smt/…`.

**Sources.** Every item names where it came from: an RFC-0005 slice and item
(for example "S8cd item 6"), a row of the release-blocker sort ("sort S3",
"sort U4"; the sort compared `main` 6cbfe8f with the channel at e497dcf), or a
worker report (`origin/worker-sls2:worker-reports/<name>.md`). Job files are on
`origin/worker-jobs:jobs/<slice>.md`.

## §0 — Motivation

RFC-0005 set out to separate over-approximation from under-approximation, so
that a decline caused by one did not throw away a verdict the other had
earned. It did that. It also lifted a large number of declines, slice by
slice, into definite verdicts, and that is where its release blockers came
from.

The blockers the 2026-11-02 sort found (B1–B26, plus W1 and W2) were not
twenty-eight different bugs. Almost all of them had one cause: **the model
treated a value as a private copy where Nim shares memory, or evaluated in an
order Nim does not use.** A by-value argument that Nim passes by address and
the callee then writes through a global (B3–B6). A pointer stored to a global
the path had only read (B1). A call inside an lvalue evaluated twice by the
model and once by the program (B7, B8). A set operand built eagerly or late
depending on its size (B2). A `setLen` that read the seq before its length
argument wrote it (B9). A destructor, an opaque routine or an `{.emit.}` that
writes a global the walker assumed unchanged (B22–B26). In each case `main`
declined, often by accident (a walker fault, an unregistered magic), and the
channel gave a clean, trusted, wrong verdict.

The pattern is that declines were lifted faster than aliasing was proved. A
decline is safe by construction. A definite verdict is safe only if the model
agrees with what the compiled program does, and the slices that lifted the
declines checked the shapes they were written for, not the neighbouring shapes
that share memory differently.

Hence the rule this RFC is built on:

> **A definite verdict that replaces a decline is a soundness risk until it is
> proven against native execution.**

Proving means a native run of the same SUT, on the same build, that reaches
(or provably cannot reach) the label, pinned in a test. A verdict that only
agrees with the model's own reading of the code is not proven.

## §1 — Scope

In scope:

- soundness items whose severity on the channel is the same as on `main` (the
  sort's SAME rows and anything later classified the same way);
- precision: every decline RFC-0005 added or widened, and every older decline
  a consumer can reach, gets an exact model or a recorded reason it stays;
- crashes, compile stops and hangs that `main` shares;
- CI and test-time work: the 60 s per-file convention, shard budgets, backend
  and Z3-version coverage;
- infrastructure: the differential fuzzer (§4), the findings ledger (§3),
  nim-z3 work, and upstream reports.

Out of scope: any soundness item worse than `main`. Those are RFC-0005 tag
blockers and stay there. If a finding here turns out to be worse than the last
release, it becomes a release blocker under §2.4, not a precision item.

## §2 — Rules carried over from RFC-0005

### §2.1 Fail-closed allowlists

The walker decides only what is proved and declines anything it does not
know. Concretely, a model is admitted by an allowlist of shapes it has been
checked on, not by a denylist of shapes known to be wrong. S8cq's by-value
fix is the model: an allowlist of types where Nim copies, or a callee proved
not to write; everything else declines. A new shape, a new type, a new build
setting or a new library version starts out declined. Lifting a decline is a
change to the allowlist, with its native pins in the same commit.

### §2.2 Native pins on the same build

Every row in this RFC, and every verdict a slice here changes, is pinned
against a native run of the same SUT on the same build: the same backend (c
or cpp), the same Z3 build, the same PCRE build, the same compile options.
"Same build" matters: RFC-0005 found verdicts that differ by memory manager
(`ll_*`, `lg_*` in S8cn), by set size (S8cd item 4), by PCRE build (S8bt,
S8cf) and by check options (S8cu). A pin that ran natively on one build says
nothing about another. A `sat` pin records the native hit; an `unsat` pin
records the native search that did not hit and says whether it was
exhaustive.

### §2.3 Walker version discipline

Every walker semantics change bumps `symexWalkerVersion` (`canonicalize.nim`),
updates the `==` pin in `tests/tsymex_phase15_CR2_cachekey.nim`, and adds a
`>=` floor pin in the slice's own test file. Parallel slices take provisional
numbers and the integrator assigns one number above every floor, as RFC-0005's
batches did (§7 there). A change that alters no verdict says so and leaves the
number alone.

### §2.4 The release rule

An open soundness item that is **worse than the last release** blocks a tag.
An open soundness item with the **same severity** as the last release may ship,
listed as a known gap in the release's migration note. "Worse" is decided by a
three-way table (last release, head, native) on the same build, as the
2026-11-02 sort did; a compile stop or a decline on the release against a false
verdict on the head counts as worse, and so does a false verdict on the
release against a process kill on the head (sort W1, W2). Once 0.9.0 is
tagged, "the last release" for this RFC is 0.9.0.

## §3 — Tracking

### §3.1 Open-ended, closed by a measured list

RFC-0005 was tracked by a slice list that grew by remainders: each slice
reported what it found and did not fix, and that became the next slice. The
list never shrank. This RFC does not close on a findings rate (D-0016-1): it
closes when §12's test says the list is empty. Findings are still recorded
with their source (slice, consumer, review, fuzzer) in the handoff's F
ledger, so that a quiet week with nobody looking is not read as progress;
the weekly rate report INF-03 proposed is dropped.

### §3.2 How a finding is recorded

Each finding gets a row in the findings ledger, kept in this RFC's handoff
(`0016-native-parity-hardening.handoff.md`, created with the first finding
recorded after this document), newest at the bottom:

| Field | Content |
|---|---|
| `F-NNNN` | sequential id |
| date | when it was observed |
| class | `soundness`, `precision`, `crash`, `hang` or `ci` (below) |
| severity vs release | `worse`, `same`, `better`, or `n/a` for precision and CI |
| source | fuzzer seed and generator version, slice, consumer, review |
| shape | the smallest SUT that shows it, or a probe path |
| release / head / native | the three-way table, with backend, Z3 and PCRE build |
| fix | slice and sha, or the reason it stays |
| state | `open`, `fixed`, `declined` (sound decline, exact model pending), `refuted` |

Classes:

- **soundness**: a trusted verdict that native execution contradicts: `sxSat`
  whose witness does not reach the label, `sxUnsat` for a label native
  execution reaches, `sxRaised` for an exception the program does not raise,
  or the reverse.
- **precision**: a decline where an exact model is possible, or a verdict
  that costs more than its budget.
- **crash**: the walker, the compiler under `symexFind`'s macro, or the
  process dies, or stops the compile on valid input.
- **hang**: a run that does not finish within its stated budget.
- **ci**: a test or leg that is slow, flaky, nondeterministic or not run.

A soundness finding that is `worse` goes to the release-blocker list of
whatever RFC owns the next tag; it does not wait in this RFC's precision queue.

### §3.3 What "done" means — **decided 2026-11-06: the work list alone**

Corey chose option B of item `exit-criterion` (decision D-0016-1): the RFC
closes when item 1 below holds. "Empty" is measured by §12: a test result,
not a reading of this list. Items 2 and 3 were the proposal and are not
part of the exit criterion; they stay here as the record of what was weighed,
and the differential fuzzer (§4) still runs as the search that feeds the work
list. The proposal was:

1. **The work list is empty**: each item in §5 is fixed with native pins, or
   its decline is recorded with the reason it stays (cannot be expressed in the
   theory, or measured as out of budget, with the number).
2. **The differential fuzzer has run 500 CPU-hours** on the full generator
   (§4) across c and cpp, Z3 5.1 and 4.13.4, Linux and at least one Windows
   leg, **with no new soundness finding in the last 250 of them**, and no new
   crash or hang in the last 100.
3. **No soundness finding from a consumer** across one full release cycle after
   the fuzzer's last soundness finding.

The figures are a starting point to argue with, not a measurement. 500 hours
is about two weeks of the 12-core worker. If the generator grows a new shape
family, the 250-hour window restarts for that family only.

## §4 — Differential fuzzing proposal

### §4.1 Why

Every blocker in the sort was found by hand: a person, or an agent, guessing a
neighbouring shape and running it natively. S8cq's report found that S8cn's
by-value decline still missed many types and routes; the next guess found more.
Hand search finds what the searcher thinks of. The rule in §0 needs a search
that does not depend on that.

### §4.2 Design

Use nelli itself. A nelli property generates SUT shapes from a small grammar,
emits each as Nim source, compiles it with `symexFind` over its labels and
with a native harness, and compares.

- **Generator.** A strategy over a typed Nim subset aimed at the defect class:
  module-level `var`s, by-value, `var`, `lent` and `openArray` parameters,
  closures and their captures, `ref`, `ptr`, `addr` and `unsafeAddr`, seq,
  string, Table, HashSet and small and large `set`s, tuples and case objects,
  `=destroy` / `=copy` / `=sink` hooks, calls inside lvalues and arguments,
  `inc` / `swap` / `setLen` / `+=`, opaque routines, and check-option pragmas.
  Each SUT has a few integer inputs and several labels.
- **Exhaustive small domains.** Inputs are drawn from small ranges (for
  example `0..7`) and declared to the walker with `symexAssume`. The native
  harness then enumerates every input, so "no native input reaches the label"
  is a proof, not a sample. This is what makes an `sxUnsat` checkable.
- **Oracle.** For each label: `sxSat` must have a witness that reaches the
  label natively; `sxUnsat` must have no input in the domain that reaches it;
  `sxRaised` must raise that exception type natively on its witness; a decline
  is never a soundness finding, and is counted for the precision rate.
- **Triage.** A disagreement is re-run on the last release. The pair gives the
  §2.4 severity automatically, so the fuzzer files `worse` and `same` findings
  separately.
- **Shrinking.** nelli's choice-sequence shrinking reduces the generated SUT,
  so the ledger records a small program, not a generated one.
- **Cost.** Compiling a one-SUT suite costs about 24 s on c (S8ca item 9), so
  each generated module carries many SUTs, and one compile serves all of them.
  The run cost is in the walk and the solver; the native enumeration is cheap.
- **Builds.** The same seed runs on c and cpp, and on both Z3 versions; a
  finding records the build. The PCRE differential leg S8co item 2 asks for is
  the same idea applied to regex, and should share the harness.
- **Where it runs.** A scheduled CI job on a Linux runner (§11, K8a),
  rotating one build row per night; it does not run on every push. (The
  first draft named the `sls2` worker, which has been offline since
  2026-11-03.) §10 revises the domain and the oracle.

### §4.3 What it is not

It does not replace native pins in slices: it finds shapes, and the slice that
fixes one still pins it. It does not test replay against real effects (quit,
foreign threads, files); the generator keeps SUTs effect-free except for
memory, unless a generator family for effects is added deliberately.

## §5 — Work list

### §5.0 Found by the 2026-11-06 research round

Six read-and-probe lenses over `83c1d304` (reports and the merged list,
W-01 to W-69 with its corrections to §5.1-§5.8, are in
`docs/rfc/0016-research/`; `MERGED-worklist.md` is the backlog this section
summarises). Seven clean false verdicts, each on the default or a documented
build; evidence V = re-run by the coordinator on one build, P = the lens ran
walker and native on one build. Every mechanism predates RFC-0005, so each is
expected to be `same` as `main`; each still gets its three-way row in W1-z.

| ID | Item | Evidence | Cause | Slice |
|---|---|---|---|---|
| W-01 | `except T as e:`: handler label false `sxUnsat`, raise target false `sxRaised` | V | `dsl_parser.nim:20460-20461` stores the `repr` as the type id | W1-a |
| W-02 | explicit `{.cursor.}` on a local: false `sxUnsat` and `sxSat` (c/orc, c/arc release, cpp) | V | `dsl_parser.nim:19771-19792` drops every local pragma but `noinit` | W1-b |
| W-03 | `--panics:on`: a label after a Defect is a clean `sxSat`; natively the process dies | V | the walker never reads `nimPanics` (only `symex.nim:2343`) | W1-c |
| W-04 | `float32` ↔ `float64` conversions, hidden ones included: false clean verdicts | P | transparent `else: parseExpr(operand)` at `dsl_parser.nim:10658`, `:10845` | W1-e |
| W-05 | `low(int) mod -1`, literal divisor: false `sxUnsat` (gcc folds to 0) | P | `runtime.nim:8862-8870` traps regardless of divisor or target | W1-d |
| W-06 | unsigned `div`/`mod` by zero: `sxRaised DivByZeroDefect`, natively SIGFPE | P | `dsl_parser.nim:4023-4025` lists unsigned beside signed | W1-d |
| W-07 | checks-off signed overflow modelled as wrap: `v + 1 > v` clean `sxSat` at `high(int)` | P | `runtime.nim:24500-24502` consumes the marker with no token | W1-d |

The rows of §5.1-§5.8 below are unchanged by this round. The reconciliation
lens found 16 of them closable at the tag head, 4 that close as a recorded
decline, 14 duplicates, 11 with stale evidence and 3 misclassified
(`E-reconcile.md`); those edits are round 2's, so the row ids stay stable
while §8 is reviewed.

Owners are left empty: the coordinator assigns them. "Moved slice" means a
job file on `origin/worker-jobs` written under RFC-0005; it keeps its id and
its scope, minus anything named as staying with RFC-0005.

### §5.1 Soundness, same severity as `main`

All are false verdicts on `main` 6cbfe8f and on the channel at e497dcf (sort,
"Same on both"). Several have a fix that landed in RFC-0005 batch 10 or is due
in batch 11; for those the item is to re-pin natively at the tag head and close
it, or reopen it if the fix did not hold.

Rows were reconciled against head `83c1d304` in `/architect` round 2 (2026-11-06); a closed row keeps its id.

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| SND-01 | Direct var-returning actual: `rab(t["a"], t, "a")` | sort S1; S8cq item 2 | Closed as a decline at head: `tests/tsymex_rfc0005_s8cq_varret.nim:84,158-159` pins `rab(t["a"], t, "a")` (`p01_r50` native hit, walker `sxUnknown`); `tests/tsymex_rfc0005_s8cq_byvalue.nim:126,162-163` (`vc_rx1`). S8cq landed in batch 11 (`47e3363e`). Exact model: PRC-36. | closed (decline; exact model PRC-36) |
| SND-02 | `$` of a negative int: `$x == "-5"`, `($x).len == 2`, `$x == ""`, `repr(x)` | sort S2; S8cb | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` native values; `:62-63` (`negs`/`negsu`), `:74-80` (char), `:81-99` (enum, string-named enum), `:116-118` (`repr`). S8cb merged `72b2c2b8`. | closed |
| SND-03 | `$` of a char: `$a == "a"` false `sxUnsat`, `$a == "97"` false `sxSat` | sort S3; S8cb | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` native values; `:62-63` (`negs`/`negsu`), `:74-80` (char), `:81-99` (enum, string-named enum), `:116-118` (`repr`). S8cb merged `72b2c2b8`. | closed |
| SND-04 | `$` of an enum, including a string-named enum | sort S4; S8cb | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` native values; `:62-63` (`negs`/`negsu`), `:74-80` (char), `:81-99` (enum, string-named enum), `:116-118` (`repr`). S8cb merged `72b2c2b8`. | closed |
| SND-05 | `ensureMove` of an int: `b == 0 and x != -1` false `sxSat` | sort S5; S8cb | `tests/tsymex_rfc0005_s8cl_magics.nim:208-218`: `nativeHits(sutEnsureMove)` then `clean(..., "em_dead", sxUnsat)`. | closed |
| SND-06 | `procCall` zero value: `r == 4 and k != 3` false `sxSat` | sort S6; S8cl | `s8cl_magics.nim:210,220-222` `declines(sutProcCall, "pc"/"pc_dead", "ProcCall")` after the native run; also `tests/tsymex_rfc0005_b10_integration_b.nim:9-12`. | closed (decline; exact model PRC-21) |
| SND-07 | `uncheckedAssign`, the other arm's bytes differ: `o.y != v` | sort S7; S8cp item 2 | Walker pinned `sxUnknown` on `diff` (`s8cp_unchecked.nim:229-230`); the file's native run (`:199-206`) covers only the shape where the other arm's bytes coincide (`same`). The sort's shape where they differ (`p_cp ua3_diff`, native HIT) has no SUT in the corpus: port it with its native hit beside the `sxUnknown` pin, then close as a decline. Exact model: PRC-37. | |
| SND-08 | A hook write through a local ref: `DR(r: r)`, `=destroy` writes `d.r[]` | sort S8 | `tests/tsymex_rfc0005_s8cs_routes.nim:525-526,542-549` (`HeapH` `=destroy` writes `d.r[]`), native `:603`, hits `:616,622`; walker `tests/tsymex_rfc0005_s8cs_routes_c.nim:292-293` `declined(heap1, …)`. | closed (decline; exact model PRC-04) |
| SND-09 | A hook on overwrite, global written first: `gW = 0; var d = mkD(k); d = mkD(k)` | sort S9 | `s8cs_routes.nim:110-113` (`w2`), native `:590`, hits `:608,622`, `declined(w2, …)` `:642-643`. | closed (decline; exact model PRC-04) |
| SND-10 | PCRE stop code read as a match: `s.match(re"(a\|a)*[bc]")` at `a^30` | sort S10; S8cf | `tests/tsymex_rfc0005_s8cf_limits.nim:71-85`: native `std/re` first, then `status != sxUnsat` for `cf_match_hit`. S8cf merged `d08fe846`. One-sided pin; exactness is PRC-33 item 10. | closed |
| SND-11 | PCRE stop code as a witness: `not s.match(...)` at `a^30` | sort S11; S8cf | same file `:92`, `!= sxSat` for `cf_miss_long`. | closed |
| SND-12 | `let` cursor over a shared global: `gc_shared` | S8cn blocker probe 1 | No test contains `gc_shared`. Nearest pin is the local-seq cursor `sCur`/`cu_shared` (`tests/tsymex_rfc0005_s8cn_seqview_e.nim:124-128`). Probe and both-sha logs at `origin/worker-sls2:worker-reports/s8cn-blocker/`. Mechanism `letCursorDecline`, `dsl_parser.nim:16698-16706`. Port probe 1 (a `let` cursor over a shared global): native HIT + `status != sxUnsat`, expect `sxUnknown`. | |
| SND-13 | S8cu's known limits: macro-built pragmas, a pushing template from another module, an import under a push in a module the scan does not read | PND-11, reclassified round 2 | a missed check-off region is the false `sxRaised` class S8cu fixed: soundness risk, not pending | |
| SND-14 | Int-offset arithmetic without an overflow fork (N24, #166) and the `range[0'u64..>int64.high]` round trip (#169) | decision D-0016-8 | owned by RFC-0014; this RFC carries no work | RFC-0014 |

### §5.2 Precision

**Replay and witnesses.**

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-01 | **First precision item.** Windows re-exec replay: marshal case-object and `ptr`/`ref` witnesses instead of declining. Windows is a consumer's main platform, so a decline there is a decline in daily use Includes INT-01 and INT-14: batch 11 (`7b2ab1e5`) widened the footprint to type symbols, result types and routine signatures, so more SUTs decline on Windows. | S8ct (coordinator ledger, 2026-11-02) | S8ct moved replay to a child process; on Windows a witness of these kinds declines with a named reason, documented in the 0.9.0 migration note and pinned on Linux by the re-exec pin | |
| PRC-02 | Windows re-exec replay: proc-value, `method` and `{.global.}` witnesses decline Includes INT-13: the six hooks `hostRuntimeHook` checks (`replayproc.nim:171-176`); `setControlCHook` stays INT-15. | S8ct | same mechanism as PRC-01; after it | |
| PRC-03 | Replay cannot aim a witness `ptr` at a global: S8cr's three open holes | S8cr; batch 10 integrator | the three open-hole pins give `sxUnknown` (`feGlobalHavoc`, `feReplayRefuted`), not `sxSat`; the false `sxUnsat` is closed, the precision is not | |

**Exact models for RFC-0005's declines.**

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-04 | Inventory every decline RFC-0005 added or widened, and give each an exact model or a recorded reason it stays. Generate the list from the code (decline sites and `SymexErrorKind` members, 6cbfe8f against the tag), not from memory. Known families to seed it: S8cq's by-value allowlist (types where Nim's copy behaviour varies); S8cs's fail-closed global write routes (hooks, opaque routines behind a local alias, `{.emit.}`); S8ct's replay declines (quit, nil deref, unbounded recursion; W1, W2); S8cu's check-option source scan; S8cl's "magic with no body declines"; S8cf's past-safe-length `zsUnknown`; S8ca's `viewFollows` "any other write declines"; S8bk's `feEvalOrderUnmodelled` late address Includes INT-10 (the seven `feGlobalRouteUnproved` pins). The inventory is generated, not written: K2a's census plus K1's `SymexErrorKind` axis (354 decline sites, 91 members, 12 with no producer). | Corey's split, 2026-11-02 | decline-before-verdict was the release fix for most blockers (ledger, 2026-11-02 entries); each decline is sound and costs precision | |
| PRC-05 | S8cn's declines, each to an exact model with native pins: a `lent` loop with a possible write, and a `let` cursor; a by-value actual reached by name, reads included (b9 `sReadOnly` now `feUnsupportedOp`); non-scalar `pairs` and array `items`; a `let` over a formal with any ptr or ref write; a `var`, parameter or computed proc value with a view and a Table (`closureTakesView`); by global name (`sqG`, `gw`); `f(s[i], s[0], s)` and `f(s[0], s[0], s)`; a pointer plus a Table call; a mutated local copy; `t.clear` and `t.pop`; `Table[string, VObj]`; a non-scalar by-value view; `nl2_other_live`, `nl2_same_dead`; two-entry `del` (hash-dependent); the ds, dt, dv forms Includes CRH-05: a pointer plus 11 Table inserts takes past 1400 s; the pin uses one insert. The 'ds, dt, dv forms' are not in `s8cn.md:186-203`: cite their source or drop them. | `worker-reports/s8cn.md` "Declines for RFC-0016" | listed by S8cn as precision; `let c = s` varies across 9 build settings (ledger), so the model must be per build or stay declined | |
| PRC-06 | The `ti_grow` Table `keys` loop that writes the Table, even with no key added: `ti_grow` at `a == 0` is now `sxUnknown`, moved from S8bl's `sxSat` | S8cn | repin accepted at batch 11 intake | |
| PRC-07 | S8cu: exact unchecked semantics — model what a routine compiled with a check off actually does (overflow, bounds, range, field, nil, float checks), instead of the source-position decline Mechanism: K10a/K5a (§9, §8.3). | S8cu | S8cu's fail-closed decline (`feCheckOption`, `feOverflowCheckOption`) closed a false `sxRaised` | |
| PRC-08 | S8cu: a `-d:danger` or `--fieldChecks:off` build declines every routine Mechanism: K10a/K5a (§9, §8.3). | S8cu | follows from the source scan; depends on PRC-07 | |
| PRC-09 | S8cu: `math.nim`'s pushed regions now decline Mechanism: K4c `admitStdlibBody`. | S8cu | every routine in a pushed region of `std/math` declines | |

**Shapes and magics.**

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-10 | `lastIdx`: a query SAT only past the cap declines; lift the cap past 8 | S8cd item 6 (S8k) | `t.len > 10` under a cap of 8 has no model within the cap; a leaf equal to a leaf equal to a literal still takes the cap | |
| PRC-11 | `len` of a nested seq: a `seq[seq[int]]` heap field, or a proc value's result of that type | S8cd remainder | Not re-probed since 136ad60 (S8cd's base); re-probe at head before work. declines on the unsupported nested element representation; last probed at 136ad60 | |
| PRC-12 | `HashSet[string]` behind a pointer or in a heap field Includes AUD-08 (non-int64 `HashSet` elements as a parameter or local, `defaultZero` `runtime.nim:6689-6792`) and the `Table` non-string-key half. | S8cd remainder | Not re-probed since 136ad60 (S8cd's base); re-probe at head before work. declines; last probed at 136ad60 | |
| PRC-13 | `f != nil` on a proc value with no lambda the walker built | S8cd remainder | Not re-probed since 136ad60 (S8cd's base); re-probe at head before work. `ceUnsupportedHof`; last probed at 136ad60 | |
| PRC-14 | `addr o.xs` bound by a `let` | S8cd remainder | Not re-probed since 136ad60 (S8cd's base); re-probe at head before work. `heUnsafeCast`; last probed at 136ad60 | |
| PRC-15 | A case object reaching a heap cell, as a global | S8cd item 3 | no entry-value model; declines (`recvValue` reads it at its type) | |
| PRC-16 | `zeroMem` and `copyMem` on `addr x` (moved to CRH-06) | S8cl remainder | in-band, but a fault rather than a named decline | moved |
| PRC-17 | `alloc0` behind a cast | S8cl remainder | `heUnsafeCast` | |
| PRC-18 | `create` | S8cl item 2; sort S12 | compile stop closed: `tests/tsymex_rfc0005_s8cl_lifetime_b.nim:96-102,193-199` `declines(sutCreate, "cr", "create")` after `nativeHits`; precision only. | |
| PRC-19 | `new(p, finalizer)` | S8cl item 1 | declines | |
| PRC-20 | `GC_ref` (and an object with a `when` member, which `GC_ref` reaches through `RefHeader`) | S8cl item 2; sort S12 | `s8cl_lifetime_b.nim:104-110,200-201` `declines(sutGcRef, "gr", "nnkCast")`, `declines(sutWhenMember, "wn", "WhenMember")`; precision only. | |
| PRC-21 | `procCall` exact model | S8cl item 1; sort S6 | declines since S8cl (empty magic body) | |
| PRC-22 | ~~A `type` section in a SUT or routine body~~ merged into PRC-34 | S8cl remainder; S8cb remainder; S8cp item 7 | declines | merged |
| PRC-23 | A nested `s[gi]` of a seq of seqs | S8cl remainder | declines | |
| PRC-24 | ~~`alt_miss` precision~~ merged into PRC-33 item 10 (the integrator's native pin and larger-budget check are done: `tests/tsymex_rfc0005_b10_integration_b.nim:4-8`) | sort B14; S8co item 10 | `main` correct `sxSat`; S8cf gives `sxUnknown` (`beSolverUndef`) where e497dcf was false (worker-sls2 57899a16). The blocker is closed; the precision against `main` is this item. Batch 10's integrator was to add a native pin and check with a longer budget that it never decides `sxUnsat` | merged |
| PRC-25 | ~~Concolic scratch solves run without limit sites~~ merged into INT-33 | batch 10 integrator | guidance only so far; no verdict observed wrong | merged |
| PRC-26 | `nsc_dead` returns `beSolverUndef` | batch 10 integrator | `nsc_dead` is in no test; re-collect the SUT from the batch-10 integrator notes or drop the row. | |
| PRC-27 | `bt_limit_replace` weakened to sat-or-decline on Z3 4.13.4 | batch 8 integrator | `tests/tsymex_rfc0005_s8bt_limit_langs_b.nim:76-79` `verdict(replaceTarget, "bt_limit_replace")` with default `want = sxSat` (`:59`); closed by S8cn step 1e. The pin runs only under `pcreSearchEngine() == peInterp` (`:70`), so the JIT rows (the Windows legs) assert nothing: a JIT build-row cell, not a reopen. | closed |
| PRC-28 | S8cq item 4: `inc(gs[nextI()])`, `inc(getV())`, `swap(gs[nextI()], x)`; a read-only by-value global through a proc value (`pr`). ~~`addr` of a global in a walked callee (`wp_dead`, `heUnsafeCast`); `unsafeAddr` of a by-value array formal in a walked callee~~ (these two are PRC-30 / S8ch) | S8cq item 4 | the coordinator released it to this RFC if it would delay batch 10; the last two bullets are S8ch's items and are struck here | |
| PRC-36 | Exact model of a `var`-returning actual (`rab(t["a"], t, "a")`) | SND-01; HRV-01 | | |
| PRC-37 | `uncheckedAssign` where the other arm's bytes differ: exact model | SND-07; HRV-02 | | |

**Moved slices (precision).** Each keeps its job file's scope; the rows below
name what moves and what stays.

| ID | Slice | Moves | Source | Owner |
|---|---|---|---|---|
| PRC-29 | S8cg | items 2 (copy a `var openArray` view at the call, so `fill(gArr, bumpA())` decides), 3 (a later argument that only reads a global counts as a read), 4 (`ti_tuple` exact `sxSat` under default budgets), 5 (`bb_rep_sym_empty_hit` exact on both Z3 versions), 7 (an index call through a proc value), 8 (`s8bb_constructs` 40.7 s (under 60); `tsymex_r6_b6_optionregion` is absent from `scripts/ci-suite-seconds.tsv`, so it is in no Windows shard and its time is unmeasured: add it to a shard or record why not). Items 1 and 6 were closed by S8ca and S8by | `jobs/s8cg.md`; batch 7 note | |
| PRC-30 | S8ch | both items: the address of a global in a walked callee halts the path; `unsafeAddr` of a by-value array formal declines | `jobs/s8ch.md`; S8cc remainder | |
| PRC-31 | S8ci | all six items: a term order that earns its cost or none; `r4_strip` within 10% of S8bm; a behavioural pin for the order; ~~`configdefaults_depth` under 60 s without lowering the depth~~ (met by S8cm's split (`tests/tsymex_configdefaults_b.nim:21-23`, 53.6 s), not by lowering the depth); wide factoring decided again; the skip's real saving. Also batch 9's addition: `ti_tuple`'s SAT search 79.8M to 411.8M units on 4.13.4, so `tupleBudget` 300M to 600M | `jobs/s8ci.md`; S8by remainder | |
| PRC-32 | S8cj item 1 | a fresh thread's spend on a query follows what earlier threads ran (72,124 to 5,854,994 units on Z3 5.1); correct the "function of the query alone" claims from S8bm and S8bp. Item 2's trust question is in §5.7 Same in-process phenomenon as CI-03 (and INT-04). | `jobs/s8cj.md`; S8by remainder | |
| PRC-33 | S8co | items 3 (auto-possession with a property or XCLASS), 4 (kept `ignore_skip_arg` under a limit), 5 (`detect_repeat` group repeats on the JIT, 400 calls skipped), 6 (SKIP:NAME past 100, languages past 7), 7 (symbolic `(*ANY)` under the JIT scan, 72+ differences when lifted), 9 (`replace`'s unmarked SKIP:NAME, `first` in UTF, `count` of `set[char]` and overlapping counts), 10 (unbounded no-match refutation past `limitReach`'s safe length, with PRC-24). Items 1, 2 and 8 are in §5.7 Includes PRC-24 (item 10) and PND-02's remainder (a differential-only leg for older PCRE). | `jobs/s8co.md`; S8cf remainder | |
| PRC-34 | S8cp item 7 | declined shapes: whole-tuple `==` (`eqBV`); a local `let b = addr o.y` alias on whole assignment; a type section in a routine body (with PRC-22); a parameter pragma `x {.inject.}: int`, a compile error in `collectStringBackedByteSeqParamsImpl`, to fix first; nested `addr t[1][0]`. `s[1].b = 7` and `s[1][0] = x` only if S8bz left them declined Includes PRC-22; add whole-seq `==` (`runtime.nim:8341`, not re-verified). | `jobs/s8cp.md`; S8cb remainder | |
| PRC-35 | S8cp item 8 | declined magics: `math.toInt`, a holey enum's invalid value, `=dup` of an object or tuple through its hook, `$float`, the remaining `repr` shapes; stop only where the theory cannot express it or the cost is measured out of budget, with the number Add `$bool` (`dsl_parser.nim:11205,11831`, not re-verified). | `jobs/s8cp.md`; S8cb item 5 remainder | |

### §5.3 Crashes, compile stops and hangs

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| CRH-01 | Compile stop on a `sort` callback: `s.sort(proc ...)` | sort S13 | confirmed SAME by S8cu: `docs/rfc/0005-branch-scoped-degrade.md:15478-15480`, `s.sort()` aborts the compile as on `main` (`dsl_typebridge.nim(1261,20)`). Includes INT-09 (`splitLines`) and the generic-param `.len/.add` stop (HRV-44): one `classifyType` row; mechanism K2a/K2c. | |
| CRH-02 | Compile stop on `create` and `GC_ref` | sort S12 | `s8cl_lifetime_b.nim:193-201`; models remain PRC-18/PRC-20. | closed |
| CRH-03 | A ref-local merge runs out of memory and is killed Includes INT-02's figures (8.36 GB under an 8 GB limit, killed at 124-135 s, same on `main`); no `iteDeep` pin in `tests/`; borders RFC-0017 P1 (path merging), which does not cite it. | S8ct | an OOM kill that matches `main`; earlier measured as a 250 s merge, and a silent exit at 300 merges under audit. Bound it to a decline within budget | |
| CRH-04 | A regex literal of 2600 nested groups | S8ct | fixed in 0.9.1 (review R1-22; `c9682ebc`, `9663105d`): `tests/tsymex_rfc0005_r1_pcrelimits.nim` | closed |
| CRH-05 | ~~A pointer plus 11 Table inserts ran past 1400 s~~ merged into PRC-05 | S8cn | liveness; the pin uses one insert | merged |
| CRH-06 | `zeroMem` and `copyMem` on `addr x`: a walker fault (`FieldDefect` reading `ptrPointeeTy` of an `itUninterp`). First make it a named decline, then model it | S8cl remainder; ex-PRC-16 | the only `zeroMem`/`copyMem` pins are the opaque-global form (`tests/tsymex_rfc0005_s8cs_routes2.nim:125,131,363`); the `zeroMem(addr x)` fault has no test. First a named decline, then back to §5.2 as precision. | |
| CRH-07 | **Latent crash:** a `v == f` Int definition in `regexRecDefConds` segfaults at `byteLeafIds` `dec_ref` | sort U4; S8co item 1; S8cf remainder | avoided, not fixed; no SUT at e497dcf reaches it; a wrong refcount can hide a use-after-free | the walker-under-sanitizers job, §11 |
| CRH-08 | The `cmpIgnoreStyle` hang | PND-12; S8cu (resumed 2026-11-02) | no `main` column yet; S8cu is producing the three-way table | |
| CRH-09 | Harvested crash and hang items with no SUT yet: N35 OOM, `cast[int32]` fault, PCRE interpreter SIGSEGV, `$simplify` hang sites, cumulative Z3 MEMOUT, `mkIntLit(0)` placeholder (HRV-06, HRV-43, HRV-45 to HRV-51); bitwise `not` on a Z3 Int (W-25); `<` on `ptr` reaching `cmpBV` (W-28) | research round, `docs/rfc/0016-research/MERGED-worklist.md` W-25, W-28, W-29 | read only: probe each, then a named decline or a fix | |

The two latent crashes that sat in §5.7 are settled: the `byteLeafIds`
segfault (PND-04) moved to CRH-07, and probe p7's rc=139 (PND-05) is closed,
superseded by INT-18.

### §5.4 CI and test time

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| CI-01 | S8cm: corpus files over 60 s of compile plus run on Windows, and shard budgets (no shard's typical time above 30 of 40 minutes). **S8cm is running and may finish before the tag**; if it lands on RFC-0005, it keeps its row there and this item tracks only what it leaves (the files listed after it started: `b10_integration` 107 s, `s8cd_setorder_large` 102 s, `_small` 100 s, `s8cn_views_c` 121 s, `s8bq_remainder` 91.4 s, `s8cr_intro` 60.2 s, `s8cd_globals`) | `jobs/s8cm.md`; ledger entries for batches 9-10, S8cd, S8cn, S8cr | S8cm done (`9ebe2a46`; shard target 23 min, `d7948de5`). `scripts/ci-suite-seconds.tsv` lists 30 suites over 60 s, longest `s8ab_letaudit` 127.4 s. Includes INT-17 and INT-08. | |
| CI-02 | A permanent cpp CI leg. No leg runs cpp today; n42 and n43 broke on cpp for several batches unnoticed (sort B21). Also run Z3 4.13.4 on a schedule: until now batch gates were c on Z3 5.1 only, and full 4.13.4 and cpp sweeps run only at the release gate | S8cl item 5; sort B21; ledger (release gate) | `.github/workflows/` = `fuzzer-mingw`, `fuzzer-msvc`, `symex-mingw`, `tianguis-publish`; no Linux leg, no cpp, no `schedule:`. Z3 4.13.4 already runs on every push on all three Windows legs, so the 'run 4.13.4 on a schedule' half is struck; what remains is CI-A (Linux c, every push) and CI-B (cpp and 4.13.4 on Linux), §11. | |
| CI-03 | `s8by_remainder`'s units check is not deterministic under load | S8ct | At `476976d3` the cpp gate passed (`0005 handoff:580-582`, cause not known); `tests/tsymex_rfc0005_s8by_remainder.nim:189` is still `check r.units == base.units`. Includes INT-04; see PRC-32; owner S8cj. | |

### §5.5 Infrastructure

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| INF-01 | The differential fuzzing harness (§4), slice D1 | coordinator ledger, S8cq blocker (2026-11-02) | every sort blocker was found by hand | |
| INF-02 | Fork (c): a gated clean replay as a safety net, which would catch a false `sxSat` on a clean path. **Decided 2026-11-06: not added** (item `fork-c-clean-replay`, decision D-0016-2); native pins and D1 carry it | RFC-0005 "the open fork (c) below" (line 1667 at 67f0b622; the DoD audit cited it at 1615); DoD audit fork 2 | the fork was never written down in RFC-0005; this is its first record | closed by D-0016-2 (record) |
| INF-03 | The findings ledger and a weekly rate report (§3.2) | this RFC | The ledger exists (handoff F-0001 onward). The weekly rate report is dropped: D-0016-1 closes on the work list, not a rate. | closed |
| INF-04 | S8ck after item 1 (slice S8ck-r): items 2 (`Z3FuncDeclOwn`, `Z3FuncInterpOwn`, `Z3RcfNum` hooks never release `ctx`), 3 (`Z3Ast[S: static]` hooks unused for `Z3Int`/`Z3Bool`), 4's version half (`tffi`, `tversion`, `tmultiversion` assert a 4.x runtime), 5 (`injectShapeFault` comment), 6's first half (ADR-0023's "a lowering-time degrade must never raise", keep or simplify), 7 (`s8s_precision` run wall 13.2 to 19.1 s on Windows), 8 (`examples/properties.nim:30`, examples in nim-z3 CI on c and cpp), 9 (a leak gate that fails on invalid reads, writes and frees, shown RED on a planted bad `dec_ref`), 10 (record and reduce the spacer read; do not file), 11 (generated seq hooks on the raise path release every element), 12 (separate real leaks from live globals, `trcf`'s 26 `Z3ContextOwn` blocks). Item 4's hang half and item 6's second half are in §5.7 | `jobs/s8ck.md`; `worker-reports/s8ck-item1.md` | item 1 closed: cc5ffc9 identical to ae509f0 on invalid accesses and leaks | |
| INF-05 | Audit the older "Different mechanisms, reported and not fixed here" lists against the remainder chain. This document took the lists of slices landed through batch 10 whose remainder has no later slice (S8ca, S8by, S8cc, S8cf, S8cb, S8cd, S8cl, S8cn) item by item. The earlier lists were each carried into a remainder slice whose job said "defer nothing", but no one has checked that every item reached one | RFC-0005, about 80 such lists | **done 2026-11-03** (owner audit of the lists of 72 slices, S8c, S8e/S9 and S8g through S8bt, plus the inline not-fixed notes in S8y, S8ah, S8ao and S8bk): 318 rows fixed, 17 owned by RFC-0005, 9 already owned here. The 13 unowned rows (11 distinct items) are filed in §5.8 as AUD-01 to AUD-11 | closed |

### §5.6 Upstream reports

Outward-facing. Decided 2026-11-06 (item `upstream-reports`, decision
D-0016-3): file UPS-01 and UPS-03, which have reductions; hold UPS-02 until
S8cj reduces it. None is filed yet.

| ID | Report | Source | Evidence | Owner |
|---|---|---|---|---|
| UPS-01 | Nim: a raise-path destroy (a destructor swallowing an in-flight exception on the C backend) | S8ce | reduction at worker `s8ce-work/probe/purenim.nim`, condensed in `worker-reports/s8ce.md` | file; record the issue URL here |
| UPS-02 | Z3 5.1: `Failed to verify: m_cache.mk_unique(p) == p` on wide factoring | S8by remainder; S8cj item 2 | not reproduced at e497dcf (sort N4); S8cj is to reduce it to SMT-LIB | held; includes PND-10 (S8cj item 2) |
| UPS-03 | Z3: invalid read in `spacer::pob_queue::reset()` | S8ck item 1, item 10 | fixedpoint only, unreachable from nelli; S8ck item 10 reduces it | file; record the issue URL here |

### §5.7 Pending classification

These could not be classified as tag blockers or not. The sort's UNVERIFIABLE
rows (U1–U8) are awaiting disposition before the tag and are **not moved**;
they are listed so nothing is lost. Each moves into §5.1–§5.4 once its
disposition shows it is not worse than `main`, or stays with RFC-0005 if it is.

| ID | Item | Source | Why pending | Owner |
|---|---|---|---|---|
| PND-01 | PCRE JIT stack limit `-27` read as a false `sxUnsat` | sort U1; S8cf items 1, 2 | needs a JIT build; the image's 8.45 has none Closed round 2: remainder INT-19. | closed |
| PND-02 | 8.39 JIT's 113 prefix-scan differences; 8.44, 8.39, 8.37 class behaviour; the differential-only leg for older PCRE builds and multi-item POSIX classes on 8.37 | sort U2; S8cf item 12; S8co items 2, 8 | needs those builds or the Windows legs Closed round 2: remainder PRC-33, INT-19. | closed |
| PND-03 | Stack size on macOS and the BSDs (compiled with `--compileOnly` only, never run) | sort U3; S8cp item 6 | no host; the item asks for a 2 MiB fallback where never run One row with S8cp-r item 6; home K5b; a compile-only macOS leg cannot exercise the 2 MiB fallback. | |
| PND-04 | Latent crash `byteLeafIds` segfault (moved to CRH-07) | sort U4; S8co item 1; S8cf remainder | avoided, not fixed; no SUT at e497dcf reaches it; a wrong refcount can hide a use-after-free | moved |
| PND-05 | **Latent crash:** rc=139 of probe p7 (top-level `let ra = symexFind(...)` plus an unused proc with `=sink`, `=dup` and `quit`) | sort N3; S8cp item 4; S8cb note | 200 of 200 runs rc 0 per sha on c, no valgrind or ASan; the cause is unknown and it is not fixed Closed round 2: superseded by INT-18; rc=139 absent in 450 runs per tree. | closed |
| PND-06 | ~~The October notes' false `sxUnsat`~~ merged into INT-20 | sort U5; S8cl item 1 | the SUT does not exist to run | merged |
| PND-07 | `z3ApiErrorCount` over-count changing a verdict | sort U6; S8ck item 6 | read, not observed; looks like a decline Closed round 2: U6 and U7 are verified. | closed |
| PND-08 | `tregex_index` hang on Z3 5.1, and whether the walker can reach it | sort U7; S8ck item 4 | the nim-z3 suite's shape was not ported to a probe Closed round 2: U6 and U7 are verified. | closed |
| PND-09 | Every row of the sort on Z3 4.13.4 | sort U8 | covered by the release gate's full 4.13.4 sweep Closed round 2: c + Z3 4.13.4 969/969 identical to 5.1, `0005 handoff:274-276`. | closed |
| PND-10 | ~~Whether a verdict reached after Z3's `mk_unique` check can be trusted~~ merged into UPS-02 | S8cj item 2 | not reproduced at e497dcf (sort N4); S8ci's report gives different figures | merged |
| PND-11 | S8cu's known limits (moved to SND-13) | S8cu | if the scan misses a check-off region, the walker assumes checks are on, which is the false `sxRaised` S8cu fixed; `main` faulted on these routines, so a miss may be worse than `main` | moved |
| PND-12 | S8cu's resumed rows: ~~`push assertions:off`, a global initialiser under a push, a nil deref with SIGSEGV against a caught `NilAccessDefect`, the cross-module rows~~ dropped round 2; the `cmpIgnoreStyle` hang moved to CRH-08 | S8cu (resumed 2026-11-02) | S8cu is producing the three-way table | moved |
| PND-13 | Z3's own internal recursion depth, not audited when S8ct bounded the walker's term walks | S8ct (B19 disposition) | to be checked at disposition | |

After round 2, §5.7 holds PND-03 and PND-13 only.

### §5.8 Intake at RFC-0005's close (2026-11-03)

The findings batch 11 and the 0.9.0 release left, with the unowned rows of
the INF-05 owner audit. RFC-0005 closed at `8177eb27` (walker 264). None of
these is worse than `main` 6cbfe8f as recorded at intake; a row whose class
says "unclear" carries the reason. Where a row restates an item already listed
above, it names that item and adds what intake learned, and the item above
stays the one to work. Classes: **precision**, **crash** (a crash or compile
stop, with its standing against `main`), **performance**, **test-harness**,
and, for audit rows only, the audit's own class.

**From batch 11 and the release.**

| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-01 | ~~Windows re-exec replay marshalling~~ merged into PRC-01 | S8ct, "For RFC-0016" 1 | precision | merged |
| INT-02 | ~~The ref-merge walk peaks at 8.36 GB~~ merged into CRH-03 | S8ct, "For RFC-0016" 2 | crash, same as `main` | merged |
| INT-03 | ~~A regex literal of about 2600 groups~~ merged into CRH-04 (closed) | S8ct, "For RFC-0016" 3 | crash | merged |
| INT-04 | ~~`s8by` units check not deterministic under load~~ merged into CI-03 | S8ct, "For RFC-0016" 4 | test-harness | merged |
| INT-05 | An object field of a two-alias type stops the compile (`expected 'O = Alias'`), at `main` and on the channel; pinned "declines as main does" in `tsymex_rfc0005_s8ct_deepterm` Evidence: builds and declines as `main` does (`feUnsupportedParamType`), `tests/tsymex_rfc0005_s8ct_deepterm.nim:105-111`; not a compile stop. | S8ct, "For RFC-0016" 5 | precision | |
| INT-06 | The array-width decline (`termWalkMaxDepth`) catches an `int` index the path confines (`a[n and 7]`): the count reads the index's type, not the path | S8ct, "For RFC-0016" 6 | precision | |
| INT-07 | On Z3 4.13.4, a nim-z3 context made after one holding 80,000 `or` terms was destroyed builds terms about 800 times slower (20,000 `or`s: 0.14 s, then 119 s); a `symexFind` in between restores it. Not chased | S8ct, "For RFC-0016" 8 | performance | |
| INT-08 | `tsymex_rfc0005_s8ct_deepterm`'s teardown takes 78 s on Windows Evidence: S8cm split; `s8ct_deepterm` 43.6 s, `_b` 50.4 s | S8ct (coordinator, release intake) | test-harness | closed |
| INT-09 | ~~`splitLines` compile stop~~ merged into CRH-01 | S8ct, "For RFC-0016" 7 | crash (compile stop), same as `main` | merged |
| INT-10 | ~~Seven pins moved to `feGlobalRouteUnproved`~~ merged into PRC-04 | S8cs, "Precision cost" and "For RFC-0016" | precision | merged |
| INT-11 | The `trace1` row of `tsymex_rfc0005_s8cs_routes` (a `=trace` hook only the cycle collector runs) is a walker fault, `coerceIntLit` on an `svPtr`; `main` stops the compile on it Add a walker pin expecting a named decline on `trace1` (today Nim-only, `s8cs_routes.nim:195-199`), then fix `coerceIntLit`. | S8cs (coordinator, release intake) | crash (walker fault) | |
| INT-12 | Under `--exceptions:setjmp` on Windows, the walker crashes entering its 16 MB fiber (SIGSEGV in `runSymexCaught`, before any walk). The same fiber and the same crash as `main`; the setjmp suite pins the default crash on Windows and cpp | S8cu, "Windows" | crash, same as `main` | |
| INT-13 | ~~Re-executed replay declines on a host runtime hook~~ merged into PRC-02 | batch 11 (`7b2ab1e5`, `tsymex_rfc0005_b11_hoststate`) | precision | merged |
| INT-14 | ~~Re-exec footprint reads type symbols~~ merged into PRC-01 | batch 11 (`7b2ab1e5`) | precision | merged |
| INT-15 | `setControlCHook` is not among the runtime hooks `hostRuntimeHook` checks, so a re-executed replay does not decline when the host set one, and the child runs without it. Not classified: needs a three-way row | batch 11 (`replayproc.nim`) | unclassified (§5.7 rule) | |
| INT-16 | The 0.9.0 migration note's counts recounted against v0.8.0 (37 new `SymexErrorKind` members, the ordinal table). **Done** in batch 11 (`8f00b736`); recorded so the item is not reopened Closed (`8f00b736`). | batch 11 | test-harness (docs) | closed |
| INT-17 | ~~30 corpus suites over 60 s~~ merged into CI-01 | S8cm (done; `9ebe2a46`) | test-harness | merged |
| INT-18 | Probe p7 (sort N3) now declines (sxUnknown) where `main` decides correctly (sxSat; native hits at k=3). A precision loss on this SUT, not a soundness one. Its old rc=139 did not recur in 450 runs per tree (c, cpp, ASan) | pre-tag probes on `8177eb27` | precision | |
| INT-19 | PCRE 8.37 built without JIT, which is on the verified-library list, was not run. U1 and U2 were verified on 8.37 JIT, 8.39 JIT and 8.44 JIT: the candidate declines where `main` gives a false pair | pre-tag probes (U2) | test-harness | |
| INT-20 | U5's original SUT (October false sxUnsat) lives only on the offline worker. S8cl's reconstruction (`unsafeNew(p, 8); if p != nil`) is correct on the candidate. Recover the original, and pin it, when the worker returns Evidence: `origin/worker-sls2` is fetched (88 report files) but the U5 SUT is not among them; S8cl's reconstruction is pinned at `s8cl_magics.nim:61-72`. Recover from the host or declare the reconstruction the pin and close. | pre-tag probes (U5) | test-harness | |
| INT-21 | The check-off probe's `ai_caught` (`mitems` over `int16`, `assertions: off`) decides sxRaised. The raise looks real (int16 overflow at 32767 with overflow checks on), but no native run tried that input. Pin it natively | pre-tag probes (S8cp item) | test-harness | |

**From the 0.9.1 wiring audit (2026-11-03).** What RFC-0005's post-tag
wiring audit (WA-1 to WA-13) and its fix slices W1 to W3 left open. Measured
against 0.8.0, as the audit was; none is worse than it.

| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-22 | A clean, faithful winner is never replayed, so nothing learns that its witness ends the process after the target. `assertCoveredBy` still splats it and `symexForAll` still seeds it, in the host (`symex.nim:4057-4061`, `:982`). Unchanged from 0.8.0; WA-2 closed only the replayed case (`witnessUnsafe`) | 0.9.1 wiring audit | crash, same as 0.8.0 | |
| INT-23 | A replay that ends at a memory limit is run-dependent only when the child's `outOfMemHook` reports it (`replayproc.nim:145`, `:328`). Under `-d:useMalloc` the hook is not reached, and a kernel OOM kill is a `reSignalled` SIGKILL, so either is cached as a permanent `:unk` | 0.9.1 wiring audit | precision | |
| INT-24 | The run-dependence flag is a threadvar reset by each entry macro's settle (`replayproc.nim:90`; read at `symex.nim:646`). A user-level `saveSymexVerdict` of an `sfUnknown` right after a settle that set it skips its save too Evidence: `d8969822`; no `threadvar` in `replayproc.nim`/`replayresult.nim` | 0.9.1 wiring audit | performance | closed |
| INT-25 | Hypothesis: on macOS a kill at `replayTimeoutMs` does not reach the SUT's own child processes, and the child does not die with the host. `setpgid` and `PR_SET_PDEATHSIG` are Linux-only (`replayproc.nim:296-298`, `:374-376`). There is no macOS CI to probe it Includes HRV-03: on macOS/musl `quit(n)` is reported as exit 0 in the hint (`replayproc.nim:100-108`). | 0.9.1 wiring audit | unclear (hypothesis; no macOS host) | |
| INT-26 | `RegexError` reaching `symexFindAllWitnesses` through the user exception hierarchy (WA-1, `symex.nim:4523`) is unpinned: W1 pinned a user exception type only. It needs a PCRE SUT | 0.9.1 wiring audit | test-harness | |
| INT-27 | Under `--panics:on` `replayInScope` declines every target (`symex.nim:2264`), so every lossy clean winner is `rsUnconfirmed` (`settleWinner`, `:3417`) and none is `trusted()` In W1-c's scope (the panics profile, §11). | 0.9.1 wiring audit | precision | |

**From the RFC-0005 code review (2026-11-04).** The Lows the review's ten
rounds reported and did not fix under the through-Medium mandate
(`docs/rfc/0005-review.md`; floor reached at round 10, `2e7a0bb6`). Each row
groups related Lows and names the ledger rows it carries. None is a
Critical/High/Medium finding. Standing against `main` was not measured at
intake, so each row still needs its three-way row (§5.7 rule) before work.

| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-28 | Replay child lifecycle and limits: SUT-started grandchildren survive when the child ends by itself; no memory cap on macOS/BSD and no CPU/FSIZE/NPROC limits or Windows `ActiveProcessLimit`; `pipe2`, the `PDEATHSIG` thread, `WaitForSingleObject` wrap, `resumeThread`, wire length overflow, "(deleted)" exe, non-atomic counter; ~~`waitpid(-1)` elsewhere~~ (only `waitpid(pid, …)` at `:480,1115,1140`) and no `setpgid` off Linux | 0005 review R1-24, R1-31, R1-32, R2-25, R2-27 | crash (hardening); not compared against `main` | slice `rv0005-lows` |
| INT-29 | Replay child start-up robustness: a POSIX re-exec `execve` failure does `_exit(127)` and reads as a SUT crash; a child that cannot open its out file writes to nil and segfaults; the Windows private dir inherits the parent's ACL; the re-exec child inherits non-CLOEXEC fds; with fd 0-2 closed in the host the report fd is clobbered | 0005 review R2-21 to R2-24, R2-26 | crash (hardening); not compared against `main` | slice `rv0005-lows` |
| INT-30 | The wire reader accepts a zero-size seq, amplifies allocation and does not bound recursion depth; unverified: the Windows fiber stack under refc | 0005 review R2-28, R2-29 | crash (hardening); the fiber half is unverified | slice `rv0005-lows` |
| INT-31 | Cache-key coverage: `--opt`, `--cc`, `--cpu` and `--os` are not in the `\|bf=` segment; a `{.push.}` inside `fn` itself is invisible to it (covered by the `feCheckOption` decline, worth a test) Includes W-18: the `;impl=` digest holes (importc/dynlib bodies, override callees, proc-value targets, `lib/`; `docs/migration/0.9.1.md:264-273`). The `\|bf=` half is closed by K5a. | 0005 review R2-16, R2-20, R3-16 | soundness (key coverage); not compared against `main` | slice `rv0005-lows` |
| INT-32 | Replay and settle policy: ~~stale "trusted by construction" comment, unenforced one-digit codec~~ (fixed: `3476f039`), `storedGaps` prefix, `reSignalled` not run-dependent, first-soundness-per-type, lossy sibling precision; `witnessUnsafe` not rendered, `spinJitter` costing up to about 100 syscalls per op, ~~the `ReplayOutcome` doc saying "three-valued"~~ (fixed: `3476f039`); an always-hanging witness is cacheable and pays `replayTimeoutMs` every run, and a loser's timeout blocks the winner; a statically refused replay stored `rsUnconfirmed` and runnable on a hit (documented policy, to be revisited) | 0005 review R1-33, R1-34, R4-07, R4-10 | performance and precision; no wrong verdict described | slice `rv0005-lows` |
| INT-33 | Liveness on the fuzzer path: `ConcolicCollectResult.annotationViolations` has no reader; `saveSecondary` is unguarded, so the new `DbError` escapes `forAll`; the concolic flip solve lacks `maxSeqLen`/`seqQueryRLimit` and the theory facts `trySolve` adds Includes PRC-25. | 0005 review R1-25, R1-26, R1-27 | crash (R1-26) and precision (R1-27); not compared against `main` | slice `rv0005-lows` |
| INT-34 | Design cleanups: `FindingHint`/`FindingGap` kinds are strings; include-split `runtime_*` modules and a `symex.nim` that mixes codegen, cache codecs and settle; the `engineSymexDbErrors` threadvar sink; `loweringPendingTaint` still a threadvar with `walk`/`walkCapSynced` as two shallow layers; the `sx2:` prefix is redundant with the walker version | 0005 review R1-28, R1-29, R2-10, R2-14, R4-08 | design debt; no wrong verdict described | slice `rv0005-lows` |
| INT-35 | Exit-group guards: a compile-time `fields()` check that every group-typed field of `WalkCtx`/`LoopFrame`/`CallFrame`/`CallFrameCtx` is visited by `forEachExitGroup`; per-frame constructors so a group cannot be default-constructed unbound; `mitemsSince` yields `var T` so an entry's depth is mutable; `replayNotRun`'s hint check | 0005 review R5-08, R6-03, R6-04 | design debt; guards against a future soundness slip | slice `rv0005-lows` |
| INT-36 | The finding collector's edges: `droppedSymexFindings` has no production consumer and is per-thread, so a worker thread's drops are invisible; `popEngineFrame` merges speculative nested runs and double-reports; a finding filed mid-statement is not stamped with later stray taint (pre-existing) | 0005 review R5-07, R6-08, R4-09, R3-17 | precision (R4-09, R5-07) and soundness (R3-17, not compared against `main`) | slice `rv0005-lows` |
| INT-37 | Precision and unverified probes: `claimStrayPendingTaint` over-taints coalesced pending taint; a possessive quantifier on a non-group item may add 0 to the PCRE size bound (probe near 65536); `symBodyHash` on a bodiless routine (importc or forward declaration) may fail at compile time | 0005 review R2-08, R2-09, R6-09 | precision; two items unverified | slice `rv0005-lows` |
| INT-38 | Cache hygiene: the notes record can be torn mid-save; old `:raised` indexes (before `:raised2`) are never cleaned up | 0005 review R6-07, R8-04 | performance; no wrong verdict | slice `rv0005-lows` |
| INT-39 | Remove `SymexResult.fromCache`, which no code path sets (WA-11), in 0.10.0 with a migration note | item `fromcache-field`, decision D-0016-4 | `src/nelli/smt/types.nim`; the readable cache-hit flag is `SymexFinding.fromCache` | |

**From the INF-05 owner audit (rows marked UNOWNED).** The rows the audit
marked OWNED-0016 were already in this document (PRC-31, PRC-32, INF-04,
PND-07, PND-08, UPS-01) and are not repeated.

| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| AUD-01 | `isLoose` leaves an `isIntOffset` parameter unstamped. By design (ADR-0001: `isLoose` is opt-in unsound and carries its banner on `main`); needs a "stays by design" record, not a slice | S8w | soundness, opt-in and documented; not worse than `main` | stays by design: `out-of-scope(reason)` cell, written by K1a |
| AUD-02 | `acDivByZero` off with `acOverflow` on leaves the continuation unconstrained at a zero divisor. A nelli setting with no Nim counterpart (Nim's zero check rides on `overflowChecks`); a witness relying on it would trap on replay, which S8ct's child contains | S8aa | unclear (policy); not worse than `main` | |
| AUD-03 | No clean no-zero type remains for the free-`retSym` guard pins; they are now `sxUnknown` on a `HashSet[string]` arm field, so the guard's coverage is weaker. No verdict defect | S8z | test-harness | |
| AUD-04 | Macro-VM closure capture: a nested proc capturing a loop `var` kept one closure environment across iterations (seen as a duplicate case label). **Probed, no instance** at `main` 6cbfe8f and the channel at 67f0b622; the one known instance was fixed in S8z (`tagOrdOf` top-level). No other RFC-0016 item audits this class (AUD-06 and AUD-07 are the `let`/parameter alias guard's coverage) | S8z; coordinator probe, 2026-11-03 | unclear at audit; probed, no instance | closed |
| AUD-05 | Step 1c's equality classes are syntactic over the roots: an equality the query implies without stating it is not seen. Shown, not closed (`tsymex_rfc0005_s8aq_remainder` (4)); the uncapped steps still decide these queries | S8ai; S8aq item 4 | precision | |
| AUD-06 | The build-time VM-alias gate runs on one suite per CI leg, not the whole corpus (deliberate: about 15–18 s per compile). Carried unchanged through S8ak and S8al | S8ah, S8ak, S8al | test-harness | |
| AUD-07 | A generic never instantiated in the scope's compilation unit gives the VM-alias guard an un-instantiated `getImpl()` tree | S8al | test-harness | |
| AUD-08 | ~~Non-integer `HashSet` elements decline~~ merged into PRC-12 | S8am | precision | merged |
| AUD-09 | A `var` global initialised by a literal is not read at its initialiser: its entry value is fresh. A deliberate sound choice (S8as item 3) | S8as | precision | stays by design: `out-of-scope(reason)` cell, written by K1a |
| AUD-10 | The nil-dereference check of a lazily read operand happened where the read moved (S8ax's `orderOperands`), not where Nim checks it. The S8ax probe turned this into two blockers, both fixed: S8cq makes argument reads follow the C backend's temporaries (`nimArgTemps`; `tests/tsymex_rfc0005_s8cq_argorder.nim`), and S8cu makes a nil dereference an uncatchable crash routed through frame exits (`tests/tsymex_rfc0005_s8cu_nil.nim`, `_nil_native`, `_nil_setjmp`) | S8ax; S8be item 7; S8cq; S8cu | soundness at audit; fixed | closed by S8cq and S8cu |
| AUD-11 | S8aw's `L`-against-`indexof` link now covers native terms only; the walker no longer emits `seq.last_indexof` or `str.indexof` for `rfind`/`find`. A coverage note, no wrong verdict or decline described | S8au | precision | stays by design: `out-of-scope(reason)` cell, written by K1a |

AUD-04 and AUD-10 were the two rows whose standing against `main` the audit
could not settle. Both are closed: AUD-04 by a probe at both shas that found
no instance, AUD-10 by S8cq and S8cu.

### §5.9 From the research round (2026-11-06)

The research list's rows that §5.0-§5.8 and §8's mechanisms do not already
carry. Ids are the research list's (`docs/rfc/0016-research/MERGED-worklist.md`,
which has the evidence); each needs its three-way row before work.

| ID | Item | Home | Owner |
|---|---|---|---|
| W-15 | `isThreadvarSym`/`isImportedVar` read a `getImpl` failure as "no": fail closed | K2a | |
| W-19b | S8cs "not covered" store routes (threads, signals, dynamic-subtype hooks, ORC cycle collector); Windows re-exec unseen macro hooks; S8cu scan misses (`mitems` instantiated under a push elsewhere, never-popped push, importer outside the graph, nelli under a user push); opaque proc with `var T` params leaves the environment unmutated | probe each, then fix or an `out-of-scope` record; Wave 4 | |
| W-19c | closure unverified: S1b block/break binding, S7 `lowerInExpr` drains | probe; Wave 4 | |
| W-34..W-42, W-44..W-49 | the precision list ranked by frequency, and the harvested precision items | Wave 4, in the research list's order | |
| W-62 | CI odds: mingw B5-4, the `fuzzer-msvc` pull-request trigger, R1-12/13 unpinned, `dt-bounded` orphans, witness folding across nim-z3; refc never tested closes as `out-of-scope` under D-0016-7 | CI-B and Wave 4 | |
| W-63 | JIT PCRE suites `skip()` on every build in use: a JIT build row | CI-B | |
| W-65..W-68 | hygiene: stale comments, the `caseNarrow` duplicate, `dOpaque` stubs, six GitHub issues, RFC-0002 commit-or-drop, stale SYMEX_PLAN, ADR and migration text | Wave 4 | |
| MOVE-0017 | the moves to RFC-0017 (N20, OQ1, CRH-03's OOM, `maxLoopUnwind`, #138, caps): record each in RFC-0017 with its id, then close here | coordinator, before W1-z | |
| STAYS | the "declined, and it stays" records (A-10, C-13, C-10, HRV-18, HRV-27, HRV-63, HRV-105, B §1.2, AUD-01, AUD-09, AUD-11) | `out-of-scope` rows, written by the slice that introduces each axis | |

## §6 — Slice procedure

Unchanged from RFC-0005's worker brief, with two additions from its lessons:

- **RED first, natively.** Every item is pinned RED against a native run on
  the same build before the fix, per §2.2.
- **A slice that lifts a decline runs its neighbours.** It pins the shape it
  lifts, and also the same shape with the value shared rather than copied, and
  with the evaluation order reversed, before it claims a verdict. Until §4's
  harness exists, this is the hand-run version of it.
- Report anything found and not fixed as a finding (§3.2), with its class and
  its three-way table, not as prose at the end of a slice note.
- **Fuzzer and consumer intake.** Each issue the nightly fuzzer job opens
  (§10), and each consumer report, becomes an `F-NNNN` row with its
  three-way probe within the week, and is named by a cell (§8.2).

## §7 — Open forks

None open. `/architect` round 1 (2026-11-06) resolved every point its five
lenses raised by recommendation (§8-§13; the handoff's round-1 ledger lists
each). Corey's decisions on the research round are D-0016-5 to D-0016-9:
Wave 1 as 0.9.2 after the design rounds; about twenty tracker rows plus the
generated ledger; refc refused by name; int-offset soundness owned by
RFC-0014; undefined behaviour as an outcome instead of a wrap setting.
Earlier: Decided by Corey on 2026-11-06:

- **`exit-criterion`:** the work list alone (B, D-0016-1).
- **`upstream-reports`:** file UPS-01 and UPS-03, hold UPS-02 (B, D-0016-3).
- **`fork-c-clean-replay`:** not added (B, D-0016-2).
- **`fromcache-field`:** remove the field in 0.10.0 (B, D-0016-4; INT-39).

## §8 — Closure design (`/architect` rounds 1 and 2, 2026-11-06)

**Why a design section was needed.** A read-and-probe of the whole walker
surface at `83c1d304` (six lenses: constructs, types × memory, magics and
stdlib, the soundness machinery and builds, reconciliation of this list, and
the test surface; reports in `docs/rfc/0016-research/`) found seven clean
false verdicts that no row here named (§5.0). They share one shape: **a clean
model at a place that is not a table.** A transparent `else:
parseExpr(operand)` (`dsl_parser.nim:10658`, `:10845`), a type id built from a
node's `repr` (`:20461`), a local pragma dropped by a loop that keeps only
`noinit` (`:19771-19792`), a build flag read only by replay and never by the
walker (`defined(nimPanics)` at `symex.nim:2343` and
`canonicalize.nim:6537`), a C-compiler fact modelled as a Nim fact
(`runtime.nim:8862-8870`, `:24500-24502`). The carrier is not the problem: the
same audit traced 23 taint mechanisms (fork, merge, call cache, unroll, prune,
halt, replay settle, cache load) and none loses taint. What is missing is
admission: §2.1 says a model is admitted by an allowlist, and in these places
nothing admitted it.

Fixing the seven one at a time is the whack-a-mole RFC-0005 played. This
section replaces it with one mechanism that makes an unadmitted model
impossible to write silently, and a finish line (§12) that is a property of
that mechanism's output, not a count of rows.

### §8.1 Admission: per-axis verbs over private rows, default decline

`smt/admission.nim`, a Z3-free leaf beside `soundness.nim`. Callers never see
a row; each axis exports a decision verb that returns the answer, and an
enumerator that K1 reads:

```nim
type
  AdmissionModel* = enum amExact, amDeclined, amOutOfScope
  Admit* = object                         ## the answer a consumer branches on
    case model*: AdmissionModel
    of amExact:      discard
    of amDeclined:   kind*: SymexErrorKind; reason*: string
    of amOutOfScope: why*: string
  Axis* = enum axConstruct, axTypeOp, axLocalPragma, axMagic, axStdlibBody,
               axBuild, axReadOnly, axDefinedness, axCallShape, axExnMemory,
               axErrorKind
  Cell* = object                          ## what K1 enumerates
    axis*: Axis; key*: string; site*: string
    model*: AdmissionModel; pin*: string; rows*: set[BuildRow]; items*: seq[string]

func admitMagic*(name: string; shape: MagicShape): Admit
func admitTypeOp*(k: IRTypeKind; op: MemOp): Admit
func admitDefinedness*(op: ArithOp; cls: OperandClass; p: BuildProfile): Admit
# ... one verb per axis ...
iterator cells*(axis: Axis): Cell
```

Rules the type carries, not the reviewer:

- **Absent is a decline.** A string-keyed axis (magics, pragmas, stdlib
  bodies) answers `amDeclined(feUnadmitted)` for a key it has no row for. An
  enum-keyed axis (`IRTypeKind × MemOp`, `ArithOp × OperandClass`) is an
  `array[K, …]`, so a missing key is a compile error and the lookup is O(1)
  on the walk's hot path; the macro-time string axes stay linear lookups
  behind a lib-scanning guard.
- **An exact row needs its evidence.** Rows are built with
  `exact(key, pin, rows)`, `declined(key, kind, reason)`,
  `outOfScope(key, why)`; `exact` with an empty `rows` set does not compile.
- **The consumer cannot bypass the table.** The seven findings were sites
  that never looked anything up, and a table only proves its own
  completeness. So parser dispatch over a keyed axis is generated:
  `dispatchMagic` (and its siblings) expands to the `case` whose `else` is a
  decline, and `error()`s at compile time on an arm with no row or a row with
  no arm. The per-name switch at `dsl_parser.nim:11868-11892`, whose
  `else: discard` falls through to generic call handling today, is the first
  one converted. `admitTypeOp` is attached to the IR at parse time
  (`IRParam.copyModel`), so a walker consumer cannot read a type without its
  verdict.
- **`feUnadmitted` is `dcNoAnswer` until K7 lands.** The walker's
  `isUnsupported` arm continues every live path with `forkPathTainted`
  (`runtime.nim:24508-24512`) and `pathTaint(dcOmitted)` is empty
  (`types.nim:3650-3652`), so a `dcOmitted` decline there would let an
  `sxSat` through clean. `feUnadmitted` moves to `dcOmitted` only once K7's
  `halt` drops the path.

The axes and what they absorb:

| axis | key | consumers | absorbs |
|---|---|---|---|
| magic | name × `MagicShape` (literal / const / variable, width, signedness) | `dispatchMagic` at `dsl_parser.nim:11868`, `ensureProcRegistered`, the opaque-call defect scan (`:4152`) | `varParamMagics` (`:4254`), the four string arrays (`:4018-4030`) |
| type × memory op | `array[IRTypeKind, set[MemOp]]` | `typeCopiedByValue` (`:7835`, on `NimNode`) and `holdsSharedMemory` (`:16561`, on `IRType`) through one `classifyType` normalisation, itself a row of the construct census | the S8cq by-value allowlist |
| local pragma | pragma name on a `var`/`let` | `localDeclGate` | the `noinit`/`global` special cases at `:19771-19792` |
| build | `BuildProfile` semantic fields (§8.3) | `symexFind` at macro time | `verifiedLibs`' role for Z3, Nim and PCRE |
| read-only | node kind and call shape proved not to write | one `mayWrite(n)` | the four parser predicates `nodeWritesHeap` (`:16574`), `routeStoresThroughDeref` (`:22429`), `ptrUsesStayLocal` (`:6546`), the hook copy-proof (`:22505`) |
| definedness | `array[ArithOp, array[OperandClass, …]]` read with the profile (§9) | the arithmetic lowering | `arithTrapConds`, `currentArithWraps` (`runtime.nim:1976`) |
| stdlib body | `(module, routine)` walked by body, with its check-option delta | the inliner | the implicit "walk any `lib/` body" |

`bindsViewWhole` (`runtime.nim:21011`) works on `IRStmt`, not `NimNode`, and
stays a separate IR-level predicate with its own fail-closed rewrite.

**Constructs are the axis that is not a `const` table.** Dispatch there is
`case n.kind` plus positional child reads. Admission is the `classOf` shape
(`types.nim:3228`, an exhaustive `case` with no `else`): every `case` over a
`NimNode` kind in `src/nelli` (the parser, and also `concolic.nim:165-200`,
`replaywire.nim:140-175`, the `symex.nim` footprint scanners,
`check_options.nim`, `vm_alias_guard.nim`) either has no `else`, or its
`else` body is a decline call. K2's census enforces it by parsing each source
file's AST at compile time; a child-shape corpus (a `getImpl` snippet per
construct row, asserting an IR with no unsupported node or a named decline)
covers the positional reads.

**Proof spike.** ADM-1 moves two existing tables onto the module with no
verdict change: `varParamMagics` (19 string-keyed entries, 16 modelled; each
needs its pin file named, which exists across the S8bl and #145 suites) and
`verifiedLibs` (`pcre_engine.nim:143`, record-keyed, whose consumer
`pcreSearchEngine` returns a payload, the engine model, and whose absent-key
kind is `psUnverifiedLib`). The second is the test of the interface: it needs
either a payload on `Admit` or an absent-kind parameter, and the spike decides
which before any new table is written. The interface above is expected to
change there.

### §8.2 The universe ledger is an output

`tests/tsymex_0016_universe.nim` (registered in `nelli.nimble`) iterates
`cells(axis)` for every axis and **emits** `docs/rfc/0016-universe.tsv` the
way `sweep.sh` emits `.drift`. It is not a hand-annotated input: the reason a
cell stays declined lives in its row, where review sees it.

- **A cell is `(axis, arm key)`**, the discriminant the code actually reads:
  an operator name, a conversion pair, a magic × shape, a type × memory
  operation. Identity does not include a file or line, so a refactor does not
  churn it. A dispatch site registers under a reviewed `site` string passed
  to the generated dispatch; the K2 census asserts each site string occurs
  once.
- **Axes:** those of §8.1, plus `SymexErrorKind` members (each named by a
  cell, or deleted), **call-site shape × callee shape** (converter, template
  with a side-effecting argument, default-valued formals, named and varargs
  arguments, two instantiations of one generic, two closures sharing an
  environment, inline vs closure iterator, `method` dispatch, hooks, `defer`,
  `{.borrow.}`) and **exceptions × memory** (a raise inside `=destroy`,
  `finally`, `defer` or an inlined iterator; `getCurrentException` across
  nested handlers; UPS-01 is this class). Magic names are scanned from all of
  `lib/` with multi-line declarations; `TMagic` is not importable, so its
  count is a dev-image script output, not an assertion.
- **States:** `exact(pin, rows)`, `declined(kind, reason)`,
  `out-of-scope(reason)`, and for unsat cells **exhaustive** vs **sampled**
  native evidence, printed separately. `unclassified` is the only state the
  test rejects.
- **Pins report themselves.** The K9 helpers write a pin record at run time:
  test file, entry point, cell, target, domain, `exhaustive`, verdict, native
  result, and the `BuildProfile` segment. K1 joins cells to records; it does
  not scan test text. Because CI runs the corpus in shards, K1 is a job after
  the shards in each leg, consuming the records as artifacts. A leg checks
  only the cells that claim its own build row; a cell claiming a row that no
  leg runs is `unclassified`.
- **The work list is joined too.** `Cell.items` names §5 row ids and
  `F-NNNN` ids. K1 reads this RFC and its handoff at run time for row ids
  (`^\| (SND|PRC|CRH|CI|INF|UPS|PND|INT|AUD|W|F)-\d+ \|`) and fails on an
  open id that no cell names. The work list is the hand list; reading it is
  the point.
- **What it certifies.** Single-site exactness. Combinations (a construct
  nested in another, a memory route through a call) are the fuzzer's,
  measured by the pairwise figure (§12 item 4).
- **Ratchet, per axis.** The test fails on any new unclassified cell against
  a committed allowlist file. The commit that introduces an axis may add
  exactly that axis's cells (the delta must equal the new axis's cell set,
  nothing from another axis); after that, the axis's allowlist may only
  shrink. K1a's first axes are the error kinds (about 90 cells, nearly all
  unclassified on day one), the two ADM-1 tables and the build rows, so the
  ratchet has content from its first commit.
- **First commit proves it runs.** The slice that lands it shows it RED on
  each CI leg with a planted unclassified cell, as `symex-mingw.yaml:217-230`
  pins the z3-optional seam.
- **Skips name a cell.** A platform arm or `skip()` in a test takes
  `skip("cell:<axis>/<key>")`, so §12 item 3 is checkable.

### §8.3 BuildProfile: one constant, read and keyed

The SUT and nelli are one binary, so the build is a compile-time fact:
`const buildProfile*: BuildProfile` in a leaf `smt/buildprofile.nim`. Its
fields split by what reads them:

- **Semantic** (read by walker arms, keyed): check options, panics, memory
  manager, exceptions mode, backend, `--opt`, the declared signed-wrap mode,
  pointer width, CPU, OS, `nimOldCaseObjects`/`strictCaseObjects`, PCRE
  engine. Each comes from `compileOption`, `defined` or `sizeof(int)`.
- **Provenance** (rendered on a finding and recorded on a pin, not keyed):
  C compiler family (`defined(gcc|clang|vcc)`), Nim version and patchset,
  Z3 version (already its own `symexCacheKey` parameter). The C compiler
  version is a run-time fact of the pin record; nothing at macro time reads
  it.

**What `querySetting` cannot read is refused or declared, not guessed.**
`querySetting(compileOptions)` does not see `--passC` from the command line,
`nim.cfg` or `config.nims` (Nim routes those to `compileOptionsCmd`,
`commands.nim:862-864`; `vmops.nim:169` returns only `compileOptions`), nor
`{.localPassC.}`, nor the `-O` level. So `-fwrapv` cannot be read: signed
wrap is undefined unless the consumer declares `-d:nelliFwrapv`, a define the
profile does read, and which a native pin row (UBSan plus `-fwrapv`) checks.

Three things derive from the one constant:

1. **The cache key.** `cacheSegment(p)` iterates `fieldPairs` over the
   semantic fields with an explicit field list, a `static` assertion that
   semantic + provenance lists cover every field, a segment tag with a
   version, and a golden string per build pinned in the CR2 cache-key test.
   (Nim's `$` on an object changes with any field rename or reorder.) It
   replaces the hand list at `canonicalize.nim:6558-6592` (INT-31's `|bf=`
   half) and the `defined(nimPanics)` default at `:6537`.
2. **Refusals at macro time.** `admitBuild(buildProfile)` runs in
   `symexFind`: a profile outside the verified set is a compile-time
   `error()` naming the field. Refused by name: `--mm:refc` (D-0016-7, from
   Wave 1), 32-bit `int`, an unverified Z3, Nim or PCRE build, and arm64 and
   macOS **until a CI leg runs the suite there** (a compile-only leg cannot
   satisfy §12). The C compiler is a pin axis, not a refusal axis.
3. **On the verdict.** `Soundness.profile` carries the segment string, so a
   finding renders "decided on c/orc/goto/64-bit, panics off, gcc" and a
   cached verdict read under another profile is a different key, never a hit.

Every walker arm that depends on the build reads `buildProfile`; a test pins
that `defined(nimPanics)`, `compileOption(` and `defined(release)` occur in
`src/nelli` only inside `buildprofile.nim`. `{.push.}` regions stay in the IR
as `feCheckOption` markers: the profile is the command-line baseline,
`check_options.nim` the per-routine delta. An inlined stdlib body's push is
visible only in `implDigest`, so an `admitStdlibBody` row carries its
check-option delta or declines under a push.

**Build rows and legs.** Linux c (CI-A), Linux cpp and Z3 4.13.4 (CI-B),
mingw (symex-mingw), and **MSVC**, a shipping build no `tsymex_*` file runs
today: a `symex-msvc` job (c, vcc) joins the CI-B rotation. arm64
(`ubuntu-24.04-arm`) and macOS (`macos-14`) are refused until their own run
legs exist; INT-25 and PND-03 wait on the macOS one.

### §8.4 The mechanisms, as views of admission

| K | what | closes |
|---|---|---|
| K1 | universe test and ledger (§8.2) | the finish line itself |
| K2 | dispatch census over every `case n.kind` in `src/nelli`; `typeIdOf(sym): Option[string]` as the only source of exception type ids (`none` is `eeUnknownExnType`); child-shape census corpus | W-01, W-04, W-15, W-21, W-27, W-33 |
| K3 | the type × memory-op and local-pragma axes (the pragma list is hand-written: Nim has no enum of `var`/`let` pragmas, so the guard is checked against Nim's `pragmas.nim` text) | W-02, W-12, W-20, W-43, B-04 |
| K4 | the magic axis with a lib-wide guard; a bodied magic not admitted as walked-by-body declines; the stdlib-body axis seeded from a `feStdlibBodyWalked` hint; every raise-text decline gets a `SymexErrorKind` | W-05, W-06, W-22, W-24, C-11, C-16 |
| K5 | `BuildProfile` (§8.3) | W-03, W-14, W-17, W-23, W-50..53, INT-31 |
| K6 | `mayWrite(n)` over the read-only axis; a walked user callee recurses with a cycle bound, an opaque one may write anything; pinned on a write-shape corpus with native runs | W-08..W-10 |
| K7 | degrade discipline by type (below) | W-07, W-11, W-16, D-13 |
| K8 | differential fuzzer (slice D1, §4, §10), its families generated from the axes | the next W-01, before a consumer finds it |
| K9 | one shared native-pin helper (below) | W-54..W-56, W-61 |
| K10 | undefined behaviour as an outcome (§9) | W-05, W-06, W-07, W-13 (settle half) |

**K7, concretely.** `degrade` stops being exported from the walker. The
token-dropping primitive becomes `proc halt(w: var WalkCtx; kind; msg)`,
returning nothing: the absence of a token *is* the halt, so `discard`
leaves the vocabulary. Every other degrade result flows into
`forkPathTainted` or `taintInPlace`, which is already how 93 of the call
sites use it. The 20 `discard w.degrade(` code sites (19 in `runtime.nim`,
1 in `runtime_heap.nim`) have three shapes, an arm return, a void return in a
routing proc, and a per-path drop inside a loop, and each converts to `halt`
plus its own control flow. The `isUnsupported` arm becomes
`proc walkUnsupported(stmt, paths, w): Survivors` with no conversion from
`seq[Path]`, so the token-less `return paths` at `runtime.nim:24500-24502`
cannot be written; W1-d2 deletes that line first. The K2 census asserts no
`discard` of a `degrade` call. W-11 (`svWithRaw` returning the old value for a
composite) and W-16 (`defectExclusions` making a Defect path unreachable with
`sxUnsat` still trusted) are the same discipline: each records a
`dcOmitted` halt instead.

**K9, concretely.** It grows `tests/s8cu_helpers.nim`, which already shares
`native`/`declines`/`decides` by import, instead of starting a fourth
lineage beside the 35 `nativeHits` copies and the 55 `declines` templates.
It is built on `assertCoveredBy`'s argument splat, so it is not tied to
`proc(k: int)`, and it runs the walker's own `sxSat` witness natively as well
as the domain:

```nim
type Domain*[T] = object
  values*: seq[T]; exhaustive*: bool
func exhaustive*[T](v: openArray[T]): Domain[T]
func sampled*[T](v: openArray[T]): Domain[T]
const boundaryInts* = sampled([low(int), low(int)+1, -1, 0, 1, 7, high(int)-1, high(int)])
macro pinExact*(fn: typed; cell: static Cell; target = tLabel("hit");
                domain = boundaryInts): untyped        ## returns the SymexResult
template pinDecline*(fn: typed; cell: static Cell; kind: SymexErrorKind;
                     target = tLabel("hit"))
template pinRaised*(fn: typed; cell: static Cell; exn: typedesc; domain = boundaryInts)
```

The cell is a typed value from `admission.nim`, so a typo is a compile error;
`kind` is mandatory on a decline; the helper writes the pin record K1 joins
on, and returns the `SymexResult` for extra checks. Whether an unsat is
exhaustive is the declared domain's property, not a separate entry point.

## §9 — Undefined behaviour is an outcome (K10)

**The problem.** Nim's checked operations define their failure as a Defect.
Its unchecked ones are plain C operators, and C leaves several of them
undefined: the compiler may assume they never happen and rewrite code around
them, including code that runs *before* them. The walker today models one
build's outcome as the semantics:

- two's-complement wrap for signed overflow under checks off
  (`runtime.nim:24500-24502`; gcc folds `v + 1 > v` away, W-07);
- an x86 trap for `low(int) mod -1` (`:8862-8870`; gcc folds a literal `-1`
  to 0, W-05; arm64 returns 0 for any divisor);
- a catchable `DivByZeroDefect` for unsigned division by zero (natively
  SIGFPE, W-06). That outcome comes from two sites: the walked `div` forks
  through the `divByZeroConds` sink (`runtime.nim:1953`, drained at
  `:19026`), and the opaque-call defect scan reads `divMagics`
  (`dsl_parser.nim:4023-4025`, consumed at `:4152`).

Replay is no evidence: a replay on the native build agrees with that build's
choice and says nothing about `-O2`, clang, MSVC or arm64.

**What is and is not undefined, on the default build too.** Unsigned
`div`/`mod` by zero (`ccgexprs.nim:676-677` emits a plain `/`) and
`INT_MIN mod -1` (`nimModInt` is a plain C `%`, `lib/nimbase.h:587`, on the
checked path as well, `ccgexprs.nim:602-614`) are undefined with every check
on. Float to int out of range is the same class. **Shifts are not:** Nim's
codegen masks the count in C (`ccgexprs.nim:665-667`,
`<< (NU)(count & (width - 1))`) on every target and compiler, so
`shiftCountBV` (`runtime.nim:6213-6220`) is exact and is a *defined* row of
the table, pinned to that codegen line. (The research report's B-08 called it
a hardware mask; round 2 corrected it.)

### §9.1 Design

The CBMC / Frama-C RTE / Alive2 treatment, expressed in this engine's
existing vocabulary:

1. **The definedness axis** (§8.1): `(op, operand class)` read with the
   profile, three answers: *defined* (exact, including wrap where the
   profile defines it: unsigned arithmetic always, the masked shift always,
   signed add/sub/mul under a declared `-d:nelliFwrapv`), *Defect* (Nim's
   checked operation: the existing raise fork), *undefined*. The default
   build is a row of the table, and the table is written out in the ledger,
   not in prose. `arithTrapConds` is retired: it is a hardware-specific
   definite outcome.
2. **Each unchecked op forks on its definedness condition**, using the
   predicates the walker already has (`addNoOverflow` and its siblings,
   `runtime.nim:8478-8492`). The defined side continues exactly. The
   undefined side halts with kind `ubUndefinedBehaviour` (`dcOmitted`, run
   coordinate `{scIncomplete}`), **but only if it is feasible**: `degrade`
   records its kind unconditionally (`runtime.nim:16613-16632`), and a halt
   has no later solve, so without a check `if y == 0: return; x div y` would
   taint every run that guards its divisor. The `(pc, cond)` pairs are
   collected in a sink like `defectSurvivorPc` and decided as one
   disjunction at path exit: one solve per terminal path, not per op. Where
   a Defect fork already covers the condition (checks on), the op is
   *Defect*, not undefined, and there is one fork, not two.
3. **A trusted `sxSat` needs the whole run defined, not only its prefix.**
   C's undefined behaviour is not sequenced, and the walk stops at the first
   label hit (`shouldStop`, `runtime.nim:17308-17318`), so it never sees what
   follows. Rule: if a static scan of the routine's IR finds any op whose
   definedness row is *undefined* on this profile, the winning path is
   continued from the label under its witness. The continuation must reach a
   routine exit (return or raise) with every definedness predicate on it
   unsat. Any other ending (a budget such as `maxLoopUnwind`, a query
   timeout, a predicate over a free symbol the witness does not bind, a
   decline marker) counts as undefined. `symexFindAllWitnesses` runs one
   continuation per witness.
4. **The verdict carries it, and replay cannot lift it.** `Soundness` gains
   `witnessUndefined: bool`, cached with the verdict (it is a function of the
   program and the profile). `trustedSat` (`soundness.nim:163-169`) becomes
   `(today's rule) and not witnessUndefined`, so a native replay that reaches
   the label on this build cannot make the verdict `trusted()` through
   `settleWinner` (`symex.nim:3387-3407`). The `{.noinit.}` read (below) sets
   the same field.
5. **Undefined behaviour is a target, not a status.** `stkUndefined`
   (`tUndefined(classes: set[UbClass] = all)`), beside `stkNilAccess`
   (`types.nim:1862`). `sxSat` comes with a witness; `sxUnsat` means none of
   the *listed* classes is reachable, never "no undefined behaviour", and
   `$target` (`symex.nim:217`) renders the list. The result gains
   `undefined*: seq[UbFinding[T]]` (class, source anchor, witness), and an
   undefined behaviour reached under any other target is listed there, not
   in `diagnostics`, which is typed for raised Defects. A halt under another
   target names `tUndefined` as the next query in its message. No
   `SymexStatusKind` member is added; `SymexTargetKind` grows, so a
   consumer's `case` on it without `else` is a 0.10.0 break, in the migration
   note.
6. **Replay does not run a `tUndefined` witness** (refused by target kind).
   `assertCoveredBy` never executes one in the host; its splat catches
   `Defect` regardless (W-26). `symexForAll` does not seed one unless asked.
7. **The native pin is UBSan**: `-fsanitize=undefined
   -fno-sanitize-recover`, gcc/clang, Linux (CI-A). MSVC has no UBSan and
   mingw's is unsupported, so the Windows legs carry declared
   `out-of-scope(no sanitizer)` cells for these rows; the unsigned-zero-divisor
   crash pin asserts "the child did not finish" rather than a signal, since
   Windows reports an SEH code.
8. **`arithChecks` is removed in 0.10.0** (with `fromCache`, INT-39): the
   checks are a fact of the build. A consumer who later wants "assume no
   undefined behaviour" gets an `assumptions: set[VerdictAssumption]` field
   on `Soundness`, rendered on the finding and keyed; not in 0.10.0.

**Float to int out of range** moves to the halt. Today it is a tainted fresh
symbol (`feConvFloatToIntUndefined`, `dcFreshSymbol`,
`runtime_floats.nim:230`); under the time-travel rule a fresh symbol is not
sound for a trusted `sxUnsat` either. The sweep-diff records the precision
change.

**`{.noinit.}` is not a halt.** A read of a `{.noinit.}` variable is an
indeterminate value, and the walker already models it soundly as havoc
(`runtime.nim:9226-9240`), so an `sxUnsat` stays trusted. The defect is that
replay *confirmed* a witness that needed garbage memory (W-13). The fix is
item 4's field, set on any path that read one; its native pin is
MemorySanitizer or valgrind, since UBSan does not detect it.

**Wave 1 (0.9.2) ships the fail-closed half** before the table exists (§11
W1-d1, W1-d2, W1-d3): the zero side of an unsigned divisor and the
`INT_MIN mod -1` side halt (the nonzero side stays exact); a checks-off
signed op declines; the `{.noinit.}` field. K10 in 0.10.0 restores the
defined side of signed arithmetic under a declared wrap and adds the target.

## §10 — The oracle is part of the universe

Every `exact` cell is measured against native execution, so the native side
has to be right too.

- **Boundary values.** Integer domains include `{low, low+1, -1, 0, 1, 7,
  high-1, high}` (K9's `boundaryInts`). W-05 and W-07 live at `low(int)` and
  `high(int)`, which a `0..7` domain never reaches.
- **Witness-directed.** The native side always runs the walker's own `sxSat`
  witness, whatever the domain. An `sxUnsat` cell is `exact` only on an
  exhaustive domain; otherwise it is `sampled`. The fuzzer's own domains
  (§4.2) are exhaustive by construction; `sampled` comes from K9 pins.
- **The declared domain is the enumerated domain.** `symexAssume` is a no-op
  natively (`engine/markers.nim:127`); the harness enumerates exactly the
  domain the walker was told, or the generator emits the guard as a real
  early return.
- **Capture window.** Marker capture is per thread (`markers.nim:70`). The
  harness asserts the SUT starts no thread and runs each point in a fresh
  scope, so hooks fire inside the capture window.
- **Sanitized native rows.** A native run that executes undefined behaviour
  is not evidence (§9). The fuzzer's native build row includes
  `-fsanitize=undefined,address`; a cell goes `exact` only on a
  sanitizer-clean native run.
- **Witness rendering has an oracle.** Per `IRTypeKind`: render, parse,
  compare with the witness, including NaN, −0.0, embedded NUL and shared
  `ref` cells (`runtime.nim:30854-30930`).
- **A second oracle where cheap.** For generated SUTs with no `importc` or
  pointer arithmetic, the Nim VM (`nim e`) gives a third column: walker
  against the Nim language versus Nim against the C backend. Every Tier-0
  row in §5.0 is a desugaring bug of the first kind.
- **Public entry points.** K1 refuses an `exact` cell whose pin record does
  not come from `symexFind`, `symexForAll`, `assertCoveredBy` or the
  concolic path.
- **Families from the axes.** The fuzzer's families iterate `cells(axis)`
  (every exact row with its shapes and build rows), so coverage means "row
  exercised on its build rows", not a hand list. `tfuzzconcolicmismatch` and
  `annotationViolations` (INT-33) are a second findings source; INT-33's
  reader is a K8a dependency.
- **Triage has a sink.** The nightly job uploads `findings/<date>.tsv` and
  the shrunk `.nim` files as an artifact and opens or updates one issue per
  new shape hash. Within the week each issue becomes an `F-NNNN` row with its
  three-way probe (§6).

## §11 — Slices and order

Each row is a slice within about three modules; a row marked *round* flips
verdicts broadly and is gated by a pinned sweep baseline from a worktree at
its base sha (`sweep.sh` + `sweep-diff.sh`), not by its own tests.

**Wave 1 — 0.9.2: the seven clean false verdicts.** The walker version is
bumped in the first semantics-bearing slice (W1-a) so no intermediate sha
serves a stale cache; later Wave-1 slices take floors above it and W1-z
assigns the final number. Every pin goes through `symexFind` or
`assertCoveredBy` and runs its witness natively, through K9a.

| id | scope | modules | RED test (default build: c, orc, goto, checks on, unless stated) | size |
|---|---|---|---|---|
| K9a | the pin helper and pin records (§8.4); the 35 `nativeHits` copies are migrated later (K9b) | `tests/s8cu_helpers.nim` | the helper itself: a planted wrong `exact` pin fails | s |
| W1-a | `typeIdOf`; W-01, W-33; first walker bump | `dsl_parser.nim` (:20461, :20444) | `try: (if k==3: raise newException(ValueError,"x")) except ValueError as e: symexTarget("h")`: `tLabel("h")` `sxSat` (today `sxUnsat`), native hit at 3; `tRaisedExn("ValueError")` `sxUnsat` (today `sxRaised`). `let e = newException(ValueError,"x"); raise e` is `sxRaised ValueError`; `raise ex` with `ex: ref Exception` a parameter declines `eeUnknownExnType` | s |
| W1-b | local-pragma allowlist (`noinit`, `global`); every other local pragma declines (W-02) | `dsl_parser.nim:19771` | `gs = @[k]; var c {.cursor.} = gs; gs[0] = 9; if c[0] == 9: symexTarget("shared")` and its `let` twin: `sxUnknown`, kind names `cursor` (today a trusted false pair, c/orc, c/arc release, cpp); `{.noinit.}`/`{.global.}` SUTs unchanged | s |
| W1-c1 | `buildprofile.nim` const; reroute `symex.nim:2343` and `canonicalize.nim:6537`; refc refused by name (D-0016-7); constructor-only pin | `buildprofile.nim` (new), `symex.nim`, `canonicalize.nim` | `defined(nimPanics)` occurs in `src/nelli` only in `buildprofile.nim`; a `--mm:refc` compile of a `symexFind` SUT fails naming the field; no verdict change (sweep-diff empty) | xs |
| W1-c2 | under panics a Defect is the S8cu `crash: true` escape (W-03, INT-27) | `runtime.nim` (`routeRaise` :25666, drains :19186, :23574), `tsymex_0016_panics.nim` + `.nim.cfg` `--panics:on` (the suite's first panics row) | `try: discard v+1 except Defect: symexTarget("h")`: `tLabel("h")` `sxUnsat`, `tRaisedExn("OverflowDefect")` not `sxRaised` (today both clean); native: a spawned child does not finish (the `s8cu_nil_native` shape) | s |
| W1-c3 | `assertCoveredBy` splat catches `Defect` (W-26) | `symex.nim:4106-4117` | `symexTarget("hit"); discard v + 1` with a `high(int)` witness: reported, host alive (today the process dies) | xs |
| W1-d1 | unsigned zero divisor and `INT_MIN mod -1` halt, feasibility-checked (§9.1 item 2); `ubUndefinedBehaviour` kind | `runtime.nim` (:8862, the `divByZeroConds` drain :19026), `dsl_parser.nim:4152`, `types.nim` (+ lattice test); rewrites the trap pins in `s8aa_remainder`, `s8i_models` | `if x == low(int): (let q = x mod -1; if q == 0: symexTarget("t"))` not a trusted `sxUnsat` (today trusted; native hit). `let r = 10'u64 div uint64(k)`: `tRaisedExn("DivByZeroDefect")` not `sxRaised`; with `except DivByZeroDefect: symexTarget("c")` not a trusted `sxSat`; `r == 5` at `k == 2` stays `sxSat`; `if k != 0: …div…` keeps a trusted `sxUnsat` where one is right; native child does not finish | s-m |
| W1-d2 | checks-off signed op declines: delete the early return at `runtime.nim:24500-24502` (W-07) | `runtime.nim`; rewrites the wrap pins in the 13 files that opt `acOverflow` out | `{.push overflowChecks: off.}` `if v+1 > v: discard else: symexTarget("hit")`: not a trusted `sxSat` (today clean `sxSat` at `high(int)`; gcc folds it away) | s |
| W1-d3 | `Soundness.witnessUndefined`; set by a `{.noinit.}` read (W-13); cache-format bump (`soundnessMetaVersion`, `symex.nim:268`) | `soundness.nim`, `runtime.nim:9226`, `symex.nim` settle | `var x {.noinit.}: int; if x == 0: symexTarget("z")`: not `trusted()` on c, cpp and arc release alike (today build-dependent) | s-m |
| W1-e | float width conversions decline (W-04) | `dsl_parser.nim` :10658, :10845 (and :4126 if it shares the path) | `let y = float32(x); if float64(y) == x: symexTarget("same")` and a hidden-conversion twin: `sxUnknown` with a conversion kind (today clean verdicts); int↔float verdicts unchanged | s |
| W1-f | object field defaults decline (W-20); `case` with `elif` (W-21) | `dsl_typebridge.nim` field walks (:646-650, the plain-record twin, tuple :1350-1356); `dsl_parser.nim` :19300, :12789, :5821 | `type O = object; x: int = 5`, `var o: O; if o.x == 5: symexTarget("h")` compiles and declines (today a compile stop); `case x of 1: … elif x > 5: symexTarget("big") else: …` in statement, expression and `hoistCaseExpr` forms: `sxSat`, native 6 | xs-s |
| W1-g | `x in a..b` / `notin` (W-31) | `dsl_parser.nim:11070` | `if x in 0 .. 10 and x == 7: symexTarget("t")` `sxSat`, native 7; `notin`, `char` and enum slices | s |
| W1-z | integration: final walker number, CR2 pin, three-way rows (0.9.1 / head / native) for every W1 row, `docs/migration/0.9.2.md` (the bump, the new kind, the new declines, the known-gap list §2.4 requires) | `canonicalize.nim:251`, CR2 test, docs | — | s |

**0.9.2's gate.** CI-A does not exist yet, so the release is gated by
`sweep.sh` on c, cpp and Z3 4.13.4 from a worktree pinned to the W1-z sha,
diffed against a 0.9.1 baseline from a worktree at its own sha (every flip is
either a Wave-1 row or accepted in the migration note), plus the three
Windows legs green at that sha, then `/wiring-audit` and `/code-review` to
floor before the tag. W-32's five syntax declines (research A-06) are
precision, not one of the seven, and move to Wave 4.

**Wave 2 — the enforcing substrate, live from its first commit.**

| id | scope | depends | size |
|---|---|---|---|
| CI-A | `symex-linux` on every push: the `2.2.10-linux-x64` Nim artifact (verify it is published first), Z3 5.1 from its release archive with `LD_LIBRARY_PATH`, PCRE 8.45 from source (cached; Ubuntu's 8.39 is unverified), a derive mode for the whole `test` task (F-06), a portable suite runner, and a committed known-red allowlist from one baseline run on the Ubuntu toolchain | — | m-l |
| CI-B | the same workflow on `schedule:` and `workflow_dispatch`: cpp, Z3 4.13.4 on Linux, and `symex-msvc` (c, vcc); a red run opens or updates an issue; required at every wave integration and tag | CI-A | s-m |
| K9b | migrate the 35 `nativeHits` copies and the `declines` templates that already name a kind | K9a | s |
| ADM-1 | `smt/admission.nim`, `feUnadmitted` (`dcNoAnswer`); `varParamMagics` and `verifiedLibs` moved onto it with no verdict change (the second-consumer spike, §8.1) | — | s-m |
| K1a | universe test and post-shard job; axes: error kinds, the ADM-1 tables, build rows; the §5/F join; per-axis ratchet; planted RED on each leg | ADM-1, K9a, CI-A | m |
| K7a | `halt`; the 20 `discard w.degrade(` sites | — | s |
| K7b | `walkUnsupported(…): Survivors`; `feUnadmitted` to `dcOmitted`; W-11, W-16 | K7a, ADM-1 | s |
| INT-33 | `annotationViolations` gets its reader (K8a's second source) | — | s |
| K8a | fuzzer skeleton with one family (the §5.0 construct shapes), boundary domains, a scheduled Linux job rotating one build row per night, the triage sink of §10 | K9a, CI-A, INT-33 | m |
| S8cj | carried: thread-history spend; Z3 mk_unique (D-0016-3 waits on it for UPS-02) | — | m |

**Wave 3 — the tables.** Each introduces its axis under §8.2's rule, adds its
fuzzer family, and shrinks its allowlist.

| id | scope | depends | size |
|---|---|---|---|
| K2a | dispatch census over every `case n.kind` in `src/nelli`; site registration | K1a | s |
| K2b | float width conversions exact (`fp.to_fp`, RNE) | K2a | s-m |
| K2c | child-shape census corpus (includes CRH-01's `classifyType` stops) | K2a | m |
| K3a | type × memory-op axis under `typeCopiedByValue` and `holdsSharedMemory` (*round*) | ADM-1, K1a | m |
| K3b | object field defaults exact (`wasMoved` stays bitwise zero) | K3a | m |
| K4a | magic axis, generated `dispatchMagic`, lib-wide guard | ADM-1 | m |
| K4b | an unadmitted bodied magic declines (*round*) | K4a | m |
| K4c | stdlib-body axis with check-option deltas (*round*) | K4a | m |
| K5a | full `BuildProfile`; `cacheSegment` with golden strings; readers migrated with no verdict change (INT-31's `\|bf=` half) | W1-c1 | m |
| K5b | refusals (32-bit, unverified Z3/Nim/PCRE, arm64, macOS); `-d:nelliFwrapv` declared wrap; cfg suites for `--mm`, `-d:useMalloc`, setjmp, `-d:release` (W-58) | K5a | s-m |
| K6a/b/c | `mayWrite` into `nodeWritesHeap`, the hook copy-proof, then `ptrUsesStayLocal`/`routeStoresThroughDeref` (*round* each) | ADM-1 | m each |
| K10a | the definedness axis; `stkUndefined`, `UbFinding`; replay refusal by target kind; float-to-int to the halt | K5a, K7b | m |
| K10b | whole-run definedness continuation (§9.1 item 3) | K10a, W1-d3 | m |
| K10c | UBSan pin suite (Linux); declared Windows cells | K10a, CI-A | s |
| K10d | `arithChecks` removed; `docs/migration/0.10.0.md` (`fromCache` INT-39, `arithChecks`, `SymexErrorKind` deletions and additions, `stkUndefined`, `Soundness.profile` and `witnessUndefined`, the second cache cold start from `cacheSegment`) | K10a, K5a | s |
| PRC-01/02 | Windows re-exec replay: marshal case-object, `ptr`/`ref`, proc-value, `method` and `{.global.}` witnesses (the first precision item; consumers' main platform) | — | m, m |

**Wave 4 — the search, then the tail.** Fuzzer families per axis; the
pairwise figure; the VM column; witness round-trip pins; the allowlists
emptied. Then the tail: the 132 decline assertions with no kind (each kind
found by running it), pins for the 481 verdict suites with no native idiom
(generated by family where the SUT is a pure proc), W-32, and the precision
rows of §5 and §5.9 in the frequency order of the research list.

**Carried slices.** The pending `[[slice]]` rows from RFC-0005 map here:
S8cj to Wave 2 (above); `rv0005-lows` loses INT-31 (K5a, and its `;impl=`
half stays with the row) and INT-33 (Wave 2) and keeps the rest for Wave 4;
S8ck-r (nim-z3 hygiene, INF-04), S8cg, S8ch, S8ci, S8co and S8cp-r are Wave 4.
UPS-01 and UPS-03 are filed by the coordinator before W1-z and their URLs
recorded in §5.6.

**The walker under sanitizers.** A scheduled job runs a slice of the corpus
with nelli itself built under ASan: a use-after-free in a Z3 AST can produce a
wrong verdict, not only a crash (CRH-07).

## §12 — The finish line

Decision D-0016-1 closes the RFC when the work list is empty. This section is
how "empty" is measured, so that it is a test result and not an opinion:

1. `tsymex_0016_universe` is green with **every axis's allowlist empty** on
   every build row with a run leg (Linux c, Linux cpp, Z3 5.1 and 4.13.4,
   mingw, MSVC): no unclassified cell; every `exact` cell has a pin record
   from a public entry point on each row it claims (`rows` is never empty);
   every `declined` cell's pin asserts its kind; `sampled` unsat cells counted
   separately from exhaustive ones.
2. Every open id in §5, §5.9 and the handoff's F ledger is named by a cell
   that is `exact`, `declined` or `out-of-scope`, and every F row is `fixed`,
   `declined` or `refuted`.
3. No failing file on any gate; no `skip()` or platform arm without a
   `cell:` reason; no decline assertion without a kind.
4. The fuzzer has exercised every exact row on its build rows, and the
   pairwise figure (two productions in one SUT with a definite verdict) is at
   or above the floor set by K8a's first full run, ratcheted.
5. **No precision regression bought the empty list.** Against the 0.9.1
   pinned corpus, no verdict that was exact and natively correct there is
   declined at the end without a §5 row saying why (the W-wave three-way rows
   and `sweep-diff.sh` measure it).
6. The certifying gate logs carry their `.summary` sidecars: CI-A emits the
   same shape `sweep.sh` does (`scripts/sweep.sh:277-294`).

Size, from the research: about 1,000–1,100 cells, most classified in bulk from
the code's own dispatch; the tail is about 250 construct cells and 190
type × operation cells that each need a pin. Two to three months of slice
work plus the fuzzer's hours, measured by one test's output.

## §13 — Alternatives considered

- **Model the post-`transf` AST through the patched compiler.** Every Tier-0
  construct row is a desugaring the walker re-implements (`except T as e`,
  hidden conversions, stripped pragmas); the compiler's transformed tree has
  them already lowered. Not taken in this RFC: it rewrites the 23k-line
  parser against an unstable internal representation, and it does not touch
  the type, memory, magic, build or undefined-behaviour classes. A candidate
  for its own RFC, measured against K2's census once that exists.
- **CBMC or KLEE on the generated C** as a wide-domain `sxUnsat` oracle.
  Deferred: §10's boundary values and witness direction cover the known
  rows; reconsider if the `sampled` count stays high.
- **Gated clean-path replay** (INF-02): declined by D-0016-2; §9.1 item 3 is a
  model-side check on one path, not a replay.
- **A generic `Admission[K]` row type with `admit(table, key)`** (round 1):
  replaced in round 2 by per-axis verbs and generated dispatch (§8.1), since
  a shared row type left every consumer building its own key and its own
  `case`, two lists that could drift.
- **A `proven(paths, pin)` constructor for K7**: dropped; a pin string at walk
  time proves nothing, and after K10 no unsupported arm has a clean exit.
- **Reading `-fwrapv` and the compiler version from `querySetting`**: not
  possible (§8.3); declared instead.
- **A hand-annotated ledger reconciled against the code**: replaced by §8.2's
  generated ledger.
- **A new `sxUndefined` status**: replaced by a target kind, a halt kind and
  `witnessUndefined` (§9.1), with no status break.
