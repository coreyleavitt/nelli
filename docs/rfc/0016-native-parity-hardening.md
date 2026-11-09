+++
type    = "rfc"
id      = "0016"
title   = "RFC — native-parity hardening: the walker agrees with the compiled program, or declines"
state   = "in-progress"
wiring  = "proven"
review  = "floor"
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
state = "in-progress"

[[slice]]
id    = "W1"
title = "Wave 1 / 0.9.2 (§11): INF-05 and the 0.9.1 baselines, K9a, W1-c3, W1-a, W1-c1a/b, W1-c2, W1-p, W1-b/e/g/f, W1-d1a/b/c, W1-d3, W1-d2 (round), K1-0, W1-m, W1-z (20 rows): the seven false verdicts of §5.0 end to end, plus W-20/21/26/31/33/52, the walker on MSVC, the release gate"
state = "done"

[[slice]]
id    = "W2"
title = "Wave 2 (§11): K5a build profile first, CI-A1/A2/A3 and CI-B legs incl. symex-msvc, K9b, ADM-1, K2-s census, K1a-cells/ids/last/ci ledger over the TOML work list, K7a/b Survivors and CapKind, K2-0 probe batch, K9d-0, K8-0, K8a-gen/job/sink, S8cj, W2-z"
state = "done"

[[slice]]
id    = "W3"
title = "Wave 3 / 0.10.0 with Wave 2 (§11): admission tables K2a-c, K3a-c (type class, memory, pragma), K4a-table/dispatch/guard, K4b/c, K5b refusals, K6a-c, K10a-target/axis/float/concolic, K10b (round), K10c/d, PRC-01/02, W3-z"
state = "in-progress"

[[slice]]
id    = "W4"
title = "Wave 4 (§11): K8b fuzzer and metamorphic families with pairwise floor, K8c sanitizer job, K7c, K9c, K9d, K9e pin strength, K2a-fail, H1 hygiene, precision rows, W4-z allowlists emptied and §12 checked"
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
title = "S8by's item 3 reopened: a term order that earns its cost, r4_strip back to S8bm, wide factoring decided again"
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
title = "The RFC-0005 code review's open Lows (INT-28 to INT-38 less INT-31 and INT-33): replay child hardening, cache-key coverage, replay and settle policy, fuzzer-path liveness, design cleanups, exit-group guards, finding-collector edges, precision probes, cache hygiene"
state = "pending"

[[audit]]
id = "review-1"
closes = "review"
verdict = "pending"
at = "c53ea0f89f8cfba7c89dd6f88a9277e36ffeb393"
owner = "corey"
date = 2026-11-07
reason = "0.9.2 code review opened over e769b87d..d9086529: round 1 found SC2 (High, fixed), D1 (High, open), M2-M6 and N1 (fixed); ledger 0016-review"
ledger = "0016-review"

[[audit]]
id = "wiring-1"
closes = "wiring"
verdict = "proven"
at = "785c4a6a2f952115445555e4efedf814cf8552c2"
owner = "corey"
date = 2026-11-07
reason = "Wave 1 wiring audit (two lenses at c0f59ca6): S1-S4 soundness and P1-P4 fixed with RED/GREEN pins (af8de076, 96165e3a, d9086529); F3-F5, F7, F10-F12 fixed (06ac34b9); K1-0 join green on c, cpp and z3-4.13.4 at d9086529, on c and cpp in CI; mingw/MSVC joins and rowOf deferred to Wave 2 (K1a-ci, K5a)"

[[audit]]
id = "review-2"
closes = "review"
verdict = "floor"
at = "205e20e50ee6b1ef2564a4bf00571b86386a8d53"
owner = "corey"
date = 2026-11-07
reason = "round 2, 0 C/H/M at 6a242791; round 1 fixed SC2, D1, M2-M6, N1; open Lows filed as INT-42"
ledger = "0016-review"
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
  Wave 1 into slices with RED specs, and reconciled §5 against head; round 3
took test and tracking metadata out of the admission rows, fixed the
undefined-behaviour sink to decide at the op, made `-d:nelliFwrapv` produce
the flag, added MSVC, the 4.13.4 tooling and publication to the 0.9.2 gate,
and gave every finish-line item and intake sink a producing slice; round 4
(2026-11-07) named the property the RFC lives on and runs it end to end in
Wave 1 (K1-0), added the trust base (§2.5), made admission a proof the IR
demands, moved the work list to TOML, split the build profile by when it is
known, routed undefined behaviour through the crash channel with an eager
check and the `Degrade` token, reordered Wave 1 (INF-05 and the release-asset
baselines first), split every slice that crossed three modules, and added
cost, docs, metamorphic and mutation figures to the finish line.
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

### §2.5 The trust base

What a trusted verdict rests on without being checked by this RFC, and what
mitigates each:

| trusted | mitigation |
|---|---|
| Z3's `unsat` | the Z3 4.13.4 and 5.1 rows run the same queries (CI-B); exhaustive native domains refute a wrong `unsat` where the domain is small; nothing refutes it outside the domain (§13) |
| nim-z3's FFI and the cache codec | ASan job (K8c); the codec's static pin and CR2 |
| the patched Nim 2.2.10 and its macro VM (the parser runs in it) | `nimVersion`/`patchset` rendered on every finding; a stock-Nim row pinned by K5b on a corpus slice, and refused if it differs; `vm_alias_guard` over a sampled slice in CI-B (the "parser VM" cell) |
| the C compiler behind native pins | native pins run on the same build (§2.2); sanitized rows (§10) |
| C flags `querySetting` cannot see (`-ffast-math`, `-ffp-contract=fast`, `-fno-strict-aliasing`, `-ftrapv`, `-fsanitize=*`) | `BuildProvenance.assumedAbsent` rendered on findings and in `docs/symex/README.md`; a `never(unobservable)` cell; K10c pins the Linux x86-64 row without contraction |

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

<!-- worklist:begin 5.0 -->
| ID | Item | Evidence | Cause | Slice | State |
|---|---|---|---|---|---|
| W-01 | `except T as e:`: handler label false `sxUnsat`, raise target false `sxRaised` | V | `dsl_parser.nim:20460-20461` stores the `repr` as the type id | W1-a | closed `c0e8bd44` (2026-11-07) |
| W-02 | explicit `{.cursor.}` on a local: false `sxUnsat` and `sxSat` (c/orc, c/arc release, cpp) | V | `dsl_parser.nim:19771-19792` drops every local pragma but `noinit` | W1-b | closed `2b5a1f8e` (2026-11-07) |
| W-03 | `--panics:on`: a label after a Defect is a clean `sxSat`; natively the process dies | V | the walker never reads `nimPanics` (only `symex.nim:2343`) | W1-c2 | closed `6d40f03c` (2026-11-07) |
| W-04 | `float32` ↔ `float64` conversions, hidden ones included: false clean verdicts | P | transparent `else: parseExpr(operand)` at `dsl_parser.nim:10658`, `:10845` | W1-e | closed `86536fa9` (2026-11-07) |
| W-05 | `low(int) mod -1`, literal divisor: false `sxUnsat` (gcc folds to 0) | P | `runtime.nim:8862-8870` traps regardless of divisor or target | W1-d1a | closed `e044a290` (2026-11-07) |
| W-06 | unsigned `div`/`mod` by zero: `sxRaised DivByZeroDefect`, natively SIGFPE | P | `dsl_parser.nim:4023-4025` lists unsigned beside signed | W1-d1b | closed `682de5a4` (2026-11-07) |
| W-07 | checks-off signed overflow modelled as wrap: `v + 1 > v` clean `sxSat` at `high(int)` | P | `runtime.nim:24500-24502` consumes the marker with no token; the settings route (`:8881-8897`, `:19032`) is the same model | W1-d2 | closed `0aa6b3bb` (2026-11-07) |

<!-- worklist:end 5.0 -->

Round 2 applied the reconciliation lens's edits to §5.1-§5.8
(`E-reconcile.md`: 16 rows closable at the tag head, 4 closing as a recorded
decline, 14 duplicates, 11 with stale evidence, 3 misclassified); round 3
corrected the ones that lens had read from an older tree. Row ids are stable.
Each row's last column is its state: a row is open unless it starts with
`closed`, `merged`, `moved`, `never` or an owning RFC. K1a-ids moved these
tables into `docs/rfc-data/0016-worklist.toml` with a `cells` field per row and
renders them back here (§8.2): the tables between the `worklist:begin` and
`worklist:end` markers are generated, so edit the TOML and run
`scripts/check-worklist.sh write`; `scripts/check-worklist.sh` (CI's `pins`
job) fails when they differ. F-0001 to F-0007 are the aliases of W-01 to W-07;
the duplicate PRC-36 and PRC-37 of the moved-slices table are PRC-39 and
PRC-40.

Owners are left empty: the coordinator assigns them. "Moved slice" means a
job file on `origin/worker-jobs` written under RFC-0005; it keeps its id and
its scope, minus anything named as staying with RFC-0005.

### §5.1 Soundness, same severity as `main`

All are false verdicts on `main` 6cbfe8f and on the channel at e497dcf (sort,
"Same on both"). Several have a fix that landed in RFC-0005 batch 10 or is due
in batch 11; for those the item is to re-pin natively at the tag head and close
it, or reopen it if the fix did not hold.

Rows were reconciled against head `83c1d304` in `/architect` round 2 (2026-11-06); a closed row keeps its id.

<!-- worklist:begin 5.1 -->
| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| SND-01 | Direct var-returning actual: `rab(t["a"], t, "a")` | sort S1; S8cq item 2 | Closed as a decline at head: `tests/tsymex_rfc0005_s8cq_varret.nim:84,158-159` pins `rab(t["a"], t, "a")` (`p01_r50` native hit, walker `sxUnknown`); `tests/tsymex_rfc0005_s8cq_byvalue.nim:126,162-163` (`vc_rx1`). S8cq landed in batch 11 (`47e3363e`). Exact model: PRC-36. | closed (decline; exact model PRC-36) |
| SND-02 | `$` of a negative int: `$x == "-5"`, `($x).len == 2`, `$x == ""`, `repr(x)` | sort S2; S8cb | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` native values; `:62-63` (`negs`/`negsu`), `:74-80` (char), `:81-99` (enum, string-named enum), `:116-118` (`repr`). S8cb merged `72b2c2b8`. | closed |
| SND-03 | `$` of a char: `$a == "a"` false `sxUnsat`, `$a == "97"` false `sxSat` | sort S3; S8cb | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` native values; `:62-63` (`negs`/`negsu`), `:74-80` (char), `:81-99` (enum, string-named enum), `:116-118` (`repr`). S8cb merged `72b2c2b8`. | closed |
| SND-04 | `$` of an enum, including a string-named enum | sort S4; S8cb | `tests/tsymex_rfc0005_s8cb_tostr.nim:37-41` native values; `:62-63` (`negs`/`negsu`), `:74-80` (char), `:81-99` (enum, string-named enum), `:116-118` (`repr`). S8cb merged `72b2c2b8`. | closed |
| SND-05 | `ensureMove` of an int: `b == 0 and x != -1` false `sxSat` | sort S5; S8cb | `tests/tsymex_rfc0005_s8cl_magics.nim:208-218`: `nativeHits(sutEnsureMove)` then `clean(..., "em_dead", sxUnsat)`. | closed |
| SND-06 | `procCall` zero value: `r == 4 and k != 3` false `sxSat` | sort S6; S8cl | `s8cl_magics.nim:210,220-222` `declines(sutProcCall, "pc"/"pc_dead", "ProcCall")` after the native run; also `tests/tsymex_rfc0005_b10_integration_b.nim:9-12`. | closed (decline; exact model PRC-21) |
| SND-07 | `uncheckedAssign`, the other arm's bytes differ: `o.y != v` | sort S7; S8cp item 2 | Walker pinned `sxUnknown` on `diff` (`s8cp_unchecked.nim:229-230`); the file's native run (`:199-206`) covers only the shape where the other arm's bytes coincide (`same`). The sort's shape where they differ (`p_cp ua3_diff`, native HIT) has no SUT in the corpus: port it with its native hit beside the `sxUnknown` pin, then close as a decline. Exact model: PRC-37. (2026-11-07, W1-z): `ua3_diff` is not a native HIT, because native never reaches `diff`; the decline is conservative, so this is a precision row (PRC-37), not a soundness one. | |
| SND-08 | A hook write through a local ref: `DR(r: r)`, `=destroy` writes `d.r[]` | sort S8 | `tests/tsymex_rfc0005_s8cs_routes.nim:525-526,542-549` (`HeapH` `=destroy` writes `d.r[]`), native `:603`, hits `:616,622`; walker `tests/tsymex_rfc0005_s8cs_routes_c.nim:292-293` `declined(heap1, …)`. | closed (decline; exact model PRC-04) |
| SND-09 | A hook on overwrite, global written first: `gW = 0; var d = mkD(k); d = mkD(k)` | sort S9 | `s8cs_routes.nim:110-113` (`w2`), native `:590`, hits `:608,622`, `declined(w2, …)` `:642-643`. | closed (decline; exact model PRC-04) |
| SND-10 | PCRE stop code read as a match: `s.match(re"(a\|a)*[bc]")` at `a^30` | sort S10; S8cf | `tests/tsymex_rfc0005_s8cf_limits.nim:71-85`: native `std/re` first, then `status != sxUnsat` for `cf_match_hit`. S8cf merged `d08fe846`. One-sided pin; exactness is PRC-33 item 10. | closed |
| SND-11 | PCRE stop code as a witness: `not s.match(...)` at `a^30` | sort S11; S8cf | same file `:92`, `!= sxSat` for `cf_miss_long`. | closed |
| SND-12 | `let` cursor over a shared global: `gc_shared` | S8cn blocker probe 1 | No test contains `gc_shared`. Nearest pin is the local-seq cursor `sCur`/`cu_shared` (`tests/tsymex_rfc0005_s8cn_seqview_e.nim:124-128`). Probe and both-sha logs at `origin/worker-sls2:worker-reports/s8cn-blocker/`. Mechanism `letCursorDecline`, `dsl_parser.nim:16698-16706`. Port probe 1 (a `let` cursor over a shared global): native HIT + `status != sxUnsat`, expect `sxUnknown`. | |
| SND-13 | S8cu's known limits: macro-built pragmas, a pushing template from another module, an import under a push in a module the scan does not read | PND-11, reclassified round 2 | a missed check-off region is the false `sxRaised` class S8cu fixed: soundness risk, not pending **K2-0 probe (2026-11-08): reproduces, a soundness defect.** A push AND its pop both built by macros (`pushOffS()` / `popS()`, `fieldChecks: off`) leave nothing in the source text for the scan: native reaches the label (`fieldChecks` off), the walker answers a false `sxRaised` (`FieldDefect`). The existing S8cu fixtures (`tsymex_rfc0005_s8cu_hidden`) cover only a macro push with a visible pop, which declines. Pinned as the current behaviour with `pinExact` expecting `PinFailure`: `tests/tsymex_0016_k20_probes.nim` (`SND-13` suite). Fix: decline when the module expands any macro or template call in statement position that the scan cannot read, or read the expansion (K3c). | |
| SND-14 | Int-offset arithmetic without an overflow fork (N24, #166; W-19) and the `range[0'u64..>int64.high]` round trip (#169) | decision D-0016-8 | owned by RFC-0014; this RFC carries no work | RFC-0014 |

<!-- worklist:end 5.1 -->

### §5.2 Precision

**Replay and witnesses.**

<!-- worklist:begin 5.2a -->
| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-01 | **First precision item.** Windows re-exec replay: marshal case-object and `ptr`/`ref` witnesses instead of declining. Windows is a consumer's main platform, so a decline there is a decline in daily use Includes INT-01 and INT-14: batch 11 (`7b2ab1e5`) widened the footprint to type symbols, result types and routine signatures, so more SUTs decline on Windows. | S8ct (coordinator ledger, 2026-11-02) | S8ct moved replay to a child process; on Windows a witness of these kinds declines with a named reason, documented in the 0.9.0 migration note and pinned on Linux by the re-exec pin | |
| PRC-02 | Windows re-exec replay: proc-value, `method` and `{.global.}` witnesses decline Includes INT-13: the six hooks `hostRuntimeHook` checks (`replayproc.nim:171-176`); `setControlCHook` stays INT-15. | S8ct | same mechanism as PRC-01; after it | |
| PRC-03 | Replay cannot aim a witness `ptr` at a global: S8cr's three open holes | S8cr; batch 10 integrator | the three open-hole pins give `sxUnknown` (`feGlobalHavoc`, `feReplayRefuted`), not `sxSat`; the false `sxUnsat` is closed, the precision is not | |

<!-- worklist:end 5.2a -->

**Exact models for RFC-0005's declines.**

<!-- worklist:begin 5.2b -->
| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-04 | Inventory every decline RFC-0005 added or widened, and give each an exact model or a recorded reason it stays. Generate the list from the code (decline sites and `SymexErrorKind` members, 6cbfe8f against the tag), not from memory. Known families to seed it: S8cq's by-value allowlist (types where Nim's copy behaviour varies); S8cs's fail-closed global write routes (hooks, opaque routines behind a local alias, `{.emit.}`); S8ct's replay declines (quit, nil deref, unbounded recursion; W1, W2); S8cu's check-option source scan; S8cl's "magic with no body declines"; S8cf's past-safe-length `zsUnknown`; S8ca's `viewFollows` "any other write declines"; S8bk's `feEvalOrderUnmodelled` late address Includes INT-10 (the seven `feGlobalRouteUnproved` pins). The inventory is generated, not written: K2a's census plus K1's `SymexErrorKind` axis (354 decline sites, 91 members, 12 with no producer). | Corey's split, 2026-11-02 | decline-before-verdict was the release fix for most blockers (ledger, 2026-11-02 entries); each decline is sound and costs precision | |
| PRC-05 | S8cn's declines, each to an exact model with native pins: a `lent` loop with a possible write, and a `let` cursor; a by-value actual reached by name, reads included (b9 `sReadOnly` now `feUnsupportedOp`); non-scalar `pairs` and array `items`; a `let` over a formal with any ptr or ref write; a `var`, parameter or computed proc value with a view and a Table (`closureTakesView`); by global name (`sqG`, `gw`); `f(s[i], s[0], s)` and `f(s[0], s[0], s)`; a pointer plus a Table call; a mutated local copy; `t.clear` and `t.pop`; `Table[string, VObj]`; a non-scalar by-value view; `nl2_other_live`, `nl2_same_dead`; two-entry `del` (hash-dependent); the ds, dt, dv forms Includes CRH-05: a pointer plus 11 Table inserts takes past 1400 s; the pin uses one insert. The 'ds, dt, dv forms' are not in `s8cn.md:186-203`: cite their source or drop them. | `worker-reports/s8cn.md` "Declines for RFC-0016" | listed by S8cn as precision; `let c = s` varies across 9 build settings (ledger), so the model must be per build or stay declined | |
| PRC-06 | The `ti_grow` Table `keys` loop that writes the Table, even with no key added: `ti_grow` at `a == 0` is now `sxUnknown`, moved from S8bl's `sxSat` | S8cn | repin accepted at batch 11 intake | |
| PRC-07 | S8cu: exact unchecked semantics — model what a routine compiled with a check off actually does (overflow, bounds, range, field, nil, float checks), instead of the source-position decline Mechanism: K10a/K5a (§9, §8.3). | S8cu | S8cu's fail-closed decline (`feCheckOption`, `feOverflowCheckOption`) closed a false `sxRaised`. (2026-11-07, W1-z): a `--rangeChecks:off` build declines every routine `feCheckOption` | |
| PRC-08 | S8cu: a `-d:danger` or `--fieldChecks:off` build declines every routine Mechanism: K10a/K5a (§9, §8.3). | S8cu | follows from the source scan; depends on PRC-07 | |
| PRC-09 | S8cu: `math.nim`'s pushed regions now decline Mechanism: K4c `admitStdlibBody`. | S8cu | every routine in a pushed region of `std/math` declines | |

<!-- worklist:end 5.2b -->

**Shapes and magics.**

<!-- worklist:begin 5.2c -->
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

<!-- worklist:end 5.2c -->

**Moved slices (precision).** Each keeps its job file's scope; the rows below
name what moves and what stays.

<!-- worklist:begin 5.2m -->
| ID | Slice | Moves | Source | Owner |
|---|---|---|---|---|
| PRC-29 | S8cg | items 2 (copy a `var openArray` view at the call, so `fill(gArr, bumpA())` decides), 3 (a later argument that only reads a global counts as a read), 4 (`ti_tuple` exact `sxSat` under default budgets), 5 (`bb_rep_sym_empty_hit` exact on both Z3 versions), 7 (an index call through a proc value), 8 (`s8bb_constructs` 40.7 s (under 60); `tsymex_r6_b6_optionregion` is absent from `scripts/ci-suite-seconds.tsv`, so it is sharded at the median estimate (`derive-ci-suites.ps1:278`) because it is unmeasured: measure it). Items 1 and 6 were closed by S8ca and S8by | `jobs/s8cg.md`; batch 7 note | |
| PRC-30 | S8ch | both items: the address of a global in a walked callee halts the path; `unsafeAddr` of a by-value array formal declines | `jobs/s8ch.md`; S8cc remainder | |
| PRC-31 | S8ci | all six items: a term order that earns its cost or none; `r4_strip` within 10% of S8bm; a behavioural pin for the order; ~~`configdefaults_depth` under 60 s without lowering the depth~~ (met by S8cm's split (`tests/tsymex_configdefaults_b.nim:21-23`, 53.6 s), not by lowering the depth); wide factoring decided again; the skip's real saving. Also batch 9's addition: `ti_tuple`'s SAT search 79.8M to 411.8M units on 4.13.4, so `tupleBudget` 300M to 600M | `jobs/s8ci.md`; S8by remainder | |
| PRC-32 | S8cj item 1 | a fresh thread's spend on a query follows what earlier threads ran (72,124 to 5,854,994 units on Z3 5.1). **Mechanism found (S8cj, 2026-11-07):** the input is Z3's process-wide allocation count (`Z3_get_estimated_alloc_size`), read by the default solver's tactic strategy as the `memory` probe: the QF_NIA portfolio's `cofactor_term_ite` preamble step runs only under 20 MB and its `nla2bv` + SAT stage only under 100 MB (`qfnia_tactic.cpp`), above which the smt core searches instead (72,053 → 876,223 in Z3's term order, 72,124 → 5,854,994 in the own-context order; 26,622 → 23,883 and 26,693 → 911,591 on 4.13.4). Deterministic and reversible (freeing the contexts restores the figures); not threads, addresses, malloc arenas or mmap thresholds. What grew the count was each exited thread's last `newContext()` left in nim-z3's current-context threadvar (17 MB per thread), and in a run `resetSymexRunState` leaving the walk context current after the run: fixed in `runSymex` / `runConcolicCollectImpl` (restore the previous current context), pinned by `tsymex_0016_s8cj_runctx`. The "function of the query alone" claims (S8bm, S8bp, `queryTermOrder`, `ownContextSolver`, `concreteScratchCheck`, the `s8by_remainder` header) now read "the query and the process's Z3 memory". Design alternative not taken: an explicit-tactic solver (`smt` / `Z3_mk_simple_solver`) would make spend memory-independent at the price of the portfolio's bit-blasting stage (72k against 876k-5.85M on factoring) and a walker version bump. The portfolio also has wall-clock `try_for` stages (2 s, 3 s), a third process-external axis on budget precision. | `docs/rfc/0016-research/S8cj.md` ("The mechanism", "Conclusions"); `s8cj/hist-*.log` | precision only: every outcome was `zsSat` in every regime |
| PRC-33 | S8co | items 3 (auto-possession with a property or XCLASS), 4 (kept `ignore_skip_arg` under a limit), 5 (`detect_repeat` group repeats on the JIT, 400 calls skipped), 6 (SKIP:NAME past 100, languages past 7), 7 (symbolic `(*ANY)` under the JIT scan, 72+ differences when lifted), 9 (`replace`'s unmarked SKIP:NAME, `first` in UTF, `count` of `set[char]` and overlapping counts), 10 (unbounded no-match refutation past `limitReach`'s safe length, with PRC-24). Items 1, 2 and 8 are in §5.7 Includes PRC-24 (item 10) and PND-02's remainder (a differential-only leg for older PCRE). | `jobs/s8co.md`; S8cf remainder | |
| PRC-34 | S8cp item 7 | declined shapes: whole-tuple `==` (`eqBV`); a local `let b = addr o.y` alias on whole assignment; a type section in a routine body (with PRC-22); a parameter pragma `x {.inject.}: int`, a compile error in `collectStringBackedByteSeqParamsImpl`, to fix first; nested `addr t[1][0]`. `s[1].b = 7` and `s[1][0] = x` only if S8bz left them declined Includes PRC-22; add whole-seq `==` (`runtime.nim:8341`, not re-verified). | `jobs/s8cp.md`; S8cb remainder | |
| PRC-35 | S8cp item 8 | declined magics: `math.toInt`, a holey enum's invalid value, `=dup` of an object or tuple through its hook, `$float`, the remaining `repr` shapes; stop only where the theory cannot express it or the cost is measured out of budget, with the number Add `$bool` (`dsl_parser.nim:11205,11831`, not re-verified). | `jobs/s8cp.md`; S8cb item 5 remainder | |
| PRC-39 | W1-b | an exact local `{.cursor.}` model: a cursor local is a non-owning alias of its source's storage (no copy, no destroy), so `var c {.cursor.} = gs; gs[0] = 9` reads 9 through `c`; replaces `feLocalPragma` for `cursor` only, other non-allowlisted local pragmas keep the decline; native pins on c and cpp | W1-b's designed decline; three-way row in the handoff (2026-11-07, W1-z) | renumbered from PRC-36 (duplicate id), K1a-ids |
| PRC-40 | W1-e | an exact float width model: `float32(x)` rounds to binary32 (Z3 `fp.to_fp` at 8/24, round-nearest-even) and widening back is exact, so `float64(float32(x)) == x` gets a model rather than `feFloatWidth`; native pins at 0.5 (hit) and 0.1 (no hit) on every build row | W1-e's designed decline; three-way row in the handoff (2026-11-07, W1-z) | renumbered from PRC-37 (duplicate id), K1a-ids |
| PRC-38 | CR-A | an exact generic exception model: identify `G[ValueError]` by its full instantiation, with ancestry from `G`'s declared base, so `except G[ValueError]` and `except CatchableError` decide rather than decline with `eeUnknownExnType`; native pins for both | CR-A's designed decline (0.9.2 review SC2, 2026-11-07) | |

<!-- worklist:end 5.2m -->

### §5.3 Crashes, compile stops and hangs

<!-- worklist:begin 5.3 -->
| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| CRH-01 | Compile stops in `classifyType`: `splitLines` (INT-09) and the generic-param `.len/.add` stop (HRV-44, zero corpus coverage) | sort S13 | the `sort` stop this row first named is gone at 83c1d304: `s.sort()` and `s.sort(system.cmp[int], Descending)` compile and decline (C-06), now precision row W-36. K2c re-probe (2026-11-09): HRV-44 is gone at head (generic procs using `.len`/`.add`/index on their generic param run and are `sxSat`, pinned). The `splitLines` stop was `classifyType` on an inline-iterator formal declared by its default alone (`keepEol = false`, empty type slot); fixed (type read from the iterator's signature), and over a bounded string it declines `seUnsupportedStringOp`, pinned. OPEN RESIDUE: `for l in s.splitLines` over an UNBOUNDED symbolic string does not terminate under `symexFind` (killed at 600 s; was a compile stop), a loop-cap defect, K7 (typed halt for every cap), not `classifyType`. Also fixed and pinned: `openArray` parameter (replay splat bound a `var` of it), object with a `pointer` or `UncheckedArray` field. One `classifyType` row; mechanism K2a/K2c. K2c (2026-11-09): a top-level `Atomic[T]` or `owned T` parameter was a further compile stop (`emitTyAndReader` raised on the `__ownership:` placeholder); it now declines `heUnsupportedOwnership`, pinned in `tests/tsymex_0016_k2c_typeclass.nim`. | |
| CRH-02 | Compile stop on `create` and `GC_ref` | sort S12 | `s8cl_lifetime_b.nim:193-201`; models remain PRC-18/PRC-20. | closed |
| CRH-03 | A ref-local merge runs out of memory and is killed Includes INT-02's figures (8.36 GB under an 8 GB limit, killed at 124-135 s, same on `main`); no `iteDeep` pin in `tests/`; borders RFC-0017 P1 (path merging), which does not cite it. | S8ct | an OOM kill that matches `main`; earlier measured as a 250 s merge, and a silent exit at 300 merges under audit. Bound it to a decline within budget; that bounded decline stays here as a `declined` cell, and only the merge itself moves to RFC-0017 (MOV-01) | |
| CRH-04 | A regex literal of 2600 nested groups | S8ct | fixed in 0.9.1 (review R1-22; `c9682ebc`, `9663105d`): `tests/tsymex_rfc0005_r1_pcrelimits.nim`. Includes INT-03. | closed |
| CRH-05 | ~~A pointer plus 11 Table inserts ran past 1400 s~~ merged into PRC-05 | S8cn | liveness; the pin uses one insert | merged |
| CRH-06 | `zeroMem` and `copyMem` on `addr x`: a walker fault (`FieldDefect` reading `ptrPointeeTy` of an `itUninterp`). First make it a named decline, then model it | S8cl remainder; ex-PRC-16 | the only `zeroMem`/`copyMem` pins are the opaque-global form (`tests/tsymex_rfc0005_s8cs_routes2.nim:125,131,363`); the `zeroMem(addr x)` fault has no test. First a named decline, then back to §5.2 as precision. **K2-0 probe (2026-11-08): reproduces.** `zeroMem(addr x, sizeof(x))` and `copyMem(addr y, addr x, sizeof(int))` on a local int both end `sxUnknown` with `weInternalWalkerFault: FieldDefect ... 'ptrPointeeTy' ... kind = itUninterp` (a fault, not a named decline); native reaches the label. Pinned: `tests/tsymex_0016_k20_probes.nim`. | |
| CRH-07 | **Latent crash:** a `v == f` Int definition in `regexRecDefConds` segfaults at `byteLeafIds` `dec_ref` | sort U4; S8co item 1; S8cf remainder | avoided, not fixed; no SUT at e497dcf reaches it; a wrong refcount can hide a use-after-free | the walker-under-sanitizers job, §11 |
| CRH-08 | The `cmpIgnoreStyle` hang | PND-12; S8cu (resumed 2026-11-02) | no `main` column yet; S8cu is producing the three-way table. **K2-0 probe (2026-11-08): reproduces.** `if cmpIgnoreStyle(a, "abc") == 0` over a string parameter: `symexFind` is still running after 25 s in a child process (the marker file shows it entered the walk; a control walk finishes in under a second). Native terminates. Pinned in `tests/tsymex_0016_k20_probes_child.nim` (child re-execution with its own budget). | |
| CRH-09 | Harvested crash and hang items with no SUT yet: N35 OOM, `cast[int32]` fault, PCRE interpreter SIGSEGV, `$simplify` hang sites, cumulative Z3 MEMOUT, `mkIntLit(0)` placeholder (HRV-06, HRV-43, HRV-45 to HRV-51); bitwise `not` on a Z3 Int (W-25); `<` on `ptr` reaching `cmpBV` (W-28) | research round, `docs/rfc/0016-research/MERGED-worklist.md` W-25, W-28, W-29 | read only: probe each, then a named decline or a fix **K2-0 probe (2026-11-08), one result per item** (`tests/tsymex_0016_k20_probes.nim` unless noted). N35 (HRV-43): `while chk(i) and i < 10` with a `while`+`continue` callee, both operand orders, does not reproduce: `sxSat` with a `beBudgetExhausted` taint, no OOM, no fault. `cast[int32]` over a helper (HRV-45): does not reproduce; a named `feUnsupportedExprKind` (`nnkCast`) decline. Bitwise `not` (W-25): does not reproduce; `(not k) + 1 == 5` agrees with native (`pinExact`). `<` on `ptr` (W-28): does not reproduce; named `feUnsupportedOp` decline (`ref/ptr comparison op bLt`). `{'0'..'9'}` `in`/`contains` (HRV-47) and `array[Enum, T]` indexing (HRV-49): both agree with native. Cumulative Z3 MEMOUT (HRV-51): 30 sequential `symexFind` calls in one binary, all `sxSat`, no MEMOUT. `mkIntLit(0)` placeholder (HRV-06): never a bare verdict; the Table and HashSet omitted-field cases decline `feUnsupportedOpHavoc`, the array, distinct and tuple cases agree with native (`tests/tsymex_0016_k20_probes_child.nim`). PCRE interpreter SIGSEGV (HRV-46): reproduces natively on Linux at 100000 subject bytes (`pinCrash`, `ceSegv`; 10000 bytes do not crash, so 8000 is a Windows PCRE 8.45 figure); no walker verdict is involved. `$simplify` literal-test hang sites (HRV-50): not probed with a SUT; the one big-term probe (1500 straight-line additions) is slow in the walk but is a cost curve (see PND-13), not a located `$simplify` print. Remaining open from this row: HRV-46's native crash (needs a decline or a documented `never`) and HRV-50 (needs a site-level probe). | |

<!-- worklist:end 5.3 -->

The two latent crashes that sat in §5.7 are settled: the `byteLeafIds`
segfault (PND-04) moved to CRH-07, and probe p7's rc=139 (PND-05) is closed,
superseded by INT-18.

### §5.4 CI and test time

<!-- worklist:begin 5.4 -->
| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| CI-01 | S8cm: corpus files over 60 s of compile plus run on Windows, and shard budgets (no shard's typical time above 30 of 40 minutes). **S8cm is running and may finish before the tag**; if it lands on RFC-0005, it keeps its row there and this item tracks only what it leaves (the files listed after it started: `b10_integration` 107 s, `s8cd_setorder_large` 102 s, `_small` 100 s, `s8cn_views_c` 121 s, `s8bq_remainder` 91.4 s, `s8cr_intro` 60.2 s, `s8cd_globals`) | `jobs/s8cm.md`; ledger entries for batches 9-10, S8cd, S8cn, S8cr | S8cm done (`9ebe2a46`; shard target 23 min, `d7948de5`). `scripts/ci-suite-seconds.tsv` lists 30 suites over 60 s, longest `s8ab_letaudit` 127.4 s. Includes INT-17 and INT-08. | |
| CI-02 | A permanent cpp CI leg. No leg runs cpp today; n42 and n43 broke on cpp for several batches unnoticed (sort B21). Also run Z3 4.13.4 on a schedule: until now batch gates were c on Z3 5.1 only, and full 4.13.4 and cpp sweeps run only at the release gate | S8cl item 5; sort B21; ledger (release gate) | `.github/workflows/` = `fuzzer-mingw`, `fuzzer-msvc`, `symex-mingw`, `tianguis-publish`; no Linux leg, no cpp, no `schedule:`. Z3 4.13.4 already runs on every push on all three Windows legs, so the 'run 4.13.4 on a schedule' half is struck; what remains is CI-A (Linux c, every push) and CI-B (cpp and 4.13.4 on Linux), §11. | |
| CI-03 | `s8by_remainder`'s units check is not deterministic under load | S8ct | **Cause (S8cj):** the test's own threads each leaked a 17 MB Z3 context (nim-z3's current-context threadvar, never destroyed with the thread), so the process crossed Z3's 100 MB strategy threshold between `base` and the compared runs (PRC-32); under a sweep's load other processes do not matter (the count is per process), but a cpp build crossed the line at a different thread. Fixed: the threads release their contexts (`setCurrentContext(nil)`), so `tests/tsymex_rfc0005_s8by_remainder.nim:189`'s `check r.units == base.units` compares two threads at one count, which the probes show exact (mode 15r: six threads, one figure). Header corrected. Includes INT-04; owner S8cj. \| `docs/rfc/0016-research/S8cj.md` conclusion 4; `s8cj/hist-c-z3-5.1.log` mode 15r | closed: test-harness; fixed |

<!-- worklist:end 5.4 -->

### §5.5 Infrastructure

<!-- worklist:begin 5.5 -->
| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| INF-01 | The differential fuzzing harness (§4), slice D1 | coordinator ledger, S8cq blocker (2026-11-02) | every sort blocker was found by hand | |
| INF-02 | Fork (c): a gated clean replay as a safety net, which would catch a false `sxSat` on a clean path. **Decided 2026-11-06: not added** (item `fork-c-clean-replay`, decision D-0016-2); native pins and D1 carry it | RFC-0005 "the open fork (c) below" (line 1667 at 67f0b622; the DoD audit cited it at 1615); DoD audit fork 2 | the fork was never written down in RFC-0005; this is its first record | closed by D-0016-2 (record) |
| INF-03 | The findings ledger and a weekly rate report (§3.2) | this RFC | The ledger exists (handoff F-0001 onward). The weekly rate report is dropped: D-0016-1 closes on the work list, not a rate. | closed |
| INF-04 | S8ck after item 1 (slice S8ck-r): items 2 (`Z3FuncDeclOwn`, `Z3FuncInterpOwn`, `Z3RcfNum` hooks never release `ctx`), 3 (`Z3Ast[S: static]` hooks unused for `Z3Int`/`Z3Bool`), 4's version half (`tffi`, `tversion`, `tmultiversion` assert a 4.x runtime), 5 (`injectShapeFault` comment), 6's first half (ADR-0023's "a lowering-time degrade must never raise", keep or simplify), 7 (`s8s_precision` run wall 13.2 to 19.1 s on Windows), 8 (`examples/properties.nim:30`, examples in nim-z3 CI on c and cpp), 9 (a leak gate that fails on invalid reads, writes and frees, shown RED on a planted bad `dec_ref`), 10 (record and reduce the spacer read; do not file), 11 (generated seq hooks on the raise path release every element), 12 (separate real leaks from live globals, `trcf`'s 26 `Z3ContextOwn` blocks). Item 4's hang half and item 6's second half are in §5.7 | `jobs/s8ck.md`; `worker-reports/s8ck-item1.md` | item 1 closed: cc5ffc9 identical to ae509f0 on invalid accesses and leaks | |
| INF-05 | Audit the older "Different mechanisms, reported and not fixed here" lists against the remainder chain. This document took the lists of slices landed through batch 10 whose remainder has no later slice (S8ca, S8by, S8cc, S8cf, S8cb, S8cd, S8cl, S8cn) item by item. The earlier lists were each carried into a remainder slice whose job said "defer nothing", but no one has checked that every item reached one | RFC-0005, about 80 such lists | **done 2026-11-03** (owner audit of the lists of 72 slices, S8c, S8e/S9 and S8g through S8bt, plus the inline not-fixed notes in S8y, S8ah, S8ao and S8bk): 318 rows fixed, 17 owned by RFC-0005, 9 already owned here. The 13 unowned rows (11 distinct items) are filed in §5.8 as AUD-01 to AUD-11 | closed |

<!-- worklist:end 5.5 -->

### §5.6 Upstream reports

Outward-facing. Decided 2026-11-06 (item `upstream-reports`, decision
D-0016-3): file UPS-01 and UPS-03, which have reductions; hold UPS-02 until
S8cj reduces it. None is filed yet.

<!-- worklist:begin 5.6 -->
| ID | Report | Source | Evidence | Owner |
|---|---|---|---|---|
| UPS-01 | Nim: a raise-path destroy (a destructor swallowing an in-flight exception on the C backend) | S8ce | reduction at worker `s8ce-work/probe/purenim.nim`, condensed in `worker-reports/s8ce.md` | closed: filed 2026-11-07: https://github.com/nim-lang/Nim/issues/26661 (body from `docs/rfc/0016-research/UPS-01.md`) |
| UPS-02 | Z3 5.1: `Failed to verify: m_cache.mk_unique(p) == p` on wide factoring | S8by remainder; S8cj item 2 | **Reduced (S8cj) to three assertions** `(> p 1) (> q 1) (= (* p q) 16777207)`: on 5.1.0.0 the VERIFY fails in `nlsat::solver::imp::reinit_cache` (from `reorder`) and the check returns `unknown` (`canceled` at any rlimit 5M-50M; `unreachable` under `arith.nl.order = false` or `random_seed = 1`, the not-canceled path) for a composite, a prime and with `p, q < 200000`; 4.13.4 answers `sat` in 2,175,259 units with no message (decision regression). No `arith.nl.*` or global `nlsat.*` setting avoids it; dropping the lower bounds does. c and cpp agree. Draft report `docs/rfc/0016-research/UPS-02.md` (nightly and the `z3` binary still to run). Includes PND-10. \| `docs/rfc/0016-research/UPS-02.md`; `s8cj/ups02b-*.log` | held (D-0016-3); ready to file once the nightly is run |
| UPS-03 | Z3: invalid read in `spacer::pob_queue::reset()` | S8ck item 1, item 10 | fixedpoint only, unreachable from nelli; S8ck item 10 reduces it | closed: filed 2026-11-07: https://github.com/Z3Prover/z3/issues/11601 (4-line input and C driver in `docs/rfc/0016-research/`; reproduces on 4.13.4, 5.1.0.0 and the 2026-11-07 master nightly) |

<!-- worklist:end 5.6 -->

### §5.7 Pending classification

These could not be classified as tag blockers or not. The sort's UNVERIFIABLE
rows (U1–U8) are awaiting disposition before the tag and are **not moved**;
they are listed so nothing is lost. Each moves into §5.1–§5.4 once its
disposition shows it is not worse than `main`, or stays with RFC-0005 if it is.

<!-- worklist:begin 5.7 -->
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
| PND-10 | ~~Whether a verdict reached after Z3's `mk_unique` check can be trusted~~ merged into UPS-02 | S8cj item 2 | **Answered (S8cj):** there is no verdict after the message. The failed VERIFY throws; the check returns `unknown` either as `canceled` (limit cut first) or `unreachable` (exception first), never `sat`/`unsat`, so nelli declines (`sxUnknown`). Pinned natively by `tests/tsymex_0016_s8cj_mkunique.nim` through `symexFind` on `p > 1 and q > 1 and p * q == 16777207` with fd 2 captured: never `sxUnsat`; `sxUnknown` whenever the message was printed; a `sxSat` (4.13.4) carries a natively checked witness. \| `docs/rfc/0016-research/S8cj.md` item 2; `docs/rfc/0016-research/UPS-02.md` | merged; test added |
| PND-11 | S8cu's known limits (moved to SND-13) | S8cu | if the scan misses a check-off region, the walker assumes checks are on, which is the false `sxRaised` S8cu fixed; `main` faulted on these routines, so a miss may be worse than `main` | moved |
| PND-12 | S8cu's resumed rows: ~~`push assertions:off`, a global initialiser under a push, a nil deref with SIGSEGV against a caught `NilAccessDefect`, the cross-module rows~~ dropped round 2; the `cmpIgnoreStyle` hang moved to CRH-08 | S8cu (resumed 2026-11-02) | S8cu is producing the three-way table | moved |
| PND-13 | Z3's own internal recursion depth, not audited when S8ct bounded the walker's term walks | S8ct (B19 disposition) | to be checked at disposition. **K2-0 probe (2026-11-08): not reachable from a SUT.** A straight-line SUT of 3000 additions stops the compile in the parser (the VM iteration cap in `parseDeferList`), far below Z3's own recursion depth; 1500 additions then an equality do not finish in 25 s, but 40 finish in about a second, so the cost is superlinear in the walk, not a Z3 stack. Probe and a `skipCell` record: `tests/tsymex_0016_k20_probes_child.nim` (`PND-13`). | never: unreachable from a SUT (K2-0) |

<!-- worklist:end 5.7 -->

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

<!-- worklist:begin 5.8a -->
| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-01 | ~~Windows re-exec replay marshalling~~ merged into PRC-01 | S8ct, "For RFC-0016" 1 | precision | merged |
| INT-02 | ~~The ref-merge walk peaks at 8.36 GB~~ merged into CRH-03 | S8ct, "For RFC-0016" 2 | crash, same as `main` | merged |
| INT-03 | ~~A regex literal of about 2600 groups~~ merged into CRH-04 (closed) | S8ct, "For RFC-0016" 3 | crash | merged |
| INT-04 | ~~`s8by` units check not deterministic under load~~ merged into CI-03 | S8ct, "For RFC-0016" 4 | test-harness. S8cj: the cpp gate's flakiness was the same mechanism (process memory crossing Z3's 100 MB strategy threshold between the compared threads), fixed with CI-03. | merged |
| INT-05 | An object field of a two-alias type stops the compile (`expected 'O = Alias'`), at `main` and on the channel; pinned "declines as main does" in `tsymex_rfc0005_s8ct_deepterm` Evidence: builds and declines as `main` does (`feUnsupportedParamType`), `tests/tsymex_rfc0005_s8ct_deepterm.nim:105-111`; not a compile stop. | S8ct, "For RFC-0016" 5 | precision | |
| INT-06 | The array-width decline (`termWalkMaxDepth`) catches an `int` index the path confines (`a[n and 7]`): the count reads the index's type, not the path | S8ct, "For RFC-0016" 6 | precision | |
| INT-07 | On Z3 4.13.4, a nim-z3 context made after one holding 80,000 `or` terms was destroyed builds terms about 800 times slower (20,000 `or`s: 0.14 s, then 119 s); a `symexFind` in between restores it. Not chased | S8ct, "For RFC-0016" 8 | performance | |
| INT-08 | `tsymex_rfc0005_s8ct_deepterm`'s teardown takes 78 s on Windows Evidence: S8cm split; `s8ct_deepterm` 43.6 s, `_b` 50.4 s | S8ct (coordinator, release intake) | test-harness | closed |
| INT-09 | ~~`splitLines` compile stop~~ merged into CRH-01 | S8ct, "For RFC-0016" 7 | crash (compile stop), same as `main` | merged |
| INT-10 | ~~Seven pins moved to `feGlobalRouteUnproved`~~ merged into PRC-04 | S8cs, "Precision cost" and "For RFC-0016" | precision | merged |
| INT-11 | The `trace1` row of `tsymex_rfc0005_s8cs_routes` (a `=trace` hook only the cycle collector runs) is a walker fault, `coerceIntLit` on an `svPtr`; `main` stops the compile on it Add a walker pin expecting a named decline on `trace1` (today Nim-only, `s8cs_routes.nim:195-199`), then fix `coerceIntLit`. | S8cs (coordinator, release intake) | crash (walker fault) **K2-0 probe (2026-11-08): reproduces on this head.** `trace1` (a `=trace` hook only the cycle collector runs) ends `sxUnknown` with `weInternalWalkerFault: ValueError: coerceIntLit: composite prototype for integer literal kind=svPtr`; native reaches the label. A dynamic-subtype `=destroy` (W-19b) is the same fault. Pinned: `tests/tsymex_0016_k20_probes.nim`. | |
| INT-12 | Under `--exceptions:setjmp` on Windows, the walker crashes entering its 16 MB fiber (SIGSEGV in `runSymexCaught`, before any walk). The same fiber and the same crash as `main`; the setjmp suite pins the default crash on Windows and cpp | S8cu, "Windows" | crash, same as `main` **K2-0 (2026-11-08): not probed, Windows only.** The crash is in the 16 MB fiber under setjmp on Windows; this build is Linux. `skipCell` in `tests/tsymex_0016_k20_probes.nim`; the Linux c arm of `tsymex_rfc0005_s8cu_nil_setjmp` is green and carries the Windows pin. | |
| INT-13 | ~~Re-executed replay declines on a host runtime hook~~ merged into PRC-02 | batch 11 (`7b2ab1e5`, `tsymex_rfc0005_b11_hoststate`) | precision | merged |
| INT-14 | ~~Re-exec footprint reads type symbols~~ merged into PRC-01 | batch 11 (`7b2ab1e5`) | precision | merged |
| INT-15 | `setControlCHook` is not among the runtime hooks `hostRuntimeHook` checks, so a re-executed replay does not decline when the host set one, and the child runs without it. Not classified: needs a three-way row | batch 11 (`replayproc.nim`) | unclassified (§5.7 rule) **K2-0 (2026-11-08): Linux half probed by reading, Windows half not runnable.** A fork replay copies the host's hooks, so there is no divergence on Linux or macOS; the re-exec replay is Windows-only. `hostRuntimeHook` (`replayproc.nim`) checks six hooks and not `setControlCHook`. `skipCell` in `tests/tsymex_0016_k20_probes.nim`. Classification: a Windows-only replay-fidelity gap; its three-way row needs a Windows leg. | |
| INT-16 | The 0.9.0 migration note's counts recounted against v0.8.0 (37 new `SymexErrorKind` members, the ordinal table). **Done** in batch 11 (`8f00b736`); recorded so the item is not reopened Closed (`8f00b736`). | batch 11 | test-harness (docs) | closed |
| INT-17 | ~~30 corpus suites over 60 s~~ merged into CI-01 | S8cm (done; `9ebe2a46`) | test-harness | merged |
| INT-18 | Probe p7 (sort N3) now declines (sxUnknown) where `main` decides correctly (sxSat; native hits at k=3). A precision loss on this SUT, not a soundness one. Its old rc=139 did not recur in 450 runs per tree (c, cpp, ASan) | pre-tag probes on `8177eb27` | precision | |
| INT-19 | PCRE 8.37 built without JIT, which is on the verified-library list, was not run. U1 and U2 were verified on 8.37 JIT, 8.39 JIT and 8.44 JIT: the candidate declines where `main` gives a false pair | pre-tag probes (U2) | test-harness | |
| INT-20 | U5's original SUT (October false sxUnsat) lives only on the offline worker. S8cl's reconstruction (`unsafeNew(p, 8); if p != nil`) is correct on the candidate. Recover the original, and pin it, when the worker returns Evidence: `origin/worker-sls2` is fetched (88 report files) but the U5 SUT is not among them; S8cl's reconstruction is pinned at `s8cl_magics.nim:61-72`. Recover from the host or declare the reconstruction the pin and close. Includes PND-06. | pre-tag probes (U5) | test-harness | |
| INT-21 | The check-off probe's `ai_caught` (`mitems` over `int16`, `assertions: off`) decides sxRaised. The raise looks real (int16 overflow at 32767 with overflow checks on), but no native run tried that input. Pin it natively | pre-tag probes (S8cp item) | test-harness | |

<!-- worklist:end 5.8a -->

**From the 0.9.1 wiring audit (2026-11-03).** What RFC-0005's post-tag
wiring audit (WA-1 to WA-13) and its fix slices W1 to W3 left open. Measured
against 0.8.0, as the audit was; none is worse than it.

<!-- worklist:begin 5.8b -->
| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-22 | A clean, faithful winner is never replayed, so nothing learns that its witness ends the process after the target. `assertCoveredBy` still splats it and `symexForAll` still seeds it, in the host (`symex.nim:4057-4061`, `:982`). Unchanged from 0.8.0; WA-2 closed only the replayed case (`witnessUnsafe`) | 0.9.1 wiring audit | crash, same as 0.8.0 **K2-0 probe (2026-11-08): reproduces.** `proc quitAfter(k) = if k == 5: symexTarget("hit"); quit(0)`: the verdict is a clean `sxSat` with no errors; `assertCoveredBy(quitAfter, tLabel("hit"))` then ends the host process (rc 0, nothing after the call runs). Pinned in a child process: `tests/tsymex_0016_k20_probes_child.nim`. | |
| INT-23 | A replay that ends at a memory limit is run-dependent only when the child's `outOfMemHook` reports it (`replayproc.nim:423-424`, `:1272-1273`). Under `-d:useMalloc` the hook is not reached, and a kernel OOM kill is a `reSignalled` SIGKILL, so either is cached as a permanent `:unk` | 0.9.1 wiring audit | precision | |
| INT-24 | The run-dependence flag is a threadvar reset by each entry macro's settle (`replayproc.nim:90`; read at `symex.nim:646`). A user-level `saveSymexVerdict` of an `sfUnknown` right after a settle that set it skips its save too Evidence: `d8969822`; no `threadvar` in `replayproc.nim`/`replayresult.nim` | 0.9.1 wiring audit | performance | closed |
| INT-25 | Hypothesis: on macOS a kill at `replayTimeoutMs` does not reach the SUT's own child processes, and the child does not die with the host. `setpgid` and `PR_SET_PDEATHSIG` are Linux-only (`replayproc.nim:393`, `:471`, `:1095`, `:1105`). There is no macOS CI to probe it Includes HRV-03: on macOS/musl `quit(n)` is reported as exit 0 in the hint (`replayproc.nim:100-108`). | 0.9.1 wiring audit | unclear (hypothesis; no macOS host) | |
| INT-26 | `RegexError` reaching `symexFindAllWitnesses` through the user exception hierarchy (WA-1, `symex.nim:4523`) is unpinned: W1 pinned a user exception type only. It needs a PCRE SUT | 0.9.1 wiring audit | test-harness | |
| INT-27 | Under `--panics:on` `replayInScope` declines every target (`replayInScope`, `symex.nim:2318`; the gate `:3169`), so every lossy clean winner is `rsUnconfirmed` (`settleWinner`, `:3387`) and none is `trusted()`. In W1-c2's scope (the panics profile, §11). | 0.9.1 wiring audit | precision | |

<!-- worklist:end 5.8b -->

**From the RFC-0005 code review (2026-11-04).** The Lows the review's ten
rounds reported and did not fix under the through-Medium mandate
(`docs/rfc/0005-review.md`; floor reached at round 10, `2e7a0bb6`). Each row
groups related Lows and names the ledger rows it carries. None is a
Critical/High/Medium finding. Standing against `main` was not measured at
intake, so each row still needs its three-way row (§5.7 rule) before work.

<!-- worklist:begin 5.8c -->
| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-28 | Replay child lifecycle and limits: SUT-started grandchildren survive when the child ends by itself; no memory cap on macOS/BSD and no CPU/FSIZE/NPROC limits or Windows `ActiveProcessLimit`; `pipe2`, the `PDEATHSIG` thread, `WaitForSingleObject` wrap, `resumeThread`, wire length overflow, "(deleted)" exe, non-atomic counter; ~~`waitpid(-1)` elsewhere~~ (only `waitpid(pid, …)` at `:480,1115,1140`) and no `setpgid` off Linux | 0005 review R1-24, R1-31, R1-32, R2-25, R2-27 | crash (hardening); not compared against `main` | moved: slice `rv0005-lows` |
| INT-29 | Replay child start-up robustness: a POSIX re-exec `execve` failure does `_exit(127)` and reads as a SUT crash; a child that cannot open its out file writes to nil and segfaults; the Windows private dir inherits the parent's ACL; the re-exec child inherits non-CLOEXEC fds; with fd 0-2 closed in the host the report fd is clobbered | 0005 review R2-21 to R2-24, R2-26 | crash (hardening); not compared against `main` | moved: slice `rv0005-lows` |
| INT-30 | The wire reader accepts a zero-size seq, amplifies allocation and does not bound recursion depth; unverified: the Windows fiber stack under refc | 0005 review R2-28, R2-29 | crash (hardening); the fiber half is unverified | moved: slice `rv0005-lows` |
| INT-31 | Cache-key coverage: `--opt`, `--cc`, `--cpu` and `--os` are not in the `\|bf=` segment; a `{.push.}` inside `fn` itself is invisible to it (covered by the `feCheckOption` decline, worth a test) Includes W-18: the `;impl=` digest holes (importc/dynlib bodies, override callees, proc-value targets, `lib/`; `docs/migration/0.9.1.md:264-273`). The `\|bf=` half is closed by K5a. | 0005 review R2-16, R2-20, R3-16 | soundness (key coverage); not compared against `main` | moved: slice `rv0005-lows` |
| INT-32 | Replay and settle policy: ~~stale "trusted by construction" comment, unenforced one-digit codec~~ (fixed: `3476f039`), `storedGaps` prefix, `reSignalled` not run-dependent, first-soundness-per-type, lossy sibling precision; `witnessUnsafe` not rendered, `spinJitter` costing up to about 100 syscalls per op, ~~the `ReplayOutcome` doc saying "three-valued"~~ (fixed: `3476f039`); an always-hanging witness is cacheable and pays `replayTimeoutMs` every run, and a loser's timeout blocks the winner; a statically refused replay stored `rsUnconfirmed` and runnable on a hit (documented policy, to be revisited) | 0005 review R1-33, R1-34, R4-07, R4-10 | performance and precision; no wrong verdict described | moved: slice `rv0005-lows` |
| INT-33 | Liveness on the fuzzer path: `ConcolicCollectResult.annotationViolations` has no reader; `saveSecondary` is unguarded, so the new `DbError` escapes `forAll`; the concolic flip solve lacks `maxSeqLen`/`seqQueryRLimit` and the theory facts `trySolve` adds Includes PRC-25. | 0005 review R1-25, R1-26, R1-27 | crash (R1-26) and precision (R1-27); not compared against `main` | moved: slice `rv0005-lows` |
| INT-34 | Design cleanups: `FindingHint`/`FindingGap` kinds are strings; include-split `runtime_*` modules and a `symex.nim` that mixes codegen, cache codecs and settle; the `engineSymexDbErrors` threadvar sink; `loweringPendingTaint` still a threadvar with `walk`/`walkCapSynced` as two shallow layers; the `sx2:` prefix is redundant with the walker version | 0005 review R1-28, R1-29, R2-10, R2-14, R4-08 | design debt; no wrong verdict described | moved: slice `rv0005-lows` |
| INT-35 | Exit-group guards: a compile-time `fields()` check that every group-typed field of `WalkCtx`/`LoopFrame`/`CallFrame`/`CallFrameCtx` is visited by `forEachExitGroup`; per-frame constructors so a group cannot be default-constructed unbound; `mitemsSince` yields `var T` so an entry's depth is mutable; `replayNotRun`'s hint check | 0005 review R5-08, R6-03, R6-04 | design debt; guards against a future soundness slip | moved: slice `rv0005-lows` |
| INT-36 | The finding collector's edges: `droppedSymexFindings` has no production consumer and is per-thread, so a worker thread's drops are invisible; `popEngineFrame` merges speculative nested runs and double-reports; a finding filed mid-statement is not stamped with later stray taint (pre-existing) | 0005 review R5-07, R6-08, R4-09, R3-17 | precision (R4-09, R5-07) and soundness (R3-17, not compared against `main`) | moved: slice `rv0005-lows` |
| INT-37 | Precision and unverified probes: `claimStrayPendingTaint` over-taints coalesced pending taint; a possessive quantifier on a non-group item may add 0 to the PCRE size bound (probe near 65536); `symBodyHash` on a bodiless routine (importc or forward declaration) may fail at compile time | 0005 review R2-08, R2-09, R6-09 | precision; two items unverified | moved: slice `rv0005-lows` |
| INT-38 | Cache hygiene: the notes record can be torn mid-save; old `:raised` indexes (before `:raised2`) are never cleaned up | 0005 review R6-07, R8-04 | performance; no wrong verdict | moved: slice `rv0005-lows` |
| INT-39 | Remove `SymexResult.fromCache`, which no code path sets (WA-11), in 0.10.0 with a migration note | item `fromcache-field`, decision D-0016-4 | `src/nelli/smt/types.nim`; the readable cache-hit flag is `SymexFinding.fromCache` | |
| INT-40 | A fork replay child inherits the host's current value of a routine `{.global.}`, so after earlier host calls a walker SAT through that global can be confirmed from run history; the verdict carries no `runDependence` (re-exec replay starts from the initial value and refutes) | 0.9.2 review SC1 (residual, predates Wave 1) | soundness: run-history dependence; unverified beyond code reading | |
| INT-41 | `symexFind`'s expansion calls `newLit(settings)` (`symex.nim:~3743`), which reads the deprecated `arithChecks` inside Nim's `macros.nim` and raises a Deprecated warning no call-site push can silence | 0.9.2 review (CR-B) | diagnostic | |
| INT-42 | The 0.9.2 code review's open Lows: R2-03 (`arithStamp` derives from the resolved push), R2-04 (one refusal-cause enum behind `hostRunnable` and `hostRefusalReason`), R2-05 (rename `effectiveArithChecks`), R2-06 (collapse `BuildRefusal.field`), R2-08 (zero-arg concolic entries), R2-10 (`k1lite.sh -b` validation), L9, SC3, D8 | `docs/rfc/0016-review.md` rounds 1-2 | design and test hygiene; no wrong verdict | |
| INT-43 | Z3 5.1.0's official Linux release archive (the `symex-linux` host leg) consumes about 1.66 times the rlimit units the podman image's Z3 5.1.0 does on the same queries (`tsymex_rfc0005_s8cn_step1d`: `rlimit=740770840` host, `446158528` podman, 74 queries both), so a budget-sensitive verdict flips: `grow_stale_dead` returns `sxUnknown` (`Z3: canceled` under `seqQueryRLimit = 20000000`) where podman returns `sxUnsat`. Known-red in `tests/0016-allowlist/linux-host-known-red.txt` until the budget is set from a unit that does not depend on the Z3 build, or the leg uses the image's Z3. S8cj: the Z3 build is one of three process-external inputs to a unit count; the others are the process's Z3 memory (the default solver's strategy reads it at 20 / 100 / 300 MB thresholds, PRC-32) and wall clock (the strategies' `try_for` stages), so a budget-sensitive verdict can also flip between a small test process and a real run, or on a slow host. Not re-measured here; the 1.66x remains unexplained by S8cj's mechanism unless the host leg's process sits in another memory regime (the probe is `Z3_get_estimated_alloc_size` at the query). | CI-A3 baseline, run 42434778262; `docs/rfc/0016-research/S8cj.md` conclusion 5 | precision (host-specific; the verdict is sound) | |
| INT-44 | On the cpp backend `tsymex_rfc0005_s8by_remainder`'s "what the context holds moves neither a scratch solve's spend nor its outcome" fails `r.units == base.units` (`holds 1`: 13236530 against 19018808, `holds 3`: 5854996; the `holds 0` baseline spends 19018808, and the outcomes and `infeasibleUnits` agree). The c backend passes it on Z3 5.1.0 and 4.13.4 and the podman cpp row passed at 0.9.1, so the unit count of a scratch solve depends on the compiled backend or the host's Z3 build; the verdicts are unaffected. Known-red in `tests/0016-allowlist/nightly-cpp-known-red.txt` until the pin compares an outcome rather than an exact unit count on the leg | CI-B first nightly, run 42440545873 | precision (cpp host; the verdict is sound) | closed Passed on cpp in `symex-nightly` run 42487154319 (rebased CI-B tree); the cause was the S8cj Z3-context leak in the test threads (INT-04), fixed on main |
| INT-45 | The first `symex-msvc` (c, vcc, Z3 4.13.4) nightly run found MSVC-only reds that `symex-mingw` cannot see: `tsymex_rfc0005_s6a_budget` (cl.exe C2124, a constant division by zero in the generated C), `tsymex_rfc0005_s8cs_routes2` (the test's `asm "nop"` is not accepted on x64, C4235), `tsymex_0016_k5a_fwrapv` (the build is refused by design under vcc and the test has no vcc arm), and `tsymex_rfc0005_s8bz_overlap` (SIGSEGV in a `=dup` hook under `tVariant` during module-init IR construction). Fixed: the first three are test-side fixes in `13578374`; `s8bz_overlap` was a Nim 2.2.10 codegen defect (under vcc a `{.packed.}` case object's `#pragma pack(pop)` landed outside the union, so pack(1) leaked to every later struct in the module), fixed by toolchain patch 0007, a backport of nim-lang/Nim#24461, published in `2.2.10-windows-x64` on 2026-11-08 | CI-B first nightly, run 42446649374 | toolchain defect (vcc codegen) plus test portability | closed `fuzzer-msvc` run 42489572022 passed `s8bz_overlap` under vcc with patch 0007; the nightly msvc known-red list no longer carries any INT-45 entry |
| INT-46 | `tfuzzforkworker`'s "submit succeeds once this process is single-threaded again" raised `ForkUnsafeError` ("2 OS threads alive") on the 4-core host leg: the fork-safety guard counted threads that were already joined and exiting. Red once in four `symex-nightly` / `symex-linux` Linux runs (z3-4.13.4 leg of run 42458557944, shard 10). Fixed: the guard ignores threads that are already exiting (`4d343177`) | CI-B, run 42458557944 | flake (host timing); the guard it tests is sound | closed |
| INT-47 | New MSVC-only reds on `symex-msvc` (run 42487154319), none in the 0.9.1 era: `tsymex_0016_k8a_gen` and `tsymex_0016_k8a1_template_except_as` fail to build under vcc (`symex.nim(2828, 29) Error: node has no type`, via `pinExact` and `scanFootprint`); `tsymex_0016_k20_probes` HRV-46 sees the PCRE interpreter exit -1073741571 (stack overflow) where the pin expects `ceSegv`; `tsymex_0016_universe` exits 1 after 0.2 s at its K1a-ids RED self-tests (suspect a CRLF or path assumption in the id join). Fixed: `846d18e9` (the `scanFootprint` guard on the untyped except-as binding, Windows replay re-exec only), `ea0d8251` (`pinCrash` maps 0xC00000FD to `ceSegv`), `4f682783` (the W-19b per-platform expectation), `1758f2ad` (`.gitattributes` eol=lf); all four pass under vcc in `fuzzer-msvc` run 42502121504 | CI-B, run 42487154319 | unclassified until triaged (the build error may be a walker defect on Windows) | closed |

<!-- worklist:end 5.8c -->

**From the INF-05 owner audit (rows marked UNOWNED).** The rows the audit
marked OWNED-0016 were already in this document (PRC-31, PRC-32, INF-04,
PND-07, PND-08, UPS-01) and are not repeated.

<!-- worklist:begin 5.8d -->
| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| AUD-01 | `isLoose` leaves an `isIntOffset` parameter unstamped. By design (ADR-0001: `isLoose` is opt-in unsound and carries its banner on `main`); needs a "stays by design" record, not a slice | S8w | soundness, opt-in and documented; not worse than `main` | never: stays by design: `never(reason)` cell, written by K1a-test |
| AUD-02 | `acDivByZero` off with `acOverflow` on leaves the continuation unconstrained at a zero divisor. A nelli setting with no Nim counterpart (Nim's zero check rides on `overflowChecks`); a witness relying on it would trap on replay, which S8ct's child contains | S8aa | unclear (policy); not worse than `main` | |
| AUD-03 | No clean no-zero type remains for the free-`retSym` guard pins; they are now `sxUnknown` on a `HashSet[string]` arm field, so the guard's coverage is weaker. No verdict defect | S8z | test-harness | |
| AUD-04 | Macro-VM closure capture: a nested proc capturing a loop `var` kept one closure environment across iterations (seen as a duplicate case label). **Probed, no instance** at `main` 6cbfe8f and the channel at 67f0b622; the one known instance was fixed in S8z (`tagOrdOf` top-level). No other RFC-0016 item audits this class (AUD-06 and AUD-07 are the `let`/parameter alias guard's coverage) | S8z; coordinator probe, 2026-11-03 | unclear at audit; probed, no instance | closed |
| AUD-05 | Step 1c's equality classes are syntactic over the roots: an equality the query implies without stating it is not seen. Shown, not closed (`tsymex_rfc0005_s8aq_remainder` (4)); the uncapped steps still decide these queries | S8ai; S8aq item 4 | precision | |
| AUD-06 | The build-time VM-alias gate runs on one suite per CI leg, not the whole corpus (deliberate: about 15–18 s per compile). Carried unchanged through S8ak and S8al | S8ah, S8ak, S8al | test-harness | |
| AUD-07 | A generic never instantiated in the scope's compilation unit gives the VM-alias guard an un-instantiated `getImpl()` tree | S8al | test-harness | |
| AUD-08 | ~~Non-integer `HashSet` elements decline~~ merged into PRC-12 | S8am | precision | merged |
| AUD-09 | A `var` global initialised by a literal is not read at its initialiser: its entry value is fresh. A deliberate sound choice (S8as item 3) | S8as | precision | never: stays by design: `never(reason)` cell, written by K1a-test |
| AUD-10 | The nil-dereference check of a lazily read operand happened where the read moved (S8ax's `orderOperands`), not where Nim checks it. The S8ax probe turned this into two blockers, both fixed: S8cq makes argument reads follow the C backend's temporaries (`nimArgTemps`; `tests/tsymex_rfc0005_s8cq_argorder.nim`), and S8cu makes a nil dereference an uncatchable crash routed through frame exits (`tests/tsymex_rfc0005_s8cu_nil.nim`, `_nil_native`, `_nil_setjmp`) | S8ax; S8be item 7; S8cq; S8cu | soundness at audit; fixed | closed by S8cq and S8cu |
| AUD-11 | S8aw's `L`-against-`indexof` link now covers native terms only; the walker no longer emits `seq.last_indexof` or `str.indexof` for `rfind`/`find`. A coverage note, no wrong verdict or decline described | S8au | precision | never: stays by design: `never(reason)` cell, written by K1a-test |

<!-- worklist:end 5.8d -->

AUD-04 and AUD-10 were the two rows whose standing against `main` the audit
could not settle. Both are closed: AUD-04 by a probe at both shas that found
no instance, AUD-10 by S8cq and S8cu.

### §5.9 From the research round (2026-11-06)

The research list's rows that §5.0-§5.8 and §8's mechanisms do not already
carry. Ids are the research list's (`docs/rfc/0016-research/MERGED-worklist.md`,
which has the evidence); each needs its three-way row before work. One id per
row, so K1's scan sees each (§8.2). W-43 is K3's; W-19 is SND-14; W-19d and
W-30 were meta-rows applied in round 2; W-57 is §10's domain rule; W-59 is
CI-A2's derive mode; W-60 is CI-B's CI-C and CI-D. A `never` row's Home names
the slice that writes its cell; until the cell lands, the slice id is its
state (§8.2).

<!-- worklist:begin 5.9 -->
| ID | Item | Home | Owner |
|---|---|---|---|
| W-08 | `nodeWritesHeap` is a fail-open denylist | K6a | |
| W-09 | the hook copy-proof defaults to "copied" | K6b | |
| W-10 | `ptrUsesStayLocal`, `routeStoresThroughDeref`, `bindsViewWhole` share the denylist shape | K6c | |
| W-12 | object field defaults (with W-20) | W1-f (decline), K3b (exact) | (2026-11-07, W1-z): W1-f found the decline premise wrong; the walker already agreed with native in every shape (see the W1-f row) |
| W-14 | `int` hard-coded as BV64; i386 unread | K5b (32-bit refused) | |
| W-17 | `nimOldCaseObjects`/`strictCaseObjects` unread | K5a (`caseObjects` field) | |
| W-22 | `parseBool` with `len 4` hangs | K2-0 (with CRH-09) | K2-0 (2026-11-08) reproduces: the walk is still running after 25 s (child process, marker file shows it entered `symexFind`); pinned in `tests/tsymex_0016_k20_probes_child.nim` (CRH-08 hangs the same way). |
| W-23 | `--mm:refc` stops the compile | W1-c1b (refusal) | |
| W-24 | `filterIt` raises `weInternalWalkerFault` | K2-0 (with CRH-09) | closed (K2-0, 2026-11-08): `filterIt` no longer raises `weInternalWalkerFault`; it is a named `feUnsupportedExprKind` decline (`nnkCommand`), pinned in `tests/tsymex_0016_k20_probes.nim`. Precision stays W-36's neighbour. |
| W-27 | macro `error()` sites reachable from SUTs | K2a | |
| W-50 | the build profile keyed and read | W1-c1a, K5a | |
| W-51 | per-build memory pins | K5b | |
| W-52 | shifts and `sizeof` as host facts; symbolic `low(int) div -1` | `div -1`: W1-d1a; `sizeof`: a `never(nrPlatform)` cell, K5b | |
| W-53 | INT-31 widened to every build read | K5a | |
| W-55 | the native-pin helper copied per file | K9a, K9b | |
| W-61 | probe agreements with no pin | W1-p, K9d-0 | |
| W-15 | `isThreadvarSym`/`isImportedVar` read a `getImpl` failure as "no": fail closed | K2a | |
| W-19b | S8cs "not covered" store routes (threads, signals, dynamic-subtype hooks, ORC cycle collector); Windows re-exec unseen macro hooks; S8cu scan misses (`mitems` instantiated under a push elsewhere, never-popped push, importer outside the graph, nelli under a user push); opaque proc with `var T` params leaves the environment unmutated | K2-0 (probe each), then fix or a `never` record | K2-0 (2026-11-08), per item. Reproduces as walker faults (`sxUnknown`, never a wrong verdict): threads (`createThread`: `ptrPointeeTy`), dynamic-subtype `=destroy` hook and the ORC cycle collector (`coerceIntLit`, INT-11). Declines, no fault: signal handlers (`feOpaqueCallUnmodelled`), never-popped push (`feCheckOption`). Closed: opaque proc with a `var T` parameter (`feGlobalHavoc` havoc of the argument; no stale value is trusted); nelli under a user push (WA-A pins it as documented, no decline). Open: a macro-built push with a macro-built pop (SND-13, false `sxRaised`); `mitems` under a push elsewhere (INT-21 pins the in-module form only); importer outside the graph (no SUT shape found). Windows re-exec macro hooks: `skipCell`, no Windows host. Pins: `tests/tsymex_0016_k20_probes.nim`. |
| W-19c | closure unverified: S1b block/break binding, S7 `lowerInExpr` drains | K2-0 (probe), then fix | closed (K2-0, 2026-11-08): S1b nested block/break binding and for-loop labels, and S7 expression-position statement lists, `try` and argument-order drains, agree with native over their domains (`tests/tsymex_0016_k20_probes.nim`, `pinExact`). |
| W-34 | `$` of seq/array/tuple/object/set/cstring (C-05, PRC-35; needs PRC-07 for `addQuoted`) | Wave 4 | |
| W-35 | `==` on seq/array/tuple (C-08, PRC-34, HRV-53) | Wave 4 | |
| W-36 | formals typed by a default are unreadable: `sort`, `sorted`, `align`, `formatFloat`, `parseHex` (C-06; the `sort` compile stop of CRH-01 is gone at 83c1d304, and it now declines) | Wave 4 | |
| W-37 | `min`/`max(openArray)`, `low`/`high` on seq/array values (C-07, HRV-19) | Wave 4 | |
| W-38 | `&` with a char operand; `intToStr`; `s.add('c')` outside loops (C-04) | Wave 4 | |
| W-39 | `for i in a ..< s.len` with a non-symbol bound written in the body (A-04) | Wave 4 | |
| W-40 | iterator shapes: yield under case/for/try, `return` in an iterator, break/continue over a user iterator, closure iterators, tuple-yield of a var (A-11) | Wave 4 | |
| W-41 | `split` variants, `contains(set[char])`, `fmt`, `%`, `cmp(string)`, `count`, `binarySearch`, `mapIt`/`toSeq`, `parseFloat` (C-09, C-14) | Wave 4 | |
| W-42 | `string` element view beside the whole `vs(s[0], s)` (B-03) | Wave 4 | |
| W-44 | `Table[K, ref T]`/`seq[T]` values; Table non-string keys at zero-init (B-09, HRV-04) | Wave 4 | |
| W-45 | value-object slicing, `of` on values (natively `of` is true on a sliced value) (B-12) | Wave 4 | |
| W-46 | set by value; a set over 8 bytes passed by pointer untracked (B-10) | Wave 4 | |
| W-47 | stdlib generic objects (Option, OrderedTable, CountTable, Deque) decline by catch-all, not by allowlist (B-11, HRV-62) | K4c | |
| W-48 | harvested precision with no row (the HRV list in the research file) | Wave 4; many close on a probe | |
| W-49 | open PRC/INT/AUD rows after the reconciliation, evidence refreshed | Wave 4 | |
| W-62 | CI odds: mingw B5-4, the `fuzzer-msvc` pull-request trigger, R1-12/13 unpinned, `dt-bounded` orphans, witness folding across nim-z3; refc never tested is a `never` cell under D-0016-7 | CI-B, H1; the refc cell K5b | |
| W-63 | JIT PCRE suites `skip()` on every Linux build: a JIT build row | CI-B | closed: the Windows legs are the JIT rows (PRC-27); K2a's `skip(` census rechecks it. Evidence (CI-B, `symex-nightly` run 42458557944 at 46af70b2, leg `msvc`, pcre64.dll JIT): the nine suites that take the JIT branch ran and none skipped (`tsymex_rfc0005_s8bt_limit_langs_b` ok=2, `s8cf_jitlimit` ok=2, `s8cf_jitlimit_b` ok=1, `s8cf_jitutf` and `_b` to `_f` ok=2 each, skipped=0 and rc=0 on all nine; `jit-rows.txt` in the `nightly-msvc-merged` artifact; the gate step `W-63` fails the leg if any has ok=0 or a skip) |
| W-64 | 12 `SymexErrorKind`s with no producer, two produced only in dead arms (HRV-05) | K1 (error-kind coverage), K10d | |
| W-65 | stale "STUB/defer" comments and dead boundary arms; the `caseNarrow` duplicate; `dOpaque` stubs | H1 | |
| W-66 | close six GitHub issues for shipped work: #152 #153 #160 #161 #162 #163 | H1 | |
| W-67 | RFC-0002 listed but absent; issues #146/#148/#149/#150: commit or drop | H1 | |
| W-68 | stale docs: SYMEX_PLAN status, ADR "PROPOSED" for landed ADRs, 0.9.0 known-gap text, RFC-0001 "Complete", CLAUDE.md's active RFC, 0014/0015 gates citing a pre-0.9.0 baseline, `docs/symex/README.md`'s decline catalogue (W1-z rewrites it) | H1 | |
| W-69 | "not green on a good day" wording in CLAUDE.md and `sweep-diff.sh` | | never: repository wording, outside this RFC |
| MOV-01 | the moves to RFC-0017 (N20, OQ1, CRH-03's OOM, `maxLoopUnwind`, #138, caps): record each in RFC-0017 with its id, then close here | W1-z | closed: done (2026-11-07, W1-z): recorded in `docs/rfc/0017-symex-reach.md` §7 and cited from slices M1, L1, P1 and E1 |
| STY-01 | `return` in `finally` on a raised path: c re-raises, cpp returns (A-10) | K5b (`never` cell of the build axis) | |
| STY-02 | Table/HashSet iteration order, hash- and build-dependent (C-13) | K4c (`never` cell of the stdlib-body axis) | |
| STY-03 | pointer order `<` (C-10, W-28) | K10a-axis (`never` cell of the definedness axis) | |
| STY-04 | `owned T`, `Atomic[T]` (HRV-18) | K3a (`never` cell of the type × memory axis) | never: done (2026-11-08, K3a): `typeclass:owned` and `typeclass:atomic` are `never` rows of the type-class axis |
| STY-05 | `nextafter` (HRV-27) | K4a-table (`never` cell of the magic axis) | |
| STY-06 | concurrency inside the SUT, sNaN payloads, float80, full Unicode case fold, symbolic-length sort (HRV-105) | K3a, K2b, K4c (one `never` cell each) | K3a done (2026-11-08): sNaN payloads and float80 are `never` rows (`typeclass:float/sNaNPayload`, `typeclass:float128`); K2b and K4c own the rest. K2c (2026-11-09): `classifyType` reads the `float128` row, so a `c_longdouble` parameter declines `feUnsupportedParamType` (it was modelled as a double); the sNaN payload row waits on K4c's cast decision point |
| STY-07 | `addr s[0]` then growth (B §1.2) | K10a-axis (`never` cell of the definedness axis) | |
| STY-08 | Z3-version-dependent `deepUnsat` (HRV-63) | K5b (`never` cell of the build axis) | |
| STY-09 | the AUD-01, AUD-09 and AUD-11 records | K5b (AUD-01), K2a (AUD-09), K4c (AUD-11) | |

<!-- worklist:end 5.9 -->

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
- **Fuzzer, CI and consumer intake.** Each issue the nightly fuzzer job or a
  red CI-B run opens (labelled `rfc-0016-intake`, §10, §11), and each
  consumer report, becomes an `F-NNNN` row with its three-way probe within
  the week, and is named by a cell (§8.2). Each wave's integration slice
  (W2-z, W3-z, W4-z) checks that none is older than seven days.

## §7 — Open forks

None open. `/architect` rounds 1-3 (2026-11-06) resolved every point their
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

## §8 — Closure design (`/architect` rounds 1-3, 2026-11-06)

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

**The property this RFC lives on**, in one sentence: *every trusted definite
verdict a consumer can obtain through a public entry point (§10) has been
reproduced natively on that build row (§8.3), or its cell declines.* K9's pin
record is the evidence, K1's join is the check, and §12 item 1 is the
property measured. It first runs end-to-end in Wave 1, over the seven §5.0
cells (K1-0, §11).

Fixing the seven one at a time is the whack-a-mole RFC-0005 played. This
section replaces it with one mechanism that makes an unadmitted model
impossible to write silently, and a finish line (§12) that is a property of
that mechanism's output, not a count of rows.

### §8.1 Admission: per-axis verbs over private rows, default decline

`smt/admission.nim`, a Z3-free module above `types.nim` (its keys,
`IRTypeKind`, `MemOp`, `ArithOp`, `SymexErrorKind`, live there). Callers never
see a row; each axis exports a decision verb that returns the answer, and an
enumerator that K1 reads. Test and tracking metadata (which file pins a cell,
which RFC row it closes) never enters `src/`. One generic table type serves
every axis, so an axis is two declarations (its site enum and its rows) plus
its verb:

```nim
type
  Scope* = enum                         ## what a cell belongs to
    axConstruct, axTypeClass, axTypeOp, axPragma, axMagic, axStdlibBody,
    axBuild, axReadOnly, axDefinedness,             # admission axes
    faCallShape, faExnMemory, faGeneric             # test-side pin families
  Axis* = range[axConstruct .. axDefinedness]
  CellKey* = object                     ## identity: (scope, rendered key)
    scope*: Scope; key*: string         ## the only producer of `key` is the axis's `render`
  Admit*[P] = object                    ## a proof, constructible only in admission.nim
    ok: bool; payload: P; kind: SymexErrorKind; reason: string; cell: CellKey
  Intent* = enum iModel, iNever         ## ledger only: declined for now vs stays
  NeverReason* = enum nrTheory, nrBudget, nrPlatform, nrUnobservable, nrByDesign
  Row[S; P] = object
    case admitted: bool
    of true:  payload: P; builds: set[BuildRow]; sites: set[S]
    of false: kind: SymexErrorKind; reason: string
              intent: Intent; never: NeverReason   ## `never` read when intent == iNever
  AxisTable[K; S; P] = object
    axis: Axis; rows: Table[K, Row[S, P]]          ## array[K, …] when K is an enum

func admitted*[P](a: Admit[P]): bool
func payload*[P](a: Admit[P]): P                   ## asserts admitted
func decline*[P](a: Admit[P]): (SymexErrorKind, string)   ## the reason names $cell

# per axis: a site enum, the rows, and the verb
type MagicSite* = enum msUnsignedOps, msCallExpr, msProcRegister, msDefectScan
const magicAxis = axisTable[string, MagicSite, Empty](axMagic, …)
func admitMagic*(name: string; site: MagicSite): Admit[Empty]
func magic*(name: static string): CellKey          ## static: the row must exist
func admitTypeOp*(k: IRTypeKind; op: MemOp): Admit[CopyModel]
func admitDefinedness*(op: ArithOp; cls: OperandClass; b: BuildSemantics): Admit[Defined]
func admitPcreLib*(version: string; jit: bool): Admit[PcreEngine]  ## absent: psUnverifiedLib
iterator cells*(axis: Axis): Cell
```

(2026-11-07, W1-z) ADM-1's spike (`origin/rfc-0016-adm1` `04cd1ab7`) changed the interface
above, and the code is the reference where they differ: the decline kind is
`Option[SymexErrorKind]` (PCRE's refusal is `psUnverifiedLib`, not a
`SymexErrorKind`); an admitted row is admitted per site set and carries an
`elsewhere` kind for the other sites; the key type parameter is dropped
(`AxisTable[S, P]`, string keys), since both first consumers key on text; rows
are a `const` seq searched linearly, not a `Table`; and the per-axis verbs live
beside their payload types (`pcre_engine.admitPcreLib`,
`dsl_parser.admitVarMagic`), because those types are not importable from
`admission.nim`. `builds` is not yet on `Row`.

Rules the types carry, not the reviewer:

- **Admission is a proof the IR demands.** `Admit`'s fields are private, so
  only `admission.nim` constructs one, and the IR constructors of every
  keyed-axis node take it as an argument (`mkMagicCall(a: Admit[Empty], …)`,
  `mkParam(copy: Admit[CopyModel], …)`). A parser arm that skips the table
  does not type-check. The census (K2) is then needed only on the construct
  axis, where no table exists.
- **Absent is a decline.** A string-keyed axis (magics, pragmas, stdlib
  bodies) answers not-admitted with `feUnadmitted` (or the axis's own absent
  kind, `psUnverifiedLib` for PCRE) for a key it has no row for. An
  enum-keyed axis is an `array[K, …]`, so a missing key is a compile error and
  the lookup is O(1) on the walk's hot path.
- **A decline names its cell.** `reason` carries `$cell`, so a consumer's
  report names the cell §6's intake keys on.
- **Out of scope is a ledger intent, not a third answer.** A consumer does
  the same thing for "not yet" and "never": decline with a kind. `Intent` and
  `NeverReason` are for the ledger, and an `iModel` decline is open work
  (§12 item 2).
- **An exact row states its build rows.** `exact(key, rows)` with an empty
  `rows` set does not compile. Which test pins a row is not on the row: pins
  report themselves (§8.2).
- **Dispatch is generated per site.** Each axis's site enum names the places
  that consume it, each row names its sites, and
  `dispatchMagic(site: static MagicSite, …)`, a macro, expands to the `case`
  whose `else` is a decline and `error()`s at compile time on an arm with no
  row for that site or a row for that site with no arm. K4a's RED asserts each
  site member is instantiated exactly once (a `{.compileTime.}` registry).
  The first site converted is `dsl_parser.nim:11866-11892`: the
  `unsignedIntOps` lookup and the per-name switch after it, whose
  `else: discard` falls through to generic call handling today.
- **The magic axis keys on name.** Whether a magic is modelled at a site is
  the magic axis's question; whether its operands make it undefined (a
  literal `-1` divisor, a signed width) is the definedness axis's, keyed by
  `OperandClass`. One enum, one axis each.
- **`feUnadmitted` is `dcNoAnswer` until K7 lands.** The walker's
  `isUnsupported` arm continues every live path with `forkPathTainted`
  (`runtime.nim:24508-24512`) and `pathTaint(dcOmitted)` is empty
  (`types.nim:3650-3652`), so a `dcOmitted` decline there would let an
  `sxSat` through clean. `feUnadmitted` moves to `dcOmitted` only once K7's
  `halted` drops the path.

**Not axes.** Things the ledger enumerates that no engine table answers:
`SymexErrorKind` coverage (each member is the kind of some declined row or
`pinDecline`, or it is deleted) and `CapKind` coverage (each cap has a pin
that a cut run is never `trusted()`, §8.4 K7) are derived by K1 from the pin
records. **Call-site × callee shape**, **exceptions × memory** and **generic
instantiation** (nested instances, `when T is …` in an uninstantiated body,
`mixin`/`bind`, static params, distinct arguments, proc-typed formals, the
instantiation cap; `geUnresolvedGeneric`, `geInstantiationCapped`, AUD-07)
are test-side pin families (`faCallShape`, `faExnMemory`, `faGeneric`),
because the walker has no single dispatch point for them; each gets a K8b
fuzzer family.

The axes and what they absorb:

| axis | key | consumers | absorbs |
|---|---|---|---|
| magic | name | four sites: `unsignedIntOps` and the switch at `dsl_parser.nim:11866-11892`, `ensureProcRegistered`, the opaque-call defect scan (`:4152`) | `varParamMagics` (`:4254`), the four string arrays (`:4018-4030`), `unsignedIntOps` |
| type class | `NimTypeKind` × modifier (`var`, `sink`, `lent`, `owned`, `static`, `typedesc`) | `classifyType` (`dsl_typebridge.nim:1247-1520`), a chain of structural guards, not a `case` | distinct (by sym), range, enum holes, `cstring`, the `varargs[T, conv]` element conversion, `static[N]`, proc types |
| type × memory op | `array[IRTypeKind, set[MemOp]]` | `typeCopiedByValue` (`:7835`, on `NimNode`) and `holdsSharedMemory` (`:16561`, on `IRType`) through one `classifyType` normalisation, itself a row of the construct census | the S8cq by-value allowlist |
| pragma | pragma name × place (local `var`/`let`; routine and parameter; type), each list checked against Nim's `pragmas.nim` text | `localDeclGate`, the routine and type walks | the `noinit`/`global` special cases at `:19771-19792`; `union`, `packed`, `byref`/`bycopy` (today read by no `smt` module); `noalias` is a definedness `OperandClass` (C `restrict`) |
| build | `BuildSemantics` (§8.3) | `symexFind` at macro time | `verifiedLibs`' role for Z3, Nim and PCRE (`admitPcreLib`) |
| read-only | node kind and call shape proved not to write | one `mayWrite(n)` | the four parser predicates `nodeWritesHeap` (`:16574`), `routeStoresThroughDeref` (`:22429`), `ptrUsesStayLocal` (`:6546`), the hook copy-proof (`:22505`) |
| definedness | `array[ArithOp, array[OperandClass, …]]` read with the profile (§9); opaque calls answer through the magic and stdlib-body rows (defined / undefined-when / absent) | the arithmetic lowering; K10b's gate | `arithTrapConds`, `currentArithWraps` (`runtime.nim:1976`) |
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
verdict change, and makes their consumers *take* an `Admit` rather than ask
for one (`ensureProcRegistered` for the first): `varParamMagics` (19
string-keyed entries, 16 modelled) and
`verifiedLibs` (`pcre_engine.nim:143`, record-keyed, three consumers in
`pcre_engine.nim`, whose lookup returns a payload, the engine model, and whose
absent kind is `psUnverifiedLib`). The second is why `Admit` carries a
payload and an axis-specific absent kind; if the spike finds the shape wrong,
the interface changes there, before any new table is written on it.

### §8.2 The universe ledger is an output

`tests/tsymex_0016_universe.nim` (registered in `nelli.nimble`) iterates
`cells(axis)` for every axis and family, joins them to the pin records and
the work list, and **emits** `docs/rfc/0016-universe.tsv`. Unlike `.drift`,
the TSV is committed: the test diffs its output against the committed copy,
which is how "only grows" (§12 item 5) is checked by a machine and not by
review.

- **A cell is a `CellKey`**: a scope and the rendered discriminant the code
  actually reads (an operator name, a conversion pair, a magic name, a type ×
  memory operation, a family shape). Identity has no file or line, so a
  refactor does not churn it.
- **What is enumerated:** every axis of §8.1, the three families, and the
  error-kind and cap-kind coverage derivations. Magic names are scanned from
  all of `lib/` with multi-line declarations; `TMagic` is not importable, so
  its count is a dev-image script output, not an assertion.
- **States:** `exact(rows)`, `declined(kind, reason)` (intent `iModel`: open
  work), `never(kind, NeverReason)`, and for unsat cells **exhaustive** vs
  **sampled** native evidence, printed separately. The test rejects
  `unclassified`, and on each leg an `exact` cell that claims the leg's row
  with no record from it counts as unclassified there, so it lands in the
  allowlist and ratchets out instead of passing silently.
- **Pins report themselves.** The K9 helpers write one record per pin at run
  time: test file, entry point, `CellKey`, target, domain, `exhaustive`,
  `PinVerdict` (an enum: `exact`, `declined`, `raised`, `crashed`,
  `skipped`), native result, the build segment, `rowOf`'s row, and for
  `pinCrash` the probe's own flags. Records go to `$NELLI_PIN_DIR` (default
  `tests/.pins/`, git-ignored), one file per run id, so two runs of one test
  file never clobber and two Z3 versions of one segment never merge.
  `dt-bounded.sh` forwards the variable into the container. K1 joins cells to
  records; it does not scan test text.
- **K1 runs after the pins it joins.** In CI, the shards upload their record
  directories as artifacts and a join job per leg runs the universe test over
  them. Locally, `sweep.sh` excludes the universe file from its parallel set
  and runs it last over the sweep's record directory, failing if the
  directory is empty. Each `BuildRow` with a run leg must have a record
  directory dated within seven days; a dead leg is a failure, not an absence.
- **The work list is data.** `docs/rfc-data/0016-worklist.toml` holds one
  `[[row]]` per id: `id`, `title`, `class`, `state` (`open`, `closed`,
  `merged`, `moved`, `never`, `owned:RFC-NNNN`), `cells` (rendered
  `CellKey`s), `home` (slice), and for `never` a `NeverReason`. §5's tables
  are rendered from it between markers by `scripts/render_worklist.nim`, and
  K1 fails when the rendered block is stale. K1 reads the TOML with a
  flat reader in `tests/` (arrays of tables, string and string-array fields
  only), never the markdown. A `cells` entry is validated by parsing it back
  to a real key, so a typo fails instead of silently naming nothing. The F
  ledger's rows live in the same file with `source = "F-NNNN"`.
- **What the join checks.** Every `open` row names at least one cell, against
  `tests/0016-allowlist/ids.txt`. Every `closed` row names a cell that is
  `exact` or `never`, or a registered `pin` file. Every `never` row names a
  `never` cell that exists. A row's `home` is a slice id until its cell lands.
- **What it certifies.** Single-site exactness. Combinations (a construct
  nested in another, a memory route through a call) are the fuzzer's,
  measured by the pairwise figure (§12 item 4), which K1 reads from K8b's
  cells-exercised records as a second record kind.
- **Ratchet.** Allowlists live in `tests/0016-allowlist/<scope>.txt` and
  `ids.txt`. What the test checks: every unclassified cell (or unnamed open
  id) is in its allowlist, and every allowlist entry is still unclassified (a
  stale entry fails, which forces removal). What review checks on the diff:
  an allowlist grows only in the commit that introduces its scope, by exactly
  that scope's cells. K1a's first content is the error-kind derivation (every
  member of `SymexErrorKind`, nearly all unpinned on day one), the two ADM-1
  axes, the build rows and the id list.
- **First commit proves it runs.** The slice that lands it shows it RED on
  each CI leg with a planted unclassified cell, demonstrated by run URL.
- **Skips are records.** `skipCell(magic("DivU"))` writes a `skipped` pin
  record; K2a's census fails on a bare `skip(` or an unexplained platform arm,
  against its own ratcheted allowlist.
- **Threads.** Pin records and marker capture are per thread
  (`markers.nim:70`); K9's helpers merge at exit. Running `symexFind` off the
  main thread (`parallel.nim:843` with `symexSeedPhase`, `symex.nim:990-1007`)
  is a cell of the build axis, pinned by the three isolation suites
  (`s8bp_isolation`, `s8ca_stack`, `s8ct_isolation_e`).

### §8.3 BuildProfile: one constant, read and keyed

The SUT and nelli are one binary, so most of the build is a compile-time
fact. Some of it is not: the PCRE engine is read through a dynlib call
(`pcre_engine.nim:93`) and the Z3 version at run time. So the profile is
split by *when it is known* and by *whether it is keyed*, and a new field is
keyed or not by where it lands; no field list can be forgotten:

```nim
type
  BuildSemantics* = object   ## compile time, keyed; const buildSemantics*
    checks*: set[CheckOption]; panics*: bool; mm*: MemModel; exceptions*: ExcMode
    backend*: Backend; opt*: OptLevel; fwrapv*: bool; ptrBits*: int
    cpu*: Cpu; os*: Os; endian*: Endian; caseObjects*: CaseObjMode   ## enums, not strings
  HostSemantics* = object    ## run time, keyed; read once at the first symexFind call
    pcre*: PcreEngine; z3*: Z3Version
  BuildProvenance* = object  ## rendered on findings and pin records, not keyed
    ccFamily*: CcFamily; nimVersion*, patchset*: string; assumedAbsent*: set[CFlag]
func buildSegment*(b: BuildSemantics; h: HostSemantics): string  ## fieldPairs, tagged, versioned
func rowOf*(b: BuildSemantics; h: HostSemantics; p: BuildProvenance): Option[BuildRow]
```

`rowOf` is the one projection from a build onto the rows cells claim
(Linux c, Linux cpp, Z3 5.1, Z3 4.13.4, mingw, MSVC), an exhaustive `case`
in `buildprofile.nim` with a written justification for each field it treats
as neutral: `opt` is neutral except through undefined behaviour (K10);
`release`/`danger` act only through `checks`; arc and orc agree except for
the cycle collector (a `never` cell, S8cs). Each neutrality claim is pinned
by K5b's cross-build cfg suites. `admitBuild` refuses a profile `rowOf`
cannot project, so a consumer's `-d:release --mm:arc` build either lands on a
pinned row or is refused by name; it never borrows a row's verdicts. Pin
records carry `rowOf`'s answer beside the segment, so K1 needs no map.

`buildprofile.nim` absorbs the build *reads* that exist today: `buildChecksOn`,
`buildMemModel`, `buildBackend`, `buildExceptions` (`canonicalize.nim:6549-6595`),
the `compileOption` reads in `check_options.nim:113-120`, `engine.nim:59`,
`runtime.nim:25916` and `dsl_parser.nim:18386-18998`. It does **not** change
`check_options.nim`'s model: `routineChecks` is a deviation from `defaultOn`
(`check_options.nim:104`, `:123`, `:739`), an absolute baseline, and that is
why a checks-off build carries the `feOverflowCheckOption` marker on every
routine (`dsl_parser.nim:1471-1474`). Rebasing it on the build would drop the
marker on exactly the builds W-07 describes. The C compiler version is a
run-time fact of the pin record.

**What `querySetting` cannot read is refused or produced, never guessed.**
`querySetting(compileOptions)` does not see `--passC` from the command line,
`nim.cfg` or `config.nims` (Nim routes those to `compileOptionsCmd`,
`commands.nim:862-864`; `vmops.nim:169` returns only `compileOptions`), nor
`{.localPassC.}`, nor the `-O` level. So nelli does not try to read
`-fwrapv`; it **produces** it. A consumer who wants defined signed wrap
compiles with `-d:nelliFwrapv`, and `buildprofile.nim` does
`when defined(nelliFwrapv): {.passC: "-fwrapv".}`, a global pragma that
reaches every C and C++ unit of the program, the runtime's included
(`pragmas.nim:1164-1168` → `extccomp.nim:474-475`, `:579-590`; the command is
hashed into each unit's footprint, so nimcache recompiles). `-fwrapv`
defines `+`, `-`, `*` and negation only; `low(T) div -1` and `mod -1` stay
undefined. It lands in K5a with the field, never after it. The define
is then a fact of the build, not a claim, and `fwrapv` is a semantic field.
`admitBuild` refuses it under `vcc`, which has no such flag.

Three things derive from the profile:

1. **The cache key.** `buildSegment` iterates `fieldPairs` over
   `BuildSemantics` and `HostSemantics`, under a versioned tag. (Nim's `$` on
   an object changes with any field rename or reorder.) It replaces the hand
   list at `canonicalize.nim:6558-6592` (INT-31's `|bf=` half), the `|z3=`
   segment (`:6645`) and the `defined(nimPanics)` default at `:6537`. The
   same treatment covers `SymexSettings` (`canonicalize.nim:6501-6530`): every
   field is keyed unless it is named in an explicit neutral `const`, so a new
   setting cannot be silently unkeyed.
2. **Refusals.** `admitBuild` runs the compile-time half in `symexFind`'s
   macro (an `error()` naming the field) and the host half once at the first
   call. Refused by name: `--mm:refc` (D-0016-7, from Wave 1), 32-bit `int`,
   big-endian, an unverified Z3, Nim or PCRE build, `-d:nelliFwrapv` under
   `vcc`, a profile `rowOf` cannot project, and arm64 and macOS **until a CI
   leg runs the suite there** (a compile-only leg cannot satisfy §12).
3. **On the verdict.** `Soundness.buildSegment` carries the segment, so a
   finding renders "decided on c/orc/goto/64-bit, panics off" and a cached
   verdict read under another profile is a different key, never a hit. The
   CR2 cache-key test holds one golden segment per run leg, selected by
   `when defined(cpp)` / `defined(vcc)` / the Z3 version, never by the
   segment function itself.

Every walker arm that depends on the build reads `buildSemantics`; a test
pins that `defined(nimPanics)`, `compileOption(` and `defined(release)` occur
in `src/nelli` only inside `buildprofile.nim`. W1-c1a and W1-c1b pin the
sites they reroute by name; K5a extends the pin to the rest (the
`compileOption("assertions")` reads in `dsl_parser.nim`).
`{.push.}` regions stay in the IR
as `feCheckOption` markers, with `defaultOn` as their baseline (above), not the profile;
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
| K1 | universe test and ledger (§8.2); error-kind coverage, deleting producer-less kinds | the finish line itself; W-64 |
| K2 | dispatch census over every `case n.kind` in `src/nelli`; `typeIdOf(sym): Option[string]` as the only source of exception type ids (`none` is `eeUnknownExnType`); child-shape census corpus | W-01, W-04, W-15, W-21, W-27, W-33 |
| K3 | the type-class, type × memory-op and pragma axes (the pragma lists are hand-written: Nim has no enum of pragmas, so the guard is checked against Nim's `pragmas.nim` text) | W-02, W-12, W-20, W-43, B-04 |
| K4 | the magic axis with a lib-wide guard; a bodied magic not admitted as walked-by-body declines; the stdlib-body axis seeded from a `feStdlibBodyWalked` hint; every raise-text decline gets a `SymexErrorKind` | W-05, W-06, W-22, W-24, C-11, C-16 |
| K5 | `BuildProfile` (§8.3) | W-03, W-14, W-17, W-23, W-50, W-51, W-52, W-53, INT-31 |
| K6 | `mayWrite(n)` over the read-only axis; a walked user callee recurses with a cycle bound, an opaque one may write anything; pinned on a write-shape corpus with native runs | W-08..W-10 |
| K7 | degrade discipline by type, and every cap a typed halt (below) | W-07, W-11, W-16, D-13 |
| K8 | differential fuzzer (slice D1, §4, §10), its families generated from the axes, plus metamorphic relations (§10) | the next W-01, before a consumer finds it |
| K9 | one shared native-pin helper (below) | W-54, W-55, W-56, W-57, W-61 |
| K10 | undefined behaviour as an outcome (§9) | W-05, W-06, W-07, W-13 (settle half) |

**K7, concretely.** Paths are `seq[Path]` everywhere
(`walkStmt(stmt, paths, w): seq[Path]`, `runtime.nim:23704`; `Path` is a
`ref object` private to `runtime.nim:549`), so the type is introduced at arm
exits, as a layer over the existing `degrade`/`forkPathTainted`/`taintInPlace`
vocabulary, not beside it:

```nim
type Survivors = object               ## runtime.nim, beside Degrade
  live: seq[Path]
func halted(w: var WalkCtx; kind: SymexErrorKind; msg: string;
            scope = walkSite()): Survivors        ## records, returns no paths
func surviving(ps: seq[Path]; d: Degrade): Survivors  ## fold of forkPathTainted
func continued(ps: seq[Path]; d: Degrade): Survivors  ## fold of taintInPlace
func exact(ps: seq[Path]): Survivors                  ## the walker's word; no token
```

There is no "admitted" constructor: an `Admit` is the parser's fact and
proves nothing at walk time, so the walker's untainted exit is plain
`exact`, and what keeps it honest is K2's census of `Survivors(`, `exact(`
and `Degrade(` sites, not the type alone (privacy inside a 31k-line module is
nominal). `degrade` stops being exported; `halted` holds the one sanctioned
`discard` of its token. K7b converts the `isUnsupported` arm to
`walkUnsupported(…): Survivors`; K7c brings every `walkStmt` arm to return
`Survivors`. The 20 `discard w.degrade(` code sites (19 in `runtime.nim`, 1 in
`runtime_heap.nim`) come in four shapes: an arm return, a void return in a
routing proc, a per-path drop inside a loop (all three become `halted`), and
recorded-but-continued (`runtime.nim:19172` records `weInternalWalkerFault`
and routes the raises anyway), which becomes `continued`. W-11 (`svWithRaw`
returning the old value for a composite) and W-16 (`defectExclusions` making a
Defect path unreachable with `sxUnsat` still trusted) take the same
discipline.

**Caps are halts.** Seventeen caps stop a walk early (`types.nim:5873-5918`:
`maxFrontierSize`, `maxCallDepth`, `maxHeapDepth`, `maxLoopUnwind`,
`maxRecursionDepth`, `maxFreshnessAssertions`, `maxClosureInlineCount`,
`maxInstantiationsPerProc`, `maxSplitParts`, the `maxVariantConstructor*`
pair, `maxSeqLen`, `seqQueryRLimit`, `queryTimeoutMs`, `replayTimeoutMs`; and
the consts `maxModelledInitialSize`, `maxBitSetDomain`, `termWalkMaxDepth`,
`maxDefectScanDepth`). K7a adds `CapKind` with one `halted` (or `continued`)
site per member; K1 derives cap coverage like error-kind coverage. The
soundness half stays here; only "raise the cap" moves to RFC-0017 (MOV-01).

**K9, concretely.** It grows `tests/s8cu_helpers.nim`, which already
shares `native`/`declines`/`decides` by import, instead of starting a fourth
lineage beside the 35 `nativeHits` copies and the 55 `declines` templates.
`pinExact` is built on the public `assertCoveredBy` (whose splat already runs
the walker's witness natively) plus a loop over the domain, so nothing in
`symex.nim` is exported for it:

```nim
type Domain*[T] = object
  values*: seq[T]; exhaustive*: bool
func exhaustive*[T](v: openArray[T]): Domain[T]
func sampled*[T](v: openArray[T]): Domain[T]
const boundaryInts* = sampled([low(int), low(int)+1, -1, 0, 1, 7, high(int)-1, high(int)])
macro pinExact*(fn: typed; key: CellKey; target = tLabel("hit");
                domain = boundaryInts): untyped        ## returns the SymexResult
template pinDecline*(fn: typed; key: CellKey; kind: SymexErrorKind;
                     target = tLabel("hit"))
proc pinCrash*(key: CellKey; probe: string; flags: openArray[string];
               expect: CrashExpect)
proc skipCell*(key: CellKey; why: string)
iterator pinRecords*(dir: string): PinRecord           ## the reader K1 joins on
```

Three verbs. A raise is a target, not a verb:
`pinExact(fn, key, target = tRaisedExn("ValueError"))`. `pinExact` is
differential: `sxSat` means its witness hits natively, `sxUnsat` means no
domain value hits (exhaustive or sampled by the domain), and `sxUnknown`
fails. The common test is `discard pinExact(sut, magic("DivU"))`. `kind` is
mandatory on a decline. `pinCrash` compiles a probe and runs it in a child
(the `probe()` shape of `tsymex_rfc0005_s8cu_nil_native.nim:18-40`); the
probe inherits the host's `-d:` defines (so `-d:nelliFwrapv` reaches it),
picks `--cc:vcc` under `defined(vcc)` and `--cc:gcc` otherwise, and asserts
the exit class per OS (`0xC0000094` on Windows, `SIGFPE` on POSIX for a
division trap), not merely "did not finish". Since it bypasses every public
entry point, a `pinCrash` record can evidence only a `declined` or `never`
cell. K9a lands `CellKey` and `render` in `smt/admission.nim` with an
unchecked `cellKey(scope, static string)`; each axis's introducing slice
switches its keys to the checked constructor (`magic("DivU")` is a `static`
lookup), so no Wave-1 pin is retyped wholesale later.

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
   `runtime.nim:8478-8492`). The defined side continues exactly, with `¬cond`
   in its `pc` (not in `defectSurvivorPc`, which makes a callee uncacheable,
   `:23618`). The undefined side is decided **eagerly, at the op**, against
   the path condition there, with the check the loop arms use
   (`checkCapped(pathRoots(p, [cond]))` under `loopPruneRLimit`,
   `:15724-15737`):
   - **unsat:** `logPrune(p, [cond])` inside the current call's prune window,
     and the side is dropped. A call-cache summary is then reused only where
     the fact still holds (`pruneFactsSince` `:18124`, `pruneFactsHold`).
     Deciding at the boundary instead would put the fact outside the callee's
     window (`pruneMark`, `:23365`) and the clause would be dead.
   - **sat or unknown:** the side becomes a terminal path that leaves through
     the crash channel, never `routeRaise`, whose handler search would let a
     bare `except:`, an `except DivByZeroDefect:` or a `finally` consume it
     (`:25742-25823`). The channel is `haltUndefined`, a sibling of
     `crashRaise` (`:25899-25947`) with no setjmp arm, no `defectExclusions`
     check, and a `degrade` halt with the op's `UbKind` (`dcOmitted`, run
     coordinate `{scIncomplete}`) in place of a finding.

   This sink is ungated, like `arithTrapConds` (`:19091-19113`). Where a
   Defect fork already covers the condition (checks on), the op is *Defect*,
   not undefined, and there is one fork, not two. The cost is one capped check
   per unchecked op on a reachable path; W1-d1a's RED records paths and solver
   units on a fixed SUT set against 0.9.1.
3. **A trusted `sxSat` needs the whole run defined, not only its prefix.**
   C's undefined behaviour is not sequenced, and the walk stops at the first
   label hit (`shouldStop`, `runtime.nim:17308-17318`), so it never sees what
   follows. The gate is a scan, transitive over the entry's walked callees
   (`parsed.procs`, `symex.nim:4461`), for any op whose definedness row is
   *undefined* on this profile. An opaque call answers through its own row on
   the magic and stdlib-body axes (*defined*, *undefined when …*, or absent,
   which is "may be undefined"); a blanket "opaque means may be undefined"
   would mark nearly every `sxSat` whose tail reaches `echo` or `$`. The scan
   is `scanOpaqueDefects` (`dsl_parser.nim:4093-4170`) parameterised, with
   three branches flipped: foreign code with no row answers "may be
   undefined" (today "raises nothing", `:4165-4166`), float-source
   conversions are included (`:4132`), and overflow magics read the owner's
   check options as floats already do (`:4147-4154`). When the gate is on,
   the winner is checked by **a second walk from the entry** under the
   witness's choices in concrete-follow mode (`wmFollowConcrete`, built at
   `runtime.nim:29882-29894`; there is no resume-from-label), ignoring
   `shouldStop`, to a routine exit with `concretelyInfeasible` (`:19793`)
   true for every undefined side. A decline, a budget (`beBudgetExhausted`,
   `:20952`), an undecided side, or a lossy witness (`wfLossy`, which cannot
   be followed) counts as undefined. `symexFindAllWitnesses` runs one walk per
   finding. K10b flips trust broadly and is a *round*.
4. **The verdict carries it, and replay cannot lift it.** Undefined
   behaviour rides the soundness machinery the way taint does: each kind is a
   `SymexErrorKind` member (`ubUnsignedDivZero`, `ubIntMinModMinusOne`,
   `ubSignedOverflow`, `ubFloatToIntRange`, `ubIndeterminateRead`, declared
   together and contiguous, `UbKind* = range[ubUnsignedDivZero ..
   ubIndeterminateRead]`); the `Degrade` token carries `ub: set[UbKind]`
   derived from its kind; `Path` carries `undefined: set[UbKind]`, joined by
   every carrier that joins `taint` (fork, merge, call cache, unroll, cache
   load; the S1 lattice test's carrier pin covers it). `Soundness` gains
   `witnessUndefined: set[UbKind]`, *derived* from the winner's
   `path.undefined` at settle as `pathTaint` is (`runtime.nim:24236`), plus
   the whole-run gate's answer. It is cached as the sixth field of codec
   version 4, a decimal integer of any length (`decodeSoundness` reads one
   character per field today, `symex.nim:355-357`, and a five-member set
   needs two), pinned by `ord(high(UbKind)) - ord(low(UbKind)) < 30`;
   `runDependence` becomes the optional seventh. `trustedSat`
   (`soundness.nim:162-169`) and `hostRunnable` both require it empty: a
   native replay that reaches the label cannot make the verdict `trusted()`,
   and neither `symexForAll` (`symex.nim:1121`) nor `assertCoveredBy` runs
   such a witness in the host. `cacheable` is unchanged. The rendered field
   says "undefined behaviour: <kinds>"; no separate hint kind. `SymexFinding`
   projects it as `FindingUndefined`, the way `gaps` is projected.
5. **Undefined behaviour is a target, not a status.** `stkUndefined`
   (`tUndefined(kinds: set[UbKind] = all)`), beside `stkNilAccess`
   (`types.nim:1862`). `UbKind`, not "class": class is the lattice's word.
   `sxSat` comes with a witness; `sxUnsat` means none of the *listed* kinds is
   reachable, never "no undefined behaviour", and `describeTarget`
   (`symex.nim:216`) renders the list. The result gains
   `undefined*: seq[UndefinedFinding[T]]` (kind, source anchor, witness), so
   `UndefinedFinding`, `FindingUndefined` and `undefined` rhyme; an undefined
   behaviour reached under any other target is listed there, not in
   `diagnostics`, which is typed for raised Defects. A halt under another
   target names `tUndefined` as the next query. No `SymexStatusKind` member is
   added; `SymexTargetKind` grows, which breaks every `case` on it without
   `else`: in-tree, `replayInScope` (`symex.nim:2343`), `wireTarget`/
   `unwireTarget` (`:2923-2943`) and the `bindSym` splices (`:3630`,
   `:3980-4024`, `:4212`, `:4246`); outside, any consumer's, which the 0.9.2
   note tells to add an `else` arm now.
6. **Replay does not run a `tUndefined` witness** (refused by target kind).
   `assertCoveredBy` never executes one in the host; its splat catches
   `Defect` regardless (W-26). `symexForAll` does not seed one unless asked.
7. **The native pin is UBSan**: `-fsanitize=undefined
   -fno-sanitize-recover`, gcc/clang, Linux (CI-A). MSVC has no UBSan and
   mingw's is unsupported, so the Windows legs carry declared
   `never(nrPlatform)` cells for these rows; the unsigned-zero-divisor crash
   pin asserts the exit class per OS (`SIGFPE` on POSIX, `0xC0000094` on
   Windows).
8. **`arithChecks` is removed in 0.10.0** (with `fromCache`, INT-39; both
   `{.deprecated.}` in 0.9.2 with the migration path in the message (2026-11-07, W1-z): Nim 2.2 rejects `{.deprecated: "msg".}` on an object field, so both fields carry the bare pragma and the path forward is in the doc comment and `docs/migration/0.9.2.md`): the
   checks are a fact of the build, and Nim's answer is the build's alone
   (with `optOverflowCheck` on, `div`/`mod` get the zero check and
   `nimDivInt`'s `low(T) / -1` check, `ccgexprs.nim:595-617`; with it off,
   plain C operators). Until then, from W1-d2: one predicate,
   `buildWraps = coOverflow notin buildSemantics.checks`, feeds every reader
   that decides wrap (`currentArithWraps` `runtime.nim:28471`, `wrapScan`
   `:28722`, `offsetExact` `:28883`), so the lowering and the Z3Int
   promotion cannot disagree (the #161 contradiction); `defaultSymexSettings`
   derives `arithChecks` from the build, so only an explicit opt-out
   disagrees; an explicit disagreement is warned by `warnIncoherentSettings`
   (`symex.nim:3532`, given the profile) and taints every path it touches
   with `feCheckOption`. A decline, not a refusal, so 0.9.2 breaks no caller
   that sets it. The `;ac=` cache segment (`canonicalize.nim:6513`) stays
   until K10d.

**Float to int out of range** moves to the halt. Today it is a tainted fresh
symbol (`feConvFloatToIntUndefined`, `dcFreshSymbol`,
`runtime_floats.nim:230`); under the time-travel rule a fresh symbol is not
sound for a trusted `sxUnsat` either. The sweep-diff records the precision
change.

**`{.noinit.}` is not a halt.** A read of a `{.noinit.}` variable is an
indeterminate value, and the walker already models it soundly as havoc
(`runtime.nim:9226-9240`), so an `sxUnsat` stays trusted. The defect is that
replay *confirmed* a witness that needed garbage memory (W-13). The fix is
item 4's field, per path from Wave 1: the read is observed where
`unwrittenKind` returns `feGlobalHavoc` for a `noinitReadPrefix` part
(`runtime.nim:9283-9293`, consumed at `observeRecvPart` `:20086-20096` and the
other `unwrittenIn` sites), not at the allocation (`noinitValue`, which runs
for `var x {.noinit.}: int; x = 5` too); it adds `ubIndeterminateRead` to that
path's `undefined`. Its native pin is MemorySanitizer or valgrind, since UBSan
does not detect it.

**Wave 1 (0.9.2) ships the fail-closed half** before the table exists (§11
W1-d1a-c, W1-d2, W1-d3): the zero side of an unsigned divisor and the
`INT_MIN mod -1` side halt through `haltUndefined` (K7's `halted` does not
exist yet; the nonzero side stays exact); a checks-off signed op declines on
both routes (the push marker and the setting); the per-path `{.noinit.}`
field. **Known gap in 0.9.2**, listed in its migration note: an undefined op
*after* the label does not yet untrust an `sxSat` (item 3 is K10b). K10 in
0.10.0 restores the defined side of signed arithmetic under `-d:nelliFwrapv`
and adds the target.

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
- **`exact` pins run on resource limits only.** `queryTimeoutMs` is wall
  clock (`canonicalize.nim:6498`), so a pin under it can flake to a decline;
  K9's `pinExact` sets rlimit budgets and no timeout.
- **Witness rendering has an oracle.** Per `IRTypeKind`: render, parse,
  compare with the witness, including NaN, −0.0, embedded NUL and shared
  `ref` cells (`runtime.nim:30854-30930`).
- **A second oracle where cheap.** For generated SUTs with no `importc` or
  pointer arithmetic, the Nim VM (`nim e`) gives a third column: walker
  against the Nim language versus Nim against the C backend. Every Tier-0
  row in §5.0 is a desugaring bug of the first kind.
- **Public entry points.** K1 refuses an `exact` cell whose pin record does
  not come from one of the six: `symexFind`, `symexFindAllWitnesses`,
  `symexForAll`, `assertCoveredBy`, the concolic path, or a cache hit
  (`loadSymexVerdict`, `symex.nim:4260-4390`), whose model is its key.
- **Metamorphic relations.** Semantics-preserving rewrites must leave the
  verdict unchanged: dead code under a provably false guard, commutative
  reorder, extract-to-proc, wrap-in-template, `let` ↔ `var` where unwritten,
  and the §6 neighbour shapes (shared vs copied, reversed evaluation order).
  It needs no native oracle and aims at the Tier-0 desugaring class directly
  (Le, Afshari and Su's EMI); K8b generates them per family.
- **Cost is measured.** Each pin record carries the walk's paths and solver
  units, and each sweep summary its wall time, so §12 item 7 is a figure.
- **Families from the axes.** The fuzzer's families iterate `cells(axis)`
  (every exact row with its shapes and build rows), so coverage means "row
  exercised on its build rows", not a hand list. `tfuzzconcolicmismatch` and
  `annotationViolations` (INT-33) are a second findings source; INT-33's
  reader is a K8a dependency.
- **Triage has a sink.** The nightly job uploads `findings/<date>.tsv` and
  the shrunk `.nim` files as an artifact and opens or updates one issue per
  new shape hash, labelled `rfc-0016-intake`. It also checks out the last
  release tag and fills the release column of the three-way row itself, and
  writes a dated heartbeat into the artifact. Each wave's integration slice
  checks that no `rfc-0016-intake` issue is older than seven days without an
  F row, and that the heartbeat is under seven days old (§6, §11).

## §11 — Slices and order

Each row is a slice within about three modules; a row marked *round* flips
verdicts broadly and is gated by a pinned sweep baseline from a worktree at
its base sha (`sweep.sh` + `sweep-diff.sh`), not by its own tests. Every new
test file a slice adds is registered in `nelli.nimble`'s `test` task in the
same slice; otherwise symex-mingw's derived corpus (`derive-ci-suites.ps1:18-19`)
never sees it.

**Walker versions.** Every slice that changes a verdict bumps
`symexWalkerVersion` (`canonicalize.nim:251`), updates the CR2 pin
(`tsymex_phase15_CR2_cachekey.nim:1103`, an `==` today) and adds a `>= N`
floor in its own test file, so no intermediate sha serves a cache written by
an earlier one. The integration slice of each release records the final
number.

**Releases.** Wave 1 ships as 0.9.2. Waves 2 and 3 ship together as 0.10.0
(`feUnadmitted`, the K3/K4/K7b verdict flips, the `buildSegment` cold start
and the removal of `arithChecks` are breaks). Wave 4 ships in 0.10.x patches,
except that a *round* slice ships in a minor.

**Wave 1 — 0.9.2: the seven clean false verdicts, plus W-20, W-21, W-26,
W-31 and W-33.** The order is forced by what each row needs:

1. **INF-05** first, then the three 0.9.1 baselines cut from a worktree at the
   `v0.9.1` tag (c, `-b cpp`, `-i z3-4.13.4`), uploaded as release assets of
   `v0.9.1` and named in `tests/0016-baselines.txt`; every later gate diffs
   against them, and §12 item 5 reads them without depending on a host.
2. **K9a**, so every RED below is a pin with a record.
3. **W1-c3** (a Defect witness can then be reported without killing the
   host), **W1-a**, **W1-c1a**, **W1-c1b**, **W1-c2**.
4. **W1-p**, **W1-b**, **W1-e**, **W1-g**, then **W1-f** after its one-time
   probe (which of a compile stop or a silent zero is today's behaviour
   decides its RED).
5. **W1-d1a**, **W1-d1b**, **W1-d1c**, **W1-d3**, then **W1-d2**, a round.
6. **K1-0**, the property end to end on the seven cells; **W1-m** at any
   point after INF-05; **W1-z** last.

In parallel, each in its own worktree: **ADM-1** (merged to `main` after the
0.9.2 tag, so it ships in 0.10.0) and **CI-A1** (provisioning only, no gate).

Every pin goes through a public entry point and runs its witness natively,
through K9a. Each new decline names its `SymexErrorKind` in the RED, and its
message points at a section of `docs/symex/README.md`, not at an RFC id.

| id | scope | modules | RED test (default build: c, orc, goto, checks on, unless stated) | size |
|---|---|---|---|---|
| INF-05 | Z3 4.13.4 tooling: `scripts/Containerfile.z3-4.13.4`; `-i <image>` on `dt-bounded.sh` and `sweep.sh`; `dt-bounded.sh` forwards `-e NELLI_PIN_DIR`; `tests/.pins/` git-ignored (RFC-0005's 4.13.4 sweep ran off an unversioned scratchpad script) | `scripts/` (3 files), `.gitignore` | `sweep.sh -i z3-4.13.4` on one file: its log names Z3 4.13.4; a pin run with `NELLI_PIN_DIR` set leaves its record on the host | xs-s |
| K9a | `pinExact`, `pinDecline`, `pinCrash`, `skipCell`, `Domain`, `boundaryInts`, the record writer and `pinRecords` (§8.4); `smt/admission.nim` with `Scope`, `CellKey`, `render` and the unchecked `cellKey`; the record's build segment rendered from `defined()` arms until W1-c1a swaps in the const | `tests/s8cu_helpers.nim`, `smt/admission.nim` (new) | a planted wrong `exact` pin fails; a `pinCrash` whose child exits 0 fails; each record read back through `pinRecords` round-trips every field | s |
| W1-c3 | `assertCoveredBy` splat catches `Defect` (W-26); every later in-host Defect witness needs it | `symex.nim:4080-4117` | `symexTarget("hit"); discard v + 1` with a `high(int)` witness: reported, host alive (today the process dies); on a panics-off build only (W1-c2 covers panics) | xs |
| W1-a | `typeIdOf` through `canonicalExnTypeSym` (`:1488`); W-01, W-33 | `dsl_parser.nim` (:20444, :20461) | `try: (if k==3: raise newException(ValueError,"x")) except ValueError as e: symexTarget("h")`: `tLabel("h")` `sxSat` (today `sxUnsat`), native hit at 3; `tRaisedExn("ValueError")` `sxUnsat` (today `sxRaised`). `let e = newException(ValueError,"x"); raise e` is `sxRaised ValueError`; `raise ex` with `ex: ref Exception` a parameter declines `eeUnknownExnType` | s |
| W1-c1a | `buildprofile.nim`: `BuildSemantics` (the Wave-1 fields: checks, panics, mm, exceptions, backend), `buildSegment`, absorbing `buildChecksOn`, `buildMemModel`, `buildBackend`, `buildExceptions` (`canonicalize.nim:6549-6595`) and the `compileOption` reads of `check_options.nim:113-120` (its `defaultOn` model unchanged, §8.3) | `buildprofile.nim` (new), `canonicalize.nim`, `check_options.nim` | the moved reads occur only in `buildprofile.nim`; `buildSegment` equals the old `\|bf=` text on each leg; no verdict change (sweep-diff empty) | s |
| W1-c1b | reroute the remaining Wave-1 reads (`symex.nim:2343`, `engine.nim:59`, `runtime.nim:25916`, the `defined(nimPanics)` default at `canonicalize.nim:6537`); refc refused by name (D-0016-7). The `dsl_parser.nim` assertion reads (`:18386-18998`) go to K5a | `symex.nim`, `engine.nim`, `runtime.nim` | `defined(nimPanics)` occurs only in `buildprofile.nim`; a `--mm:refc` compile of a `symexFind` SUT fails naming the field (`pinCrash`, `declined` cell) | s |
| W1-c2 | under panics a Defect is the S8cu `crash: true` escape (W-03, INT-27): `routeRaise` tests defect-ness before the handler search; a `raise` of an unknown-typed `ref Exception` under any `try` declines instead of warning; an `isDefect` claim sets `witnessUnsafe` (`soundness.nim:139-150`), so no host runs it. Destructors that run while a panic unwinds are a named known gap | `runtime.nim` (`routeRaise` :25666, :25733-25735, :25847, drains :19186, :23574), `tsymex_0016_panics.nim` + `.nim.cfg` `--panics:on` | `try: discard v+1 except Defect: symexTarget("h")`: `tLabel("h")` `sxUnsat`, `tRaisedExn("OverflowDefect")` not `sxRaised` (today both clean); native: `pinCrash`, exit class per OS. (2026-11-07, W1-z): the label is `sxRaised` with `witnessUnsafe` (the walker's Defect rule E6), never `sxUnsat` and never `sxSat`; `witnessUnsafe` is set on every crash claim, not only panics ones | s |
| W1-p | the three probe agreements without a pin: SND-07's `ua3_diff`, SND-12's `gc_shared`, INT-21's `ai_caught`, each ported with its native run | `tests/` only | each SUT's verdict matches its native run under `pinExact`; a disagreement becomes an F row, not a skip. (2026-11-07, W1-z): `ua3_diff` is conservative, not a native HIT (see SND-07) | xs |
| W1-b | local-pragma allowlist (`noinit`, `global`); every other local pragma declines `feLocalPragma` (W-02) | `dsl_parser.nim:19771-19792` | `gs = @[k]; var c {.cursor.} = gs; gs[0] = 9; if c[0] == 9: symexTarget("shared")` and its `let` twin: `sxUnknown` with `feLocalPragma` naming `cursor` (today a trusted false pair); `{.noinit.}`/`{.global.}` SUTs unchanged | s |
| W1-e | float width conversions decline `feFloatWidth` (W-04) | `dsl_parser.nim` :10658, :10845 | `let y = float32(x); if float64(y) == x: symexTarget("same")` and a hidden-conversion twin: `sxUnknown` with `feFloatWidth`; int↔float verdicts unchanged | s |
| W1-g | `x in a..b` / `notin` (W-31), in the infix list and, after template expansion, the `DotExpr` arm | `dsl_parser.nim:11070` | `if x in 0 .. 10 and x == 7: symexTarget("t")` `sxSat`, native 7; `notin`, `char` and enum slices | s |
| W1-f | object field defaults decline (W-20); `case` with `elif` (W-21) | `dsl_typebridge.nim` field walks (:646-650, the plain-record twin, tuple :1350-1356); `dsl_parser.nim` `case` sites :19259-19300, :10366, :5747-5821 | `type O = object; x: int = 5`, `var o: O; if o.x == 5: symexTarget("h")` compiles and declines with a named kind; `case x of 1: … elif x > 5: symexTarget("big") else: …` in all three forms: `sxSat`, native 6. (2026-11-07, W1-z): the field-default premise was wrong: native `var o: T` reads zero while `default(T)`, constructors and `new` apply the defaults, and the walker already agreed in every shape; W-20's compile stop was an empty `seq` default reaching the parser as a bare `[]`, fixed by lowering typed `seq` brackets as seq literals | xs-s |
| W1-d1a | `INT_MIN mod -1` and `low(int) div -1` (W-52) halt through `haltUndefined` (§9.1 item 2): eager capped check at the op, unsat to `logPrune`; the five `ub*` kinds declared contiguous with `UbKind` (unproduced ones allowlisted until K10a) | `runtime.nim` (:8862, `crashRaise` :25899), `types.nim` (+ lattice test); rewrites the trap pins in `s8aa_remainder`, `s8i_models` | `if x == low(int): (let q = x mod -1; if q == 0: symexTarget("t"))` not a trusted `sxUnsat` (today trusted; native hit); the `div` twin likewise; `except: symexTarget("c")` around it is not reached; the RED records paths and solver units on its SUT set against 0.9.1. (2026-11-07, W1-z): natively `low(int) mod -1` is SIGFPE on x86-64 and never reaches the label; the halt is still right because C leaves it undefined. Cost against 0.9.1: identical Z3 check counts, units unchanged on guarded SUTs, about 3x on the one SUT whose undefined side is reachable on a sat path | s |
| W1-d1b | unsigned division by zero: the `divByZeroConds` sink (`:1953`, drained at `:19026`) split so the unsigned zero side goes to `haltUndefined`; the opaque-call defect scan's `divMagics` (`dsl_parser.nim:4152`) answers "undefined", not `DivByZeroDefect` | `runtime.nim`, `dsl_parser.nim` | `let r = 10'u64 div uint64(k)`: `tRaisedExn("DivByZeroDefect")` not `sxRaised`; with `except DivByZeroDefect: symexTarget("c")` not a trusted `sxSat`; `r == 5` at `k == 2` stays `sxSat`; `if k != 0: …` keeps a trusted `sxUnsat`; native `pinCrash`, exit class per OS (`declined` cell). (2026-11-07, W1-z): unsigned div/mod by zero is SIGFPE natively while signed raises `DivByZeroDefect`; an opaque callee's unsigned division now forks no Defect and is not yet answered "undefined" (the opaque-scan "may be undefined" answer is §9.1 item 3, K10b) | s |
| W1-d1c | the call-cache side of the halt: a summary relying on a pruned undefined side is replayed only where the prune holds | `runtime.nim` (`pruneFactsSince` :18124, `pruneFactsHold`) | a callee holding the division, called twice under contexts where only the second admits zero: not a trusted `sxUnsat` | xs-s |
| W1-d3 | `Path.undefined: set[UbKind]` joined by every taint carrier; the `{.noinit.}` read recorded at the read site (`unwrittenKind` :9283-9293, `observeRecvPart` :20086); `Soundness.witnessUndefined` derived from the winner; `trustedSat`/`hostRunnable` require it empty; codec v4 (`soundnessMetaVersion`, `symex.nim:268`; `:345-370`; static pin `:320-333`) | `runtime.nim`, `soundness.nim`, `symex.nim` | `var x {.noinit.}: int; if x == 0: symexTarget("z")` with the slot forced to zero: `rsConfirmed` and not `trusted()`, not host-run; `var y {.noinit.}: int; y = 5; if y == 5: symexTarget("w")` stays trusted; a version-3 record decodes as a miss; a set with `ord ≥ 10` round-trips | s-m |
| W1-d2 | checks-off signed op declines on both routes (W-07): delete the push-marker early return (`runtime.nim:24500-24502`); one `buildWraps` predicate feeds `currentArithWraps` (:28471), `wrapScan` (:28722) and `offsetExact` (:28883), with `:28980`, `dsl_parser.nim:1474` and `canonicalize.nim:6513` consistent; `defaultSymexSettings` derives `arithChecks` from the build; an explicit disagreement taints `feCheckOption`; `tsymex_0016_checksoff.nim` + `.nim.cfg` `--overflowChecks:off` | `runtime.nim`, `symex.nim` (`warnIncoherentSettings` :3532); rewrites the opt-out pins in the 13 verdict-bearing files of the 21 that name `arithChecks` (listed in the handoff) | `{.push overflowChecks: off.}` `if v+1 > v: discard else: symexTarget("hit")`: not a trusted `sxSat` (today clean at `high(int)`; gcc folds it away); the checks-off cfg suite: the same with no push; `arithChecks = {acDivByZero}` explicit on a checks-on build: not trusted | *round*, s-m |
| K1-0 | the load-bearing property on Wave 1's cells: a `K1a-lite` join of `pinRecords` against the seven §5.0 keys, on c, cpp and Z3 4.13.4; fails if any of them lacks an `exact` or `declined` record per row | `tests/k1lite.nim` (new), run by `scripts/k1lite.sh` and wired into `.github/workflows/symex-linux.yaml` (2026-11-07, W1-z): the file was named `tests/tsymex_0016_k1lite.nim` here before it landed | with one §5.0 pin deleted, the join fails naming its key and row | xs |
| W1-m | the walker on MSVC before 0.9.2: a `fuzzer-msvc` step compiles and runs every `tsymex_0016_*` file with `--cc:vcc` against the installed Z3 4.13.4; `workflow_dispatch` with a `ref` input; a glob matching zero files fails | `.github/workflows/fuzzer-msvc.yaml` | the step fails on a planted red `tsymex_0016_*` file and on an empty glob, each shown by run URL; its log names `vcc` | s |
| W1-z | integration: final walker number and CR2 pin; three-way rows (0.9.1 / head / native) for every W1 row; the §5.0 rows and F-0001..F-0007 closed with their sha; `arithChecks` and `fromCache` `{.deprecated.}` with the path in the message (bare pragma on a field, (2026-11-07, W1-z): see §9.1 item 8); `docs/migration/0.9.2.md` with the bump, the new kinds, the new declines, the §2.4 known gaps plus §9's "after the label" gap and W1-c2's destructor gap, a **Compile breaks** section (the `ub*` kinds and `UbKind`, `feLocalPragma`, `feFloatWidth`, `Soundness.witnessUndefined`, the codec cold start, `--mm:refc` now an error, and the advice to add an `else` to any `case` on `SymexTargetKind`); `docs/symex/README.md`'s decline catalogue (`:381-395`) rewritten; UPS-01 and UPS-03 filed with URLs in §5.6; RFC-0017 records MOV-01's items | `canonicalize.nim:251`, CR2 test, docs | §5.6 holds two issue URLs; RFC-0017 names N20, OQ1, CRH-03's merge, `maxLoopUnwind`, #138 and the caps; a script check that the README names every Wave-1 kind | s |

**0.9.2's gate.** CI-A does not exist yet, so the release is gated by
`sweep.sh` on c, `sweep.sh -b cpp` and `sweep.sh -i z3-4.13.4`, all from a
worktree pinned to the W1-z sha, each diffed against the 0.9.1 release-asset
baselines (every flip is a Wave-1 row or accepted in the migration note), and
by K1-0 green on all three. Then the three Windows legs and the W1-m step
green at that sha, then `/wiring-audit` and `/code-review` to floor. Then
publication: `nelli.nimble` to 0.9.2 (milpa refuses a tag that does not match
the version), a `workflow_dispatch` dry run of `tianguis-publish.yaml`, the
`v0.9.2` tag pushed, and the registry entry checked. W-32's five syntax
declines (research A-06) are precision, not one of the seven, and move to
Wave 4.

**Wave 2 — the enforcing substrate, live from its first commit.** K5a comes
first, since every record after it carries the real profile.

| id | scope | depends | size |
|---|---|---|---|
| K5a | full `BuildSemantics`, `HostSemantics`, `BuildProvenance` with enums, `rowOf` with its justifications, `-d:nelliFwrapv` producing `-fwrapv` (§8.3); `SymexSettings` keyed by `fieldPairs` with a neutral `const`; one golden segment per run leg in CR2; the `dsl_parser.nim` assertion reads moved; readers migrated with no verdict change (INT-31's `\|bf=` half) | W1-c1b | m |
| CI-A1 | provisioning: the `2.2.10-linux-x64` Nim artifact (verify it is published first), Z3 5.1 from its release archive with `LD_LIBRARY_PATH`, PCRE 8.45 from source, cached (Ubuntu's 8.39 is unverified); a workflow that builds one file | — | s-m |
| CI-A2 | `sweep.sh --host`: the same runner without podman, writing `<log>.summary` in `sweep.sh:277-294`'s shape (§12 item 6); a derive mode for the whole `test` task (W-59) | CI-A1 | s |
| CI-A3 | `symex-linux` on every push over CI-A2; a committed known-red allowlist from one baseline run on the Ubuntu toolchain; a watchdog step that fails when the K8a heartbeat is over seven days old or an `rfc-0016-intake` issue is over seven days old with no F row | CI-A2 | s |
| CI-B | the same workflow on `schedule:` and on `workflow_dispatch` with a `ref` input: cpp, Z3 4.13.4 on Linux, `symex-msvc` (c, vcc) absorbing W1-m; baseline logs as artifacts with `sweep-diff.sh` in CI (CI-C, W-60); the 60 s ceiling (CI-D, W-60); `vm_alias_guard` over a sampled corpus slice (the parser-VM cell, §2.5); a red run opens or updates an `rfc-0016-intake` issue. W-63's JIT PCRE row closes against the Windows legs (PRC-27) | CI-A3 | m |
| K9b | migrate the 35 `nativeHits` copies and the `declines` templates that already name a kind onto K9a's verbs; no retype (keys are `CellKey` from K9a) | K9a | s |
| ADM-1 | (from Wave 1's parallel worktree) `smt/admission.nim`'s `Admit`, `Row`, `AxisTable`; `feUnadmitted` (`dcNoAnswer`); `varParamMagics` and `verifiedLibs` (as `admitPcreLib`) moved onto it with no verdict change, and `ensureProcRegistered` taking an `Admit` (the second-consumer spike, §8.1) | K9a | s-m |
| K2-s | read-only census script: every `case n.kind` in `src/nelli`, every `Survivors(`/`Degrade(` literal, every bare `skip(`; prints counts, gates nothing yet | — | xs |
| K1a-cells | `tsymex_0016_universe.nim` (registered): cells of ADM-1's axes and the build rows; the error-kind and cap-kind derivations; the record join; allowlists under `tests/0016-allowlist/`; the committed `0016-universe.tsv` diff | ADM-1, K9b | s-m |
| K1a-ids | `docs/rfc-data/0016-worklist.toml` from §5, §5.9 and the F ledger; `scripts/render_worklist.nim` and the staleness check; the id join and `ids.txt` | K1a-cells | s-m |
| K1a-last | `sweep.sh` runs the universe test last over the sweep's record directory and fails on an empty one; the per-row seven-day freshness check | K1a-ids | xs |
| K1a-ci | post-shard join on each leg: record upload steps and a join job in `symex-mingw.yaml`, `symex-linux` and CI-B's; planted RED shown on each leg by run URL | K1a-last, CI-B | s-m |
| K7a | `Survivors` with `halted`, `surviving`, `continued`, `exact`; `CapKind` with one site per member; the 20 `discard w.degrade(` sites in their four shapes (§8.4) | — | s |
| K7b | `walkUnsupported(…): Survivors`; `feUnadmitted` to `dcOmitted`; W-11, W-16 | K7a, ADM-1 | s |
| K2-0 | the probe batch, one probe each and a row or `never` record from each: SND-13, CRH-06, CRH-08, CRH-09 (with W-22's `parseBool` hang and W-24's `filterIt` fault), INT-11, INT-12, INT-15, INT-22, PND-13, W-19b, W-19c | K9b | m |
| K9d-0 | the first pins through `symexForAll` and the concolic path (one per entry point), so §10's six entry points each have a record before Wave 3 | K9b | s |
| K8-0 | `annotationViolations` gets its reader (INT-33; K8a's second source) | — | s |
| K8a-gen | the generator: one family (§5.0's construct shapes), boundary domains, metamorphic twins for that family | K9a, K8-0 | s-m |
| K8a-job | a scheduled Linux job rotating one build row per night, `workflow_dispatch` with `ref`, a last-tag checkout filling the three-way release column, a dated heartbeat | K8a-gen, CI-A3 | s |
| K8a-sink | the triage sink of §10: a disagreement reduced, keyed by cell, filed as an `rfc-0016-intake` issue | K8a-job | s |
| S8cj | carried: thread-history spend; Z3 mk_unique (D-0016-3 waits on it for UPS-02) | — | m |
| W2-z | integration: CI-B and K8a dispatched at the integration sha and green, run URLs in the handoff; the record directory of each leg nonempty; the universe test's cell, SUT and verdict counts nonzero and in the handoff; the CI-A3 watchdog green | all of Wave 2 | xs |

**Wave 3 — the tables.** Each introduces its axis under §8.2's rule, adds its
fuzzer family, shrinks its allowlist, and switches its pins to the checked
`CellKey` constructor.

| id | scope | depends | size |
|---|---|---|---|
| K2a | dispatch census as a test over K2-s's counts, with an allowlist: the construct axis's `case n.kind` sites, the `skip(` and platform arms without `skipCell`, the `Survivors(`/`Degrade(` literals (AUD-09) | K1a-cells, K2-s | s |
| K2b | float width conversions exact (`fp.to_fp`, RNE) | K2a | s-m |
| K2c | child-shape census corpus with one snippet per `NimTypeKind` (includes CRH-01's remaining `classifyType` stops) | K2a | m |
| K3a | the type-class axis (`admitTypeClass`, §8.1) and the type × memory-op axis under `typeCopiedByValue` and `holdsSharedMemory`; STY-04 and STY-06's type cells (*round*) | ADM-1, K1a-cells | m |
| K3b | object field defaults exact (`wasMoved` stays bitwise zero) | K3a | m |
| K3c | the pragma axis's three lists (local, routine/param, type); `union`, `packed`, `byref`/`bycopy` decline until modelled | K3a | s-m |
| K4a-table | the magic axis's rows, keyed by name; the lib-wide guard; STY-05. (2026-11-07, W1-z): ADM-1 declares the `vsArm` site but nothing consumes it until here | ADM-1 | s |
| K4a-dispatch | `dispatchMagic` per site, the four sites (`unsignedIntOps` first); the once-per-site registry RED | K4a-table | s-m |
| K4a-guard | the opaque-call defect scan reads the axis | K4a-dispatch | s |
| K4b | an unadmitted bodied magic declines (*round*) | K4a-guard | m |
| K4c | stdlib-body axis with check-option deltas; STY-02 and STY-06's stdlib cells; W-47; AUD-11 (*round*) | K4a-guard, K2-0 | m |
| K5b | refusals (32-bit, big-endian, unverified Z3/Nim/PCRE, no `rowOf`, arm64, macOS, `-d:nelliFwrapv` under `vcc`); the stock-Nim corpus slice; cfg suites for `--mm`, `-d:useMalloc`, setjmp, `-d:release`, `-d:nelliFwrapv` (W-58); the per-build memory pins (W-51); STY-01, STY-08, AUD-01 and refc as `never` cells | K5a | s-m |
| K6a/b/c | `mayWrite` into `nodeWritesHeap`, the hook copy-proof, then `ptrUsesStayLocal`/`routeStoresThroughDeref`/`bindsViewWhole` (*round* each) | ADM-1 | m each |
| K10a-target | `stkUndefined`, `tUndefined`, `UndefinedFinding`, `FindingUndefined`; replay refusal by target kind | K7b | s |
| K10a-axis | the definedness axis with `noalias` as an `OperandClass`; STY-03, STY-07; unproduced `ub*` kinds leave the allowlist | K10a-target, K5a | s-m |
| K10a-float | float-to-int to `haltUndefined` (*round*) | K10a-axis | s |
| K10a-concolic | the concolic flip solve carries the definedness disjunction | K10a-axis | s |
| K10b | whole-run definedness (§9.1 item 3): the parameterised `scanOpaqueDefects` and the second walk under the witness's choices; the 0.9.2 known gap closed; a perf figure on the K10 SUT set (*round*) | K10a-axis, K4a-guard, K4c | m |
| K10c | UBSan pin suite (Linux); a one-off build with `-ffp-contract=off` pinned against the default; declared Windows cells | K10a-axis, CI-A3 | s |
| K10d | `arithChecks` and `fromCache` removed; `docs/migration/0.10.0.md` (`SymexErrorKind` deletions and additions, `stkUndefined` and the `case` sites it breaks, `Soundness.buildSegment`, the cache cold start, the `Admit`-taking IR constructors) | K10a-axis, K5a | s |
| PRC-01/02 | Windows re-exec replay: marshal case-object, `ptr`/`ref`, proc-value, `method` and `{.global.}` witnesses (the first precision item; consumers' main platform) | — | m, m |
| W3-z | integration, as W2-z, plus: every axis has at least one `exact` cell with a record on each of its claimed rows, and its allowlist is shorter than at its introduction; the 0.10.0 publication steps of 0.9.2's gate | all of Wave 3 | xs |

**Wave 4 — the search, then the tail.**

| id | scope | depends | size |
|---|---|---|---|
| K8b | fuzzer families per axis and per family (`faCallShape`, `faExnMemory`, `faGeneric`); metamorphic relations (§10) per family; the pairwise figure with its floor in `tests/0016-pairwise.floor`; cells-exercised records read by K1 | K8a-sink, Wave 3 | m-l |
| K8c | the walker under sanitizers: a scheduled job runs a slice of the corpus with nelli built under ASan, since a use-after-free in a Z3 AST can produce a wrong verdict, not only a crash (CRH-07) | CI-B | s |
| K7c | every `walkStmt` arm returns `Survivors` (§8.4) | K7b | m |
| K9c | the 132 decline assertions with no kind: each kind found by running it (W-56) | K9b | m |
| K9d | pins for the 481 verdict suites with no native idiom, generated by family where the SUT is a pure proc (W-54) | K9d-0 | l |
| K9e | pin strength: a mutation run over `runtime.nim`'s arithmetic and raise arms (operator swaps, dropped forks) reports the share of mutants some pin kills; the figure and its floor committed | K9d | s-m |
| K2a-fail | K2a's `skip(` census fails instead of listing, ratcheted | K9c | xs |
| H1 | hygiene: W-62, W-65, W-66, W-67, W-68, AUD-03, AUD-06, AUD-07 (to `faGeneric`), INT-19, INT-20, INT-26, CI-01's remainder | — | s |
| W-32 and the precision rows | §5 and §5.9 precision rows in the research list's frequency order; the VM column; witness round-trip pins | — | per row |
| W4-z | the allowlists emptied; §12 checked item by item, each with its producing slice's evidence | all | s |

**Carried slices.** The pending `[[slice]]` rows from RFC-0005 map here:
S8cj to Wave 2 (above); `rv0005-lows` loses INT-31 (K5a, and its `;impl=`
half stays with the row) and INT-33 (K8-0) and keeps the rest for Wave 4;
S8ck-r (nim-z3 hygiene, INF-04), S8cg, S8ch, S8ci, S8co and S8cp-r are Wave 4.
INF-04's item 10 ("do not file") is superseded by D-0016-3: UPS-03 is filed
in W1-z.

## §12 — The finish line

Decision D-0016-1 closes the RFC when the work list is empty. This section is
how "empty" is measured, so that it is a test result and not an opinion. Each
item names the slice that produces it.

1. `tsymex_0016_universe` is green with **every allowlist empty** on every
   build row with a run leg (Linux c, Linux cpp, Z3 5.1 and 4.13.4, mingw,
   MSVC), each over a record directory dated within seven days: no
   unclassified cell; every `exact` cell has a pin record from a public
   entry point (§10's six) on each row it claims; every `declined` cell's pin
   asserts its kind; `sampled` unsat cells counted separately from
   exhaustive ones; every `CapKind` and `SymexErrorKind` covered. (K1a-cells,
   K1a-last, K1a-ci; the legs from CI-A3 and CI-B; emptied by Waves 3-4,
   checked at W4-z.)
2. Every row of `docs/rfc-data/0016-worklist.toml` is closed, merged, moved,
   owned elsewhere, or `never` with a `NeverReason`; no `iModel` decline
   remains (a declined-for-now cell is open work); the ids allowlist is
   empty. (K1a-ids; every fixing slice.)
3. No failing file on any gate; no bare `skip(` or platform arm without
   `skipCell`; no decline assertion without a kind. (K2a, K2a-fail, K9c.)
4. The fuzzer has exercised every exact row on its build rows, the pairwise
   figure is at or above `tests/0016-pairwise.floor` (which only rises), and
   the pin-strength figure is at or above its floor. (K8b, K9e.)
5. **No precision regression bought the empty list.** The committed
   `docs/rfc/0016-universe.tsv` only gains `exact` cells; a cell that leaves
   `exact` is named by a work-list row in the same commit. Before an axis
   exists, the Wave-1 three-way rows and each wave's `sweep-diff.sh` against
   the 0.9.1 release-asset baselines measure it. (K1a-cells; W1-z; W4-z.)
   `sweep-diff.sh` alone cannot: it diffs pass/fail per file, so a pin
   rewritten from exact to a decline passes.
6. The certifying gate logs carry their `.summary` sidecars: CI-A2 emits the
   same shape `sweep.sh` does (`scripts/sweep.sh:277-294`). (CI-A2.)
7. **Cost.** Each leg's suite wall time is within 25% of its 0.9.1 figure,
   any excess named by a work-list row; no single file over CI-D's 60 s
   ceiling; each workflow under its minutes cap. (CI-B, from the pin
   records' path and solver-unit counts.)
8. **Docs.** `docs/symex/README.md` names every `SymexErrorKind`, every
   `UbKind` and every `NeverReason`, checked by a grep in K1. (W1-z, K10d,
   W4-z.)

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
  possible (§8.3). `-fwrapv` is produced from `-d:nelliFwrapv` instead; the
  compiler version is a run-time fact of the pin record.
- **`-d:nelliFwrapv` as a recorded assumption** (`assumptions = {vaSignedWrap}`
  on `Soundness`, round 3): not needed once the define produces the flag, so
  the verdict depends on no unverified claim.
- **Pin file and RFC ids on `Cell`** (round 2): moved out of `src/` in
  round 3. The pin record is the only link from a cell to its test, and the
  RFC row names its cell.
- **A `bool` for `witnessUndefined`**: replaced by `set[UbKind]`, which
  renders which undefined behaviour and is still one field.
- **A hand-annotated ledger reconciled against the code**: replaced by §8.2's
  generated ledger.
- **A new `sxUndefined` status**: replaced by a target kind, a halt kind and
  `witnessUndefined` (§9.1), with no status break.
- **Refusing checks-off and `-d:danger` builds**: rejected per D-0016-9.
  Those are consumer builds; the walker models them (§9) or declines by cell.
- **Always producing `-fwrapv`**: it would change the consumer's program
  semantics behind their back and still leave `div -1` undefined. It stays
  opt-in through `-d:nelliFwrapv`.
- **A second solver or a proof check for every `unsat`**: partly taken. The
  Z3 4.13.4 row re-decides every query on a second build (§2.5), and a
  disagreement found by any route is re-decided by cvc5 during triage. A
  per-query proof check (Z3's proof objects, or a second solver on every
  query) costs more than the whole walk on the deep suites.
- **Metamorphic testing (EMI)**: adopted in K8a-gen and K8b (§10).
- **Mutation testing of the pins**: adopted as K9e.
- **Generating only UB-free programs** (Csmith's discipline): rejected for
  the fuzzer, whose job includes finding the undefined ops the walker
  mishandles; the generator tags each program's expected `UbKind` instead.
- **An IR interpreter as a third column** beside the walker and the native
  run: deferred. It would separate parser from walker bugs in triage, but
  the native run is the ground truth and K8's reduction already localises.
- **`admittedExact` and a regex over the RFC markdown** (round 3): replaced
  by plain `exact` with K2's literal census, and by the TOML work list
  (§8.2).
