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
state    = "open"
owner    = "corey"
kind     = "design"
reversible = "reversible"
recommendation = "exit-criterion.A"
lean     = "A gives a stated, measurable bar that shrinks only when search stops finding things; the figures are a starting point and can be revised without changing the shape."

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
state    = "open"
owner    = "corey"
kind     = "risk"
reversible = "one-way"
recommendation = "upstream-reports.B"
lean     = "File the Nim and spacer reports, which have reductions; hold mk_unique until S8cj reduces it, since the sort did not reproduce it at e497dcf."

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
state    = "open"
owner    = "corey"
kind     = "design"
reversible = "reversible"
recommendation = "fork-c-clean-replay.A"
lean     = "The blockers were trusted verdicts on clean paths; a replay gate would have refuted the false sxSat half of them, at a run-time cost a setting can switch off."

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
state    = "open"
owner    = "corey"
kind     = "design"
reversible = "one-way"
recommendation = "fromcache-field.A"
lean     = "Removing it breaks every caller that reads it and gives no user anything, since it already reads false; keep it until a symexFind cache gives it a producer, or remove it then if that cache never comes."

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

[[slice]]
id    = "D1"
title = "Differential fuzzing harness: generated SUT shapes, walker against native execution, exhaustive small domains (§4)"
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
+++

# RFC — native-parity hardening: the walker agrees with the compiled program, or declines

- **Status:** in-progress — opened 2026-11-02 when Corey split RFC-0005.
  RFC-0005 ends at the 0.9.0 tag, once every open soundness item that is
  worse than `main` (6cbfe8f) is fixed. Everything else moves here: soundness
  items with the same severity as `main`, precision gaps, crashes and hangs
  that match `main`, CI and test-time work, and the exact models behind the
  declines RFC-0005 added. Nothing was dropped. This RFC is open-ended: it has
  no fixed slice list, and it is tracked by the rate of new findings (§3). The
  exit criterion in §3.3 is a proposal, **awaiting Corey** (item `exit-criterion`).
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

### §3.1 Open-ended, tracked by findings rate

RFC-0005 was tracked by a slice list that grew by remainders: each slice
reported what it found and did not fix, and that became the next slice. The
list never shrank. This RFC accepts that and tracks the thing that should
shrink instead: **the rate of new findings**, above all new soundness findings,
per unit of search effort.

The unit of effort is a CPU-hour of the differential fuzzer (§4), once it
exists. Until then it is a calendar week, and the rate is reported as found
per week with the source of each finding (slice, consumer, review, fuzzer), so
that a quiet week with nobody looking is not read as progress.

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

### §3.3 What "done" means — **proposal, awaiting Corey**

Every listed item closed is necessary but not sufficient, because the list is
open-ended. The proposal:

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
- **Where it runs.** On the worker (`nelli-work`) at first, then as a
  scheduled CI job on a Linux runner, which also gives the cpp leg in CI-02 a
  home. It does not run on every push.

### §4.3 What it is not

It does not replace native pins in slices: it finds shapes, and the slice that
fixes one still pins it. It does not test replay against real effects (quit,
foreign threads, files); the generator keeps SUTs effect-free except for
memory, unless a generator family for effects is added deliberately.

## §5 — Work list

Owners are left empty: the coordinator assigns them. "Moved slice" means a
job file on `origin/worker-jobs` written under RFC-0005; it keeps its id and
its scope, minus anything named as staying with RFC-0005.

### §5.1 Soundness, same severity as `main`

All are false verdicts on `main` 6cbfe8f and on the channel at e497dcf (sort,
"Same on both"). Several have a fix that landed in RFC-0005 batch 10 or is due
in batch 11; for those the item is to re-pin natively at the tag head and close
it, or reopen it if the fix did not hold.

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| SND-01 | Direct var-returning actual: `rab(t["a"], t, "a")` | sort S1; S8cq item 2 | false pair on both; native `r == x+1` HIT (`p_cq vc_*`). S8cn's report lists the same false pair on both. S8cq (batch 11) may close it | |
| SND-02 | `$` of a negative int: `$x == "-5"`, `($x).len == 2`, `$x == ""`, `repr(x)` | sort S2; S8cb | false on both (`p_cb`). S8cb records it fixed (batch 10): confirm at the tag head | |
| SND-03 | `$` of a char: `$a == "a"` false `sxUnsat`, `$a == "97"` false `sxSat` | sort S3; S8cb | as SND-02 | |
| SND-04 | `$` of an enum, including a string-named enum | sort S4; S8cb | as SND-02 | |
| SND-05 | `ensureMove` of an int: `b == 0 and x != -1` false `sxSat` | sort S5; S8cb | `p_cb em_dead`. S8cb's model won at batch 10: confirm | |
| SND-06 | `procCall` zero value: `r == 4 and k != 3` false `sxSat` | sort S6; S8cl | `p_cb pc_dead`. S8cl makes it decline (batch 10): confirm the decline; exact model is PRC-21 | |
| SND-07 | `uncheckedAssign`, the other arm's bytes differ: `o.y != v` | sort S7; S8cp item 2 | `main` false `sxSat`, channel false `sxRaised` (`p_cp ua3_diff`). S8cp item 2 is a batch-11 requirement and may close it | |
| SND-08 | A hook write through a local ref: `DR(r: r)`, `=destroy` writes `d.r[]` | sort S8 | false pair on both; native `r == 1` HIT (`p_cp dg2_*`). No owner. S8cs covers global write routes only | |
| SND-09 | A hook on overwrite, global written first: `gW = 0; var d = mkD(k); d = mkD(k)` | sort S9 | false pair on both; native `==1` HIT (`p_hook2 w2_*`). Check whether S8cs's fail-closed routes cover it at the tag head | |
| SND-10 | PCRE stop code read as a match: `s.match(re"(a|a)*[bc]")` at `a^30` | sort S10; S8cf | false `sxUnsat` on both (`p_cf cf_match_hit`). S8cf (batch 10) records the fix: confirm | |
| SND-11 | PCRE stop code as a witness: `not s.match(...)` at `a^30` | sort S11; S8cf | false `sxSat` on both (`p_cf cf_miss_long`). As SND-10 | |
| SND-12 | `let` cursor over a shared global: `gc_shared` | S8cn blocker probe 1 | `sxUnsat` with a native hit on both shas (`s8cn-blocker/s8cn_release_blocker_probe.{6cbfe8f,e497dcf}.log`). S8cn's let-over-written-seq decline should cover it; not re-run on bb1031c | |

### §5.2 Precision

**Replay and witnesses.**

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-01 | **First precision item.** Windows re-exec replay: marshal case-object and `ptr`/`ref` witnesses instead of declining. Windows is a consumer's main platform, so a decline there is a decline in daily use | S8ct (coordinator ledger, 2026-11-02) | S8ct moved replay to a child process; on Windows a witness of these kinds declines with a named reason, documented in the 0.9.0 migration note and pinned on Linux by the re-exec pin | |
| PRC-02 | Windows re-exec replay: proc-value, `method` and `{.global.}` witnesses decline | S8ct | same mechanism as PRC-01; after it | |
| PRC-03 | Replay cannot aim a witness `ptr` at a global: S8cr's three open holes | S8cr; batch 10 integrator | the three open-hole pins give `sxUnknown` (`feGlobalHavoc`, `feReplayRefuted`), not `sxSat`; the false `sxUnsat` is closed, the precision is not | |

**Exact models for RFC-0005's declines.**

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-04 | Inventory every decline RFC-0005 added or widened, and give each an exact model or a recorded reason it stays. Generate the list from the code (decline sites and `SymexErrorKind` members, 6cbfe8f against the tag), not from memory. Known families to seed it: S8cq's by-value allowlist (types where Nim's copy behaviour varies); S8cs's fail-closed global write routes (hooks, opaque routines behind a local alias, `{.emit.}`); S8ct's replay declines (quit, nil deref, unbounded recursion; W1, W2); S8cu's check-option source scan; S8cl's "magic with no body declines"; S8cf's past-safe-length `zsUnknown`; S8ca's `viewFollows` "any other write declines"; S8bk's `feEvalOrderUnmodelled` late address | Corey's split, 2026-11-02 | decline-before-verdict was the release fix for most blockers (ledger, 2026-11-02 entries); each decline is sound and costs precision | |
| PRC-05 | S8cn's declines, each to an exact model with native pins: a `lent` loop with a possible write, and a `let` cursor; a by-value actual reached by name, reads included (b9 `sReadOnly` now `feUnsupportedOp`); non-scalar `pairs` and array `items`; a `let` over a formal with any ptr or ref write; a `var`, parameter or computed proc value with a view and a Table (`closureTakesView`); by global name (`sqG`, `gw`); `f(s[i], s[0], s)` and `f(s[0], s[0], s)`; a pointer plus a Table call; a mutated local copy; `t.clear` and `t.pop`; `Table[string, VObj]`; a non-scalar by-value view; `nl2_other_live`, `nl2_same_dead`; two-entry `del` (hash-dependent); the ds, dt, dv forms | `worker-reports/s8cn.md` "Declines for RFC-0016" | listed by S8cn as precision; `let c = s` varies across 9 build settings (ledger), so the model must be per build or stay declined | |
| PRC-06 | The `ti_grow` Table `keys` loop that writes the Table, even with no key added: `ti_grow` at `a == 0` is now `sxUnknown`, moved from S8bl's `sxSat` | S8cn | repin accepted at batch 11 intake | |
| PRC-07 | S8cu: exact unchecked semantics — model what a routine compiled with a check off actually does (overflow, bounds, range, field, nil, float checks), instead of the source-position decline | S8cu | S8cu's fail-closed decline (`feCheckOption`, `feOverflowCheckOption`) closed a false `sxRaised` | |
| PRC-08 | S8cu: a `-d:danger` or `--fieldChecks:off` build declines every routine | S8cu | follows from the source scan; depends on PRC-07 | |
| PRC-09 | S8cu: `math.nim`'s pushed regions now decline | S8cu | every routine in a pushed region of `std/math` declines | |

**Shapes and magics.**

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| PRC-10 | `lastIdx`: a query SAT only past the cap declines; lift the cap past 8 | S8cd item 6 (S8k) | `t.len > 10` under a cap of 8 has no model within the cap; a leaf equal to a leaf equal to a literal still takes the cap | |
| PRC-11 | `len` of a nested seq: a `seq[seq[int]]` heap field, or a proc value's result of that type | S8cd remainder | declines on the unsupported nested element representation; last probed at 136ad60 | |
| PRC-12 | `HashSet[string]` behind a pointer or in a heap field | S8cd remainder | declines; last probed at 136ad60 | |
| PRC-13 | `f != nil` on a proc value with no lambda the walker built | S8cd remainder | `ceUnsupportedHof`; last probed at 136ad60 | |
| PRC-14 | `addr o.xs` bound by a `let` | S8cd remainder | `heUnsafeCast`; last probed at 136ad60 | |
| PRC-15 | A case object reaching a heap cell, as a global | S8cd item 3 | no entry-value model; declines (`recvValue` reads it at its type) | |
| PRC-16 | `zeroMem` and `copyMem` on `addr x`: a walker fault (`FieldDefect` reading `ptrPointeeTy` of an `itUninterp`). First make it a named decline, then model it | S8cl remainder | in-band, but a fault rather than a named decline | |
| PRC-17 | `alloc0` behind a cast | S8cl remainder | `heUnsafeCast` | |
| PRC-18 | `create` | S8cl item 2; sort S12 | a compile stop on both at e497dcf; declines since S8cl (`formalsReadable`, `create`'s `size = 1.Positive` has no type) | |
| PRC-19 | `new(p, finalizer)` | S8cl item 1 | declines | |
| PRC-20 | `GC_ref` (and an object with a `when` member, which `GC_ref` reaches through `RefHeader`) | S8cl item 2; sort S12 | compile stop on both at e497dcf; the type bridge now leaves a `nnkRecWhen` member unsupported | |
| PRC-21 | `procCall` exact model | S8cl item 1; sort S6 | declines since S8cl (empty magic body) | |
| PRC-22 | A `type` section in a SUT or routine body | S8cl remainder; S8cb remainder; S8cp item 7 | declines | |
| PRC-23 | A nested `s[gi]` of a seq of seqs | S8cl remainder | declines | |
| PRC-24 | `alt_miss`: `s[s.len-1]=='c' and not s.contains(re"(a|a)*b|c$")` | sort B14; S8co item 10 | `main` correct `sxSat`; S8cf gives `sxUnknown` (`beSolverUndef`) where e497dcf was false (worker-sls2 57899a16). The blocker is closed; the precision against `main` is this item. Batch 10's integrator was to add a native pin and check with a longer budget that it never decides `sxUnsat` | |
| PRC-25 | Concolic scratch solves run without limit sites | batch 10 integrator | guidance only so far; no verdict observed wrong | |
| PRC-26 | `nsc_dead` returns `beSolverUndef` | batch 10 integrator | solver undef rather than a decided `sxUnsat` | |
| PRC-27 | `bt_limit_replace` weakened to sat-or-decline on Z3 4.13.4 | batch 8 integrator | precision loss recorded at batch 8, not assigned to a slice | |
| PRC-28 | S8cq item 4: `inc(gs[nextI()])`, `inc(getV())`, `swap(gs[nextI()], x)`; a read-only by-value global through a proc value (`pr`); `addr` of a global in a walked callee (`wp_dead`, `heUnsafeCast`); `unsafeAddr` of a by-value array formal in a walked callee | S8cq item 4 | the coordinator released it to this RFC if it would delay batch 10; the last two bullets are S8ch's items | |

**Moved slices (precision).** Each keeps its job file's scope; the rows below
name what moves and what stays.

| ID | Slice | Moves | Source | Owner |
|---|---|---|---|---|
| PRC-29 | S8cg | items 2 (copy a `var openArray` view at the call, so `fill(gArr, bumpA())` decides), 3 (a later argument that only reads a global counts as a read), 4 (`ti_tuple` exact `sxSat` under default budgets), 5 (`bb_rep_sym_empty_hit` exact on both Z3 versions), 7 (an index call through a proc value), 8 (timing of `r6_b6_optionregion` and `s8bb_constructs`). Items 1 and 6 were closed by S8ca and S8by | `jobs/s8cg.md`; batch 7 note | |
| PRC-30 | S8ch | both items: the address of a global in a walked callee halts the path; `unsafeAddr` of a by-value array formal declines | `jobs/s8ch.md`; S8cc remainder | |
| PRC-31 | S8ci | all six items: a term order that earns its cost or none; `r4_strip` within 10% of S8bm; a behavioural pin for the order; `configdefaults_depth` under 60 s without lowering the depth; wide factoring decided again; the skip's real saving. Also batch 9's addition: `ti_tuple`'s SAT search 79.8M to 411.8M units on 4.13.4, so `tupleBudget` 300M to 600M | `jobs/s8ci.md`; S8by remainder | |
| PRC-32 | S8cj item 1 | a fresh thread's spend on a query follows what earlier threads ran (72,124 to 5,854,994 units on Z3 5.1); correct the "function of the query alone" claims from S8bm and S8bp. Item 2's trust question is in §5.7 | `jobs/s8cj.md`; S8by remainder | |
| PRC-33 | S8co | items 3 (auto-possession with a property or XCLASS), 4 (kept `ignore_skip_arg` under a limit), 5 (`detect_repeat` group repeats on the JIT, 400 calls skipped), 6 (SKIP:NAME past 100, languages past 7), 7 (symbolic `(*ANY)` under the JIT scan, 72+ differences when lifted), 9 (`replace`'s unmarked SKIP:NAME, `first` in UTF, `count` of `set[char]` and overlapping counts), 10 (unbounded no-match refutation past `limitReach`'s safe length, with PRC-24). Items 1, 2 and 8 are in §5.7 | `jobs/s8co.md`; S8cf remainder | |
| PRC-34 | S8cp item 7 | declined shapes: whole-tuple `==` (`eqBV`); a local `let b = addr o.y` alias on whole assignment; a type section in a routine body (with PRC-22); a parameter pragma `x {.inject.}: int`, a compile error in `collectStringBackedByteSeqParamsImpl`, to fix first; nested `addr t[1][0]`. `s[1].b = 7` and `s[1][0] = x` only if S8bz left them declined | `jobs/s8cp.md`; S8cb remainder | |
| PRC-35 | S8cp item 8 | declined magics: `math.toInt`, a holey enum's invalid value, `=dup` of an object or tuple through its hook, `$float`, the remaining `repr` shapes; stop only where the theory cannot express it or the cost is measured out of budget, with the number | `jobs/s8cp.md`; S8cb item 5 remainder | |

### §5.3 Crashes, compile stops and hangs

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| CRH-01 | Compile stop on a `sort` callback: `s.sort(proc ...)` | sort S13 | compile stop on both; runs natively (`p_havoc2 a15`). S8cu is collecting both columns again; if it confirms SAME, it stays here | |
| CRH-02 | Compile stop on `create` and `GC_ref` | sort S12 | compile stop on both at e497dcf; S8cl turned both into declines at batch 10. Confirm at the tag head; models are PRC-18, PRC-20 | |
| CRH-03 | A ref-local merge runs out of memory and is killed | S8ct | an OOM kill that matches `main`; earlier measured as a 250 s merge, and a silent exit at 300 merges under audit. Bound it to a decline within budget | |
| CRH-04 | A regex literal of 2600 nested groups | S8ct | assigned here by the coordinator (2026-11-02); bound the parser's recursion and decline | |
| CRH-05 | A pointer plus 11 Table inserts ran past 1400 s | S8cn | liveness; the pin uses one insert | |

Two latent crashes are not settled and sit in §5.7: the `byteLeafIds`
segfault (PND-04) and probe p7's rc=139 (PND-05). If the pre-tag disposition
does not settle them, they move here.

### §5.4 CI and test time

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| CI-01 | S8cm: corpus files over 60 s of compile plus run on Windows, and shard budgets (no shard's typical time above 30 of 40 minutes). **S8cm is running and may finish before the tag**; if it lands on RFC-0005, it keeps its row there and this item tracks only what it leaves (the files listed after it started: `b10_integration` 107 s, `s8cd_setorder_large` 102 s, `_small` 100 s, `s8cn_views_c` 121 s, `s8bq_remainder` 91.4 s, `s8cr_intro` 60.2 s, `s8cd_globals`) | `jobs/s8cm.md`; ledger entries for batches 9-10, S8cd, S8cn, S8cr | `symex-mingw` run 41516396577 table; shards at 37.3 and 36.7 of 40 min at e497dcf | |
| CI-02 | A permanent cpp CI leg. No leg runs cpp today; n42 and n43 broke on cpp for several batches unnoticed (sort B21). Also run Z3 4.13.4 on a schedule: until now batch gates were c on Z3 5.1 only, and full 4.13.4 and cpp sweeps run only at the release gate | S8cl item 5; sort B21; ledger (release gate) | `fuzzer-msvc.yaml` records why cpp/MSVC was removed; a Linux cpp leg has no such obstacle | |
| CI-03 | `s8by_remainder`'s units check is not deterministic under load | S8ct | red on a loaded host, green on the worker at e497dcf | |

### §5.5 Infrastructure

| ID | Item | Source | Evidence | Owner |
|---|---|---|---|---|
| INF-01 | The differential fuzzing harness (§4), slice D1 | coordinator ledger, S8cq blocker (2026-11-02) | every sort blocker was found by hand | |
| INF-02 | Fork (c): a gated clean replay as a safety net, which would catch a false `sxSat` on a clean path. **Awaiting Corey** (item `fork-c-clean-replay`) | RFC-0005 "the open fork (c) below" (line 1667 at 67f0b622; the DoD audit cited it at 1615); DoD audit fork 2 | the fork was never written down in RFC-0005; this is its first record | |
| INF-03 | The findings ledger and a weekly rate report (§3.2) | this RFC | none yet | |
| INF-04 | S8ck after item 1 (slice S8ck-r): items 2 (`Z3FuncDeclOwn`, `Z3FuncInterpOwn`, `Z3RcfNum` hooks never release `ctx`), 3 (`Z3Ast[S: static]` hooks unused for `Z3Int`/`Z3Bool`), 4's version half (`tffi`, `tversion`, `tmultiversion` assert a 4.x runtime), 5 (`injectShapeFault` comment), 6's first half (ADR-0023's "a lowering-time degrade must never raise", keep or simplify), 7 (`s8s_precision` run wall 13.2 to 19.1 s on Windows), 8 (`examples/properties.nim:30`, examples in nim-z3 CI on c and cpp), 9 (a leak gate that fails on invalid reads, writes and frees, shown RED on a planted bad `dec_ref`), 10 (record and reduce the spacer read; do not file), 11 (generated seq hooks on the raise path release every element), 12 (separate real leaks from live globals, `trcf`'s 26 `Z3ContextOwn` blocks). Item 4's hang half and item 6's second half are in §5.7 | `jobs/s8ck.md`; `worker-reports/s8ck-item1.md` | item 1 closed: cc5ffc9 identical to ae509f0 on invalid accesses and leaks | |
| INF-05 | Audit the older "Different mechanisms, reported and not fixed here" lists against the remainder chain. This document took the lists of slices landed through batch 10 whose remainder has no later slice (S8ca, S8by, S8cc, S8cf, S8cb, S8cd, S8cl, S8cn) item by item. The earlier lists were each carried into a remainder slice whose job said "defer nothing", but no one has checked that every item reached one | RFC-0005, about 80 such lists | **done 2026-11-03** (owner audit of the lists of 72 slices, S8c, S8e/S9 and S8g through S8bt, plus the inline not-fixed notes in S8y, S8ah, S8ao and S8bk): 318 rows fixed, 17 owned by RFC-0005, 9 already owned here. The 13 unowned rows (11 distinct items) are filed in §5.8 as AUD-01 to AUD-11 | |

### §5.6 Upstream reports — awaiting Corey

Outward-facing; none is filed. Each needs Corey's decision to file (item `upstream-reports`).

| ID | Report | Source | Evidence | Owner |
|---|---|---|---|---|
| UPS-01 | Nim: a raise-path destroy (a destructor swallowing an in-flight exception on the C backend) | S8ce | reduction at worker `s8ce-work/probe/purenim.nim`, condensed in `worker-reports/s8ce.md` | |
| UPS-02 | Z3 5.1: `Failed to verify: m_cache.mk_unique(p) == p` on wide factoring | S8by remainder; S8cj item 2 | not reproduced at e497dcf (sort N4); S8cj is to reduce it to SMT-LIB | |
| UPS-03 | Z3: invalid read in `spacer::pob_queue::reset()` | S8ck item 1, item 10 | fixedpoint only, unreachable from nelli; S8ck item 10 reduces it | |

### §5.7 Pending classification

These could not be classified as tag blockers or not. The sort's UNVERIFIABLE
rows (U1–U8) are awaiting disposition before the tag and are **not moved**;
they are listed so nothing is lost. Each moves into §5.1–§5.4 once its
disposition shows it is not worse than `main`, or stays with RFC-0005 if it is.

| ID | Item | Source | Why pending | Owner |
|---|---|---|---|---|
| PND-01 | PCRE JIT stack limit `-27` read as a false `sxUnsat` | sort U1; S8cf items 1, 2 | needs a JIT build; the image's 8.45 has none | |
| PND-02 | 8.39 JIT's 113 prefix-scan differences; 8.44, 8.39, 8.37 class behaviour; the differential-only leg for older PCRE builds and multi-item POSIX classes on 8.37 | sort U2; S8cf item 12; S8co items 2, 8 | needs those builds or the Windows legs | |
| PND-03 | Stack size on macOS and the BSDs (compiled with `--compileOnly` only, never run) | sort U3; S8cp item 6 | no host; the item asks for a 2 MiB fallback where never run | |
| PND-04 | **Latent crash:** a `v == f` Int definition in `regexRecDefConds` segfaults at `byteLeafIds` `dec_ref` | sort U4; S8co item 1; S8cf remainder | avoided, not fixed; no SUT at e497dcf reaches it; a wrong refcount can hide a use-after-free | |
| PND-05 | **Latent crash:** rc=139 of probe p7 (top-level `let ra = symexFind(...)` plus an unused proc with `=sink`, `=dup` and `quit`) | sort N3; S8cp item 4; S8cb note | 200 of 200 runs rc 0 per sha on c, no valgrind or ASan; the cause is unknown and it is not fixed | |
| PND-06 | The October notes' false `sxUnsat` "on a SUT nobody reproduced" | sort U5; S8cl item 1 | the SUT does not exist to run | |
| PND-07 | `z3ApiErrorCount` over-count changing a verdict | sort U6; S8ck item 6 | read, not observed; looks like a decline | |
| PND-08 | `tregex_index` hang on Z3 5.1, and whether the walker can reach it | sort U7; S8ck item 4 | the nim-z3 suite's shape was not ported to a probe | |
| PND-09 | Every row of the sort on Z3 4.13.4 | sort U8 | covered by the release gate's full 4.13.4 sweep | |
| PND-10 | Whether a verdict reached after Z3's `mk_unique` check can be trusted; if not, declining on that query is a soundness fix | S8cj item 2 | not reproduced at e497dcf (sort N4); S8ci's report gives different figures | |
| PND-11 | S8cu's known limits: macro-built pragmas, a pushing template from another module, an import under a push in a module the scan does not read | S8cu | if the scan misses a check-off region, the walker assumes checks are on, which is the false `sxRaised` S8cu fixed; `main` faulted on these routines, so a miss may be worse than `main` | |
| PND-12 | S8cu's resumed rows without a `main` column yet: `push assertions:off` (`compileOption` reads nelli's own option), a global initialiser under a push, the `cmpIgnoreStyle` hang, a nil deref with SIGSEGV against a caught `NilAccessDefect`, the cross-module rows | S8cu (resumed 2026-11-02) | S8cu is producing the three-way table | |
| PND-13 | Z3's own internal recursion depth, not audited when S8ct bounded the walker's term walks | S8ct (B19 disposition) | to be checked at disposition | |

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
| INT-01 | Windows re-exec replay: marshal case-object and `ptr`/`ref` witnesses (a direct `replayWitness`, and as globals) instead of declining. The first precision item | S8ct, "For RFC-0016" 1 | precision | is PRC-01 |
| INT-02 | The ref-merge walk (`iteDeep`'s SUT) peaks at 8.36 GB under an 8 GB limit and is killed at 124–135 s, the same at `main` and on the channel, with and without tracing | S8ct, "For RFC-0016" 2 | crash, same as `main` | is CRH-03 |
| INT-03 | A regex literal of about 2600 groups | S8ct, "For RFC-0016" 3 | crash | is CRH-04 |
| INT-04 | `tsymex_rfc0005_s8by`'s units check is not deterministic under concurrent load (18.2M and 18.3M units against 5.85M alone). On cpp it fails alone, deterministically, at `8177eb27` (eos, Z3 5.1): the same query's spend drifts within one process regardless of what the context holds (72,126 units for the first three runs, then 17.5M, 18.4M, 18.0M, 17.5M, 17.1M), so `r.units == base.units` fails while every outcome and the bounded outcome agree. The settling step does not settle on cpp. Not a verdict defect; no CI leg runs cpp | S8ct, "For RFC-0016" 4 | test-harness | is CI-03 |
| INT-05 | An object field of a two-alias type stops the compile (`expected 'O = Alias'`), at `main` and on the channel; pinned "declines as main does" in `tsymex_rfc0005_s8ct_deepterm` | S8ct, "For RFC-0016" 5 | crash (compile stop), same as `main` | |
| INT-06 | The array-width decline (`termWalkMaxDepth`) catches an `int` index the path confines (`a[n and 7]`): the count reads the index's type, not the path | S8ct, "For RFC-0016" 6 | precision | |
| INT-07 | On Z3 4.13.4, a nim-z3 context made after one holding 80,000 `or` terms was destroyed builds terms about 800 times slower (20,000 `or`s: 0.14 s, then 119 s); a `symexFind` in between restores it. Not chased | S8ct, "For RFC-0016" 8 | performance | |
| INT-08 | `tsymex_rfc0005_s8ct_deepterm`'s teardown takes 78 s on Windows | S8ct (coordinator, release intake) | test-harness | with CI-01 |
| INT-09 | A `for` over a `splitLines` iterator (`readFile(...).splitLines`) in a SUT stops the compile: "node has no type" in `classifyType`, from `parseStmtInner`. The same family as CRH-01's `s.sort()` compile stop. The S8ct note says it was not checked at `main`; the coordinator's intake records it as the same as `main` | S8ct, "For RFC-0016" 7 | crash (compile stop), same as `main` | with CRH-01 |
| INT-10 | Seven pins moved from a verdict to a decline (`feGlobalRouteUnproved`): `cvm`, `cvm_dead` in `tsymex_rfc0005_s8bg_remainder` and `uc`, `uc_dead`, `dc`, `dc_dead`, `dx_dead` in `tsymex_rfc0005_s8bs_byref`. Each is a read in a routine with a route an exact model of the hook would close | S8cs, "Precision cost" and "For RFC-0016" | precision | with PRC-04 |
| INT-11 | The `trace1` row of `tsymex_rfc0005_s8cs_routes` (a `=trace` hook only the cycle collector runs) is a walker fault, `coerceIntLit` on an `svPtr`; `main` stops the compile on it | S8cs (coordinator, release intake) | crash (walker fault), better than `main` | |
| INT-12 | Under `--exceptions:setjmp` on Windows, the walker crashes entering its 16 MB fiber (SIGSEGV in `runSymexCaught`, before any walk). The same fiber and the same crash as `main`; the setjmp suite pins the default crash on Windows and cpp | S8cu, "Windows" | crash, same as `main` | |
| INT-13 | A re-executed replay declines while the host has set a runtime hook (`globalRaiseHook`, `localRaiseHook`, `outOfMemHook`, `unhandledExceptionHook`, `onUnhandledException`, `errorMessageWriter`), so a Windows run loses verdicts a fork confirms. A proc value cannot be marshalled, so the replay declines as not marshallable, naming the hook | batch 11 (`7b2ab1e5`, `tsymex_rfc0005_b11_hoststate`) | precision | with PRC-02 |
| INT-14 | The re-exec footprint now also reads the type symbols a body names, a call's result type and each user routine's signature, so more SUTs reach a type whose module declares a hook and decline on Windows | batch 11 (`7b2ab1e5`) | precision | with PRC-01 |
| INT-15 | `setControlCHook` is not among the runtime hooks `hostRuntimeHook` checks, so a re-executed replay does not decline when the host set one, and the child runs without it. Not classified: needs a three-way row | batch 11 (`replayproc.nim`) | unclassified (§5.7 rule) | |
| INT-16 | The 0.9.0 migration note's counts recounted against v0.8.0 (37 new `SymexErrorKind` members, the ordinal table). **Done** in batch 11 (`8f00b736`); recorded so the item is not reopened | batch 11 | test-harness (docs) | closed |
| INT-17 | 30 corpus suites still take over 60 s of compile plus run on Windows (`scripts/ci-suite-seconds.tsv`, run 41671937922). Each is a single long test or compile-bound. The longest in that table is 127.4 s (`tsymex_rfc0005_s8ab_letaudit`); the coordinator's intake reports up to 157 s | S8cm (done; `9ebe2a46`) | test-harness | with CI-01 |
| INT-18 | Probe p7 (sort N3) now declines (sxUnknown) where `main` decides correctly (sxSat; native hits at k=3). A precision loss on this SUT, not a soundness one. Its old rc=139 did not recur in 450 runs per tree (c, cpp, ASan) | pre-tag probes on `8177eb27` | precision | |
| INT-19 | PCRE 8.37 built without JIT, which is on the verified-library list, was not run. U1 and U2 were verified on 8.37 JIT, 8.39 JIT and 8.44 JIT: the candidate declines where `main` gives a false pair | pre-tag probes (U2) | test-harness | |
| INT-20 | U5's original SUT (October false sxUnsat) lives only on the offline worker. S8cl's reconstruction (`unsafeNew(p, 8); if p != nil`) is correct on the candidate. Recover the original, and pin it, when the worker returns | pre-tag probes (U5) | test-harness | |
| INT-21 | The check-off probe's `ai_caught` (`mitems` over `int16`, `assertions: off`) decides sxRaised. The raise looks real (int16 overflow at 32767 with overflow checks on), but no native run tried that input. Pin it natively | pre-tag probes (S8cp item) | test-harness | |

**From the 0.9.1 wiring audit (2026-11-03).** What RFC-0005's post-tag
wiring audit (WA-1 to WA-13) and its fix slices W1 to W3 left open. Measured
against 0.8.0, as the audit was; none is worse than it.

| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| INT-22 | A clean, faithful winner is never replayed, so nothing learns that its witness ends the process after the target. `assertCoveredBy` still splats it and `symexForAll` still seeds it, in the host (`symex.nim:4057-4061`, `:982`). Unchanged from 0.8.0; WA-2 closed only the replayed case (`witnessUnsafe`) | 0.9.1 wiring audit | crash, same as 0.8.0 | |
| INT-23 | A replay that ends at a memory limit is run-dependent only when the child's `outOfMemHook` reports it (`replayproc.nim:145`, `:328`). Under `-d:useMalloc` the hook is not reached, and a kernel OOM kill is a `reSignalled` SIGKILL, so either is cached as a permanent `:unk` | 0.9.1 wiring audit | precision | |
| INT-24 | The run-dependence flag is a threadvar reset by each entry macro's settle (`replayproc.nim:90`; read at `symex.nim:646`). A user-level `saveSymexVerdict` of an `sfUnknown` right after a settle that set it skips its save too | 0.9.1 wiring audit | performance | |
| INT-25 | Hypothesis: on macOS a kill at `replayTimeoutMs` does not reach the SUT's own child processes, and the child does not die with the host. `setpgid` and `PR_SET_PDEATHSIG` are Linux-only (`replayproc.nim:296-298`, `:374-376`). There is no macOS CI to probe it | 0.9.1 wiring audit | unclear (hypothesis; no macOS host) | |
| INT-26 | `RegexError` reaching `symexFindAllWitnesses` through the user exception hierarchy (WA-1, `symex.nim:4523`) is unpinned: W1 pinned a user exception type only. It needs a PCRE SUT | 0.9.1 wiring audit | test-harness | |
| INT-27 | Under `--panics:on` `replayInScope` declines every target (`symex.nim:2264`), so every lossy clean winner is `rsUnconfirmed` (`settleWinner`, `:3417`) and none is `trusted()` | 0.9.1 wiring audit | precision | |

**From the INF-05 owner audit (rows marked UNOWNED).** The rows the audit
marked OWNED-0016 were already in this document (PRC-31, PRC-32, INF-04,
PND-07, PND-08, UPS-01) and are not repeated.

| ID | Item | Source | Class | Owner |
|---|---|---|---|---|
| AUD-01 | `isLoose` leaves an `isIntOffset` parameter unstamped. By design (ADR-0001: `isLoose` is opt-in unsound and carries its banner on `main`); needs a "stays by design" record, not a slice | S8w | soundness, opt-in and documented; not worse than `main` | |
| AUD-02 | `acDivByZero` off with `acOverflow` on leaves the continuation unconstrained at a zero divisor. A nelli setting with no Nim counterpart (Nim's zero check rides on `overflowChecks`); a witness relying on it would trap on replay, which S8ct's child contains | S8aa | unclear (policy); not worse than `main` | |
| AUD-03 | No clean no-zero type remains for the free-`retSym` guard pins; they are now `sxUnknown` on a `HashSet[string]` arm field, so the guard's coverage is weaker. No verdict defect | S8z | test-harness | |
| AUD-04 | Macro-VM closure capture: a nested proc capturing a loop `var` kept one closure environment across iterations (seen as a duplicate case label). **Probed, no instance** at `main` 6cbfe8f and the channel at 67f0b622; the one known instance was fixed in S8z (`tagOrdOf` top-level). No other RFC-0016 item audits this class (AUD-06 and AUD-07 are the `let`/parameter alias guard's coverage) | S8z; coordinator probe, 2026-11-03 | unclear at audit; probed, no instance | closed |
| AUD-05 | Step 1c's equality classes are syntactic over the roots: an equality the query implies without stating it is not seen. Shown, not closed (`tsymex_rfc0005_s8aq_remainder` (4)); the uncapped steps still decide these queries | S8ai; S8aq item 4 | precision | |
| AUD-06 | The build-time VM-alias gate runs on one suite per CI leg, not the whole corpus (deliberate: about 15–18 s per compile). Carried unchanged through S8ak and S8al | S8ah, S8ak, S8al | test-harness | |
| AUD-07 | A generic never instantiated in the scope's compilation unit gives the VM-alias guard an un-instantiated `getImpl()` tree | S8al | test-harness | |
| AUD-08 | Non-integer `HashSet` elements (`HashSet[string]`, float, tuple) decline as a parameter or local; PRC-12 covers only a `HashSet[string]` behind a pointer or in a heap field | S8am | precision | with PRC-12 |
| AUD-09 | A `var` global initialised by a literal is not read at its initialiser: its entry value is fresh. A deliberate sound choice (S8as item 3) | S8as | precision | |
| AUD-10 | The nil-dereference check of a lazily read operand happened where the read moved (S8ax's `orderOperands`), not where Nim checks it. The S8ax probe turned this into two blockers, both fixed: S8cq makes argument reads follow the C backend's temporaries (`nimArgTemps`; `tests/tsymex_rfc0005_s8cq_argorder.nim`), and S8cu makes a nil dereference an uncatchable crash routed through frame exits (`tests/tsymex_rfc0005_s8cu_nil.nim`, `_nil_native`, `_nil_setjmp`) | S8ax; S8be item 7; S8cq; S8cu | soundness at audit; fixed | closed by S8cq and S8cu |
| AUD-11 | S8aw's `L`-against-`indexof` link now covers native terms only; the walker no longer emits `seq.last_indexof` or `str.indexof` for `rfind`/`find`. A coverage note, no wrong verdict or decline described | S8au | precision | |

AUD-04 and AUD-10 were the two rows whose standing against `main` the audit
could not settle. Both are closed: AUD-04 by a probe at both shas that found
no instance, AUD-10 by S8cq and S8cu.

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

## §7 — Open forks

- **`exit-criterion`.** §3.3's proposal, or the work list alone. Recommended:
  §3.3's proposal. Awaiting Corey.
- **`upstream-reports`.** File UPS-01 to UPS-03 now, file the two with
  reductions (UPS-01, UPS-03) and hold UPS-02 for S8cj, or hold all three.
  Recommended: file the two with reductions. Awaiting Corey.
- **`fork-c-clean-replay`.** A gated clean replay as a safety net (INF-02),
  off by default and on in nelli's own suites and the fuzzer, or none.
  Recommended: add it. Awaiting Corey.
