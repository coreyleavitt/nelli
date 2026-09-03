# RFC — soundness channels: separating over- from under-approximation

- **Status:** draft — **repurposed 2026-09-01.** This RFC was opened to carry
  RFC-0001's BLOCKER B7-2 ("case/else-raise sibling poisoning") on the
  premise that it needed a branch-scoped classified-degrade architecture.
  **That premise was wrong and B7-2 is fixed** (`cac15e6`, walker v124) — see
  §1. What survives is the genuinely valuable half, which B7-2 was never an
  instance of: the engine conflates two structurally opposite kinds of
  imprecision and throws away answers it has already earned.
- Category: symex
- **Depends on:**
  - RFC-0001 (chapulin-hardening) — the SND-1 taint machinery, the three-way
    carrier taxonomy, and the N36/N37/N39/N40 raise-to-in-band migration are
    all prior art this builds directly on.

## §0 — Thesis

There are two ways the walker can be wrong about a program, and it currently
reports both as one undifferentiated `sxUnknown`:

| | mechanism | modelled behaviour set |
|---|---|---|
| **Over-approximation** | fresh unconstrained placeholder, `mkUnsupported`, unmodelled field | ⊇ real — *adds* behaviours |
| **Under-approximation** | `maxLoopUnwind` k-unroll, `defaultZero`, heap-depth halt | ⊆ real — *removes* behaviours |

Their soundness consequences are **dual**:

- **SAT is trustworthy iff the path carries no over-approximation.** An
  under-approximation cannot invent a model — a witness found under
  k-unrolling is a real witness.
- **UNSAT is trustworthy iff no path carried an under-approximation.** An
  over-approximation cannot hide a model — if the enlarged program has no
  solution, neither does the real one.

Note the asymmetry: **over-taint scopes to a path; under-taint is global.** A
sibling branch's garbage cannot invalidate a witness found and replayed on a
clean path, but an UNSAT claim is a statement about *all* paths, so one
under-approximated path anywhere voids it.

**This is not hygiene — it is discarded capability.** Today a k-unroll taint
forces `sxUnknown` even when a witness was found *and replays against the
real function*. RFC-0001's own handoff records exactly this for the opOack
whole-proc search: "stays sxUnknown because the region-membership non-member
fallback still k-unrolls." Under the rule above that is a sound `sxSat`.

It also unifies findings RFC-0001 fixed one at a time. **S1** — the
placeholder seq whose `.len` silently read 0, producing a false `sxUnsat` one
line from a committed pin — was an under-approximation treated as sound.
**Bug #2**'s field poisoning was an over-approximation applied globally
instead of per-read. **N20**'s k-unroll is an under-approximation, which is
precisely why its own note that "verdict stays correct either way" holds.
Three separate slices, one missing distinction.

## §1 — What is already true (do not re-derive)

Read the source before designing against it. Four things that are **not**
what RFC-0001's escalation implies:

1. **B7-2 was a parser gap, not an architecture gap. FIXED `cac15e6`.**
   `case` as a statement was always modelled; `case` as an *expression* had
   no `parseExpr` arm and declined `feUnsupportedExprKind`. The "sibling
   poisoning" was downstream: the declining proc is a callee, parsed
   whole-proc at registration **before any path exists**, so the decline had
   no path to scope to. Fixed by the A-normalisation M5 already applied to
   `nnkIfExpr` at walker v50. No architecture was required.

2. **The raise-to-in-band migration already happened** — N36/N37/N39/N40,
   walker v101–v104, in the 0.5.1 fix loop. `allocDegrade`'s own comment
   records that those arms "previously `raise`d." RFC-0005's original
   framing described this as the large unstarted refactor. It is substantially
   done.

3. **SAT already beats the global flag.** `runtime.nim`'s verdict is
   `if winnerFound: … elif w.sawUnknown …`. A found witness wins regardless
   of what degraded elsewhere, so the SAT half of §0's rule is *already*
   path-scoped. What is missing is the UNSAT half and the over/under
   distinction — not path-scoping per se.

4. **Per-path taint exists and is well built.** `Path.uncertain`,
   `forkPathTainted`, and an internal template deliberately shaped so that
   "drop the taint" is unspellable. There is also an Invariant-7 backstop
   asserting no site sets `sawUnknown` bare without a classified error.

So the remaining work is **narrower and better-founded** than the original
seed claimed: classify each existing degrade site as over- or
under-approximating, carry that on the taint, and make the verdict rule
consume it.

## §2 — Design sketch (for stage-2 architect rounds)

Taint becomes a two-channel lattice value joined by the existing combinators
(`t₁ ⊔ t₂` through arithmetic/comparison), carried as a field on the value or
path that is already threaded — **not** a side table. Representation matters:
see §3.

The verdict rule then reads roughly:

- some path yielded a witness, and that path carries no over-taint → `sxSat`
- proven UNSAT, and no path anywhere carried under-taint → `sxUnsat`
- otherwise → `sxUnknown`, carrying which channel forced it

**Open questions for round 1:**

1. **Classifying the existing sites.** Every current degrade must be labelled
   over or under. Some are obvious (`mkUnsupported` over; `maxLoopUnwind`
   under). Others are not: what is a *halted* path (heap-depth exhaustion)?
   It removes behaviours from consideration, so under — but it also halts
   rather than continues, so it has no surviving path to carry the taint.
   That class may need the taint attached to the fork point.
2. **Is any site BOTH?** A placeholder that is fresh-unconstrained in one
   dimension and zero-forced in another would be, and would need both bits.
3. **The three-carrier taxonomy.** `allocDegrade`, the R1 placeholder funnel,
   and `degradeStrArm` converge on shared sinks. Does the channel ride the
   existing sinks, or does the taxonomy need a fourth column?
4. **Cost.** ✅ **Unblocked 2026-09-03 — N45 was REFUTED.** This question was
   gated on a supposed ~3.4x fork-cost regression; measurement showed the
   B5-4 query is bit-identical between v105 and v124 at both k=2 and k=5
   (`rlimit` 69524 and 630599 respectively, same at both revisions), so there
   is no prior regression to budget around. The design guidance stands on its
   own merits regardless: prefer an O(1) field on a carrier already threaded
   over a side structure, and re-measure with `-d:symexQueryStats` once the
   taint lands — the instrument makes that a one-line check rather than an
   argument.

## §3 — Verification strategy

The killer property is **taint monotonicity**: *adding an unreachable tainted
branch to a green SUT must never change its verdict.* It is mechanically
generable — graft a poisoned disjoint arm onto any existing passing test — it
directly encodes this RFC's whole point, and it would have caught B7-2 as a
red test years before it was escalated.

Second: **witness replay as ground truth.** Any `sxSat` this RFC newly
permits (SAT on an under-approximated path) must have its witness replayed
against the real function, exactly as B7's differential oracle does. That
converts the soundness argument from a proof obligation into a test.

## §4 — Non-goals

- Widening the modelled fragment. This changes how gaps are *reported*, not
  how many there are.
- Root-causing N45 (own work; see §2 question 4, which depends on it).
- Unifying `hoistCaseExpr` with M5's `nnkIfExpr` arm — same idiom, worth
  sharing, but it is a refactor-under-green and belongs in its own slice.
