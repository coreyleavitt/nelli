# nelli RFCs

Numbered design docs. One RFC per file, `NNNN-slug.md`, with an optional
`NNNN-slug.handoff.md` carrying the session-to-session state (stage, round,
slices done, open forks, review ledger) and any number of
`NNNN-slug.<suffix>.md` companions for material too long to inline.

Renumbered from the old flat `docs/RFC-<slug>.md` layout on 2026-08-31 so the
quipu tracker can read them — it requires a 4-digit prefix. Numbering is
chronological by when the work was actually done, which is not the same as
git-add order: three docs were authored earlier and committed late.

| # | slug | subsystem |
|---|---|---|
| 0001 | chapulin-hardening | symex |
| 0002 | parser-normalization | symex |
| 0003 | fuzzer-nextgen | fuzzer |
| 0004 | z3-optional | packaging |
| 0005 | branch-scoped-degrade (soundness channels) | symex |
| 0006 | reflective-strategies | core |
| 0007 | trace-properties | core |
| 0008 | assurance-record | core |
| 0009 | deterministic-simulation | core |
| 0010 | config-discipline | core |
| 0011 | effect-annotations | symex |
| 0012 | complexity-properties | core |
| 0013 | coverage-guided-cost | core |
| 0014 | integer-range-provenance | symex |
| 0015 | audit-remainder | core |

0006–0012 were composed together on 2026-09-03 from a post-0005 architecture
survey rather than authored one at a time. They are grouped by shared
*mechanism*, not by theme — see each doc's thesis for why its parts belong
together. `docs/rfc/SEED-SET-2026-09-03.md` carries the composition rationale
and the recommended order. (It is deliberately unnumbered — a `NNNN-` prefix
would make quipu parse it as an eighth RFC.)

**0006 and 0010 have since been through `/architect`.** 0006 had round 1 on
2026-09-03 and is a `draft` with one open fork. **0010 is `implemented`** — two
review rounds on 2026-09-03/04, then all 19 slices built on
`rfc-0010-config-discipline`, each gated by a whole-suite sweep diff against a
recorded baseline (end to end: `regressed=0`), a five-round `/code-review` to
floor, and a follow-up pass clearing the Lows. **Merged to `main` and released
as `v0.8.0` on 2026-09-08.** Upgrade notes: `docs/migration/0.8.0.md`.
0007–0009, 0011 and 0012 remain unreviewed `seed`s, none of them designed.
**0013** is a later, separately-composed `seed` (2026-09-09): a bisected
per-example cost regression in coverage-guided `forAll`, reported by a
downstream rather than found by the survey.

**0014 and 0015** are `seed`s composed together on 2026-09-20 from the nine
issues (#164–#172) the #161–#163 audit left behind. The split is by mechanism,
not by size: **0014** is four issues that are one missing capability — the
abstraction layer carries an integer bound only for a value that *is* a
declared-range param — paid for once in soundness and twice in precision, with
a slice order forced by a measured Z3 blowup. **0015** is the remainder, and
says so in its own §0 rather than inventing a mechanism to justify itself:
three findings share a defect class (a contract documented at an entry point and
honoured on a subset of the paths behind it) and two are hygiene. Each carries
one open fork for Corey.

Not every design doc lives here. `docs/FUZZ_PLAN.md`, `docs/SYMEX_PLAN.md`
and `docs/MODAL_PBT_PLAN.md` are standing plans rather than RFCs, and the
symex ADRs live under `docs/symex/`. `docs/RFC-fuzzer-hybrid.md` is a
superseded 2026-08-14 draft kept only as design notes; it is deliberately
untracked and unnumbered.

## Conventions

**Migration notes are not RFC artifacts.** An RFC that changes behaviour a
consumer has to react to gets a `docs/migration/<version>.md`, keyed to the
release, addressed to whoever is upgrading. It does **not** get a per-RFC
downstream-audit document.

That format is **retired** (2026-09-08). `0004` and `0010` each carried one;
both named specific downstream projects, told the reader to run greps from
another repository's root, and carried a release gate whose items were that
consumer's work. Two things were wrong with it. It contradicted this project's
standing rule that consumers report what they hit rather than engine work
blocking on their chores — an RFC cannot be "done" pending somebody else's
build. And it keyed migration facts to a *consumer* when they are properties
of a *release*, so a downstream nobody had thought of was addressed by none of
it. nelli ships tags and a CHANGELOG; downstreams manage themselves. See
`docs/migration/README.md`, which also says when a release needs a note at all
— most do not.

**Status.** Every RFC carries a `- **Status:**` line whose FIRST word is
authoritative and drawn from a controlled vocabulary:

    living · seed · draft · ready · in-progress · implemented · superseded · parked

The rest of the line is free prose. Anything outside that vocabulary reads as
`unknown` on the board, so lead with the word and explain afterwards.

**Category.** `- Category: <slug>` — one of `core`, `symex`, `fuzzer`,
`packaging` (display order and labels are set in the repo's `quipu.toml`).

**Size / Value.** `- Size: M` and `- Value: high`, on their own lines under
`Category:`. Sizes are `xs · s · m · l · xl`; values are
`low · med · high · critical`. These two are the *only* prioritisation input —
quipu derives everything else (readiness, dependency wave, leverage, critical
path, and the rank itself) from the `Depends on:` graph, and renders it at
`/p/nelli/roadmap`. Both are optional: a doc missing either is listed but
unranked, never guessed at.

**Do not add a priority or order field.** Ordering is derived, on purpose — a
hand-written rank becomes a second source of truth the moment the dependency
graph changes under it. To override, pin on the board
(`POST …/rfc/NNNN/pin`), which is recorded as an override rather than folded
into the score.

**Depends on.** Put the references on lines *below* the header, never on it:

    - **Depends on:**
      - RFC-0003 (fuzzer-nextgen) — why

A single-line `- **Depends on:** RFC-0003` parses to an empty block and
silently yields no graph edge, because the extractor starts scanning after
the matched line.

**Awaiting a decision.** Phrase blockers as "awaiting Corey" / "needs Corey" /
"open forks" so they surface in the tracker's decision queue.

## Tracker

These docs are read by quipu (`quipu.leavitt.dev`, project `nelli`). The hub
runs on the same host and bind-mounts this repo read-only, so there is no
token and nothing is ever written back here. Repo-side conventions live in
`quipu.toml` at the repo root; a `post-commit` hook refreshes the hub.
