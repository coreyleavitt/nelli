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

0006–0012 were composed together on 2026-09-03 from a post-0005 architecture
survey rather than authored one at a time. They are grouped by shared
*mechanism*, not by theme — see each doc's thesis for why its parts belong
together. `docs/rfc/SEED-SET-2026-09-03.md` carries the composition rationale
and the recommended order. (It is deliberately unnumbered — a `NNNN-` prefix
would make quipu parse it as an eighth RFC.)

**0006 has since been through `/architect` round 1** (2026-09-03) and is now a
`draft` with one open fork; see its handoff. 0007–0012 remain unreviewed
`seed`s, none of them designed.

Not every design doc lives here. `docs/FUZZ_PLAN.md`, `docs/SYMEX_PLAN.md`
and `docs/MODAL_PBT_PLAN.md` are standing plans rather than RFCs, and the
symex ADRs live under `docs/symex/`. `docs/RFC-fuzzer-hybrid.md` is a
superseded 2026-08-14 draft kept only as design notes; it is deliberately
untracked and unnumbered.

## Conventions

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
