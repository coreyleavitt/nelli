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

**Category.** `- Category: <slug>` — one of `symex`, `fuzzer`, `packaging`
(display order and labels are set in the repo's `quipu.toml`).

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
