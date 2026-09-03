---
name: tracker
description: Query or update the quipu work-status tracker (https://quipu.leavitt.dev, project nelli). USE THE API FIRST for any "what's the state of RFC X / what's open / what's owed / what's next" question — the tracker has already parsed status, review-state, debt, drift, dependencies, and activity for the whole corpus; one curl replaces a multi-file audit. Also: update curated fields (needs-help, notes, edges, dismissals).
---

# quipu tracker — project `nelli`

Live dashboard + pre-computed audit cache for this repo's RFC/work state:
https://quipu.leavitt.dev/p/nelli

## Agent API — query this BEFORE auditing by hand

```
# Orient in one call: every RFC's status/review/debt/drift/stage/activity,
# plus debt list, awaiting-decision queue, unblocked frontier, dirty files.
curl --resolve quipu.leavitt.dev:443:100.101.212.69 -s https://quipu.leavitt.dev/p/nelli/api/summary

# One RFC, everything parsed: fields + open items + slices + notes.
curl --resolve quipu.leavitt.dev:443:100.101.212.69 -s https://quipu.leavitt.dev/p/nelli/api/rfc/0001

# Full-text search across statuses / open items / slices / streams.
curl --resolve quipu.leavitt.dev:443:100.101.212.69 -s 'https://quipu.leavitt.dev/p/nelli/api/search?q=term'

# Dependency graph (depends/related edges, parsed and manual).
curl --resolve quipu.leavitt.dev:443:100.101.212.69 -s https://quipu.leavitt.dev/p/nelli/api/graph

# Ranked order: what to do next, the waves behind it, and the critical path.
curl --resolve quipu.leavitt.dev:443:100.101.212.69 -s https://quipu.leavitt.dev/p/nelli/api/roadmap
```

Useful jq one-liners:

```
# actually-complete list (review at floor, zero open items)
… /api/summary | jq -r '.rfcs[] | select(.clean_complete) | .number'
# blocked on the human right now
… /api/summary | jq -r '.awaiting_decision[] | .rfc + ": " + .text[0:100]'
# what should be worked next
… /api/summary | jq -r '.roadmap.next'
# the full ranked queue with the terms behind each score
… /api/roadmap | jq -r '.items[] | "\(.number) \(.score // "-") \(.value)/\(.size) unblocks=\(.unblocks) \(if .unblocked then "ready" else "blocked" end)"'
# what could run in parallel right now
… /api/roadmap | jq -r '.waves[0][]'
```

## Ranking — two declared fields, everything else derived

An RFC is ranked when its header declares both grades, beside `Category:`:

```
- Size: M          # xs · s · m · l · xl
- Value: high      # low · med · high · critical
```

Everything else is computed from the dependency graph: readiness, wave
(topological depth), leverage (how many docs finishing this releases), the
critical path, and `score = value x leverage / size`.

**Order is never declared.** Do not add a priority field — a hand-written
order becomes a second source of truth the moment the graph changes under it.
The one override is `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/pin` (curated, exclusive, reported
separately and never folded into a score).

Check `.ranked` before acting on `.roadmap.next` / `.items[0]`: when no doc
declares both grades it is `false`, and the order you get is the graph's own
(wave, then number) — honest, but not a priority. Grades outside the
project's vocabulary come back with `size_known`/`value_known` false and no
score, rather than a guessed default.

Trust model: the tracker mirrors the DOCS (plus git metadata). It is the
cheap first answer, not a source of truth over the tree — spot-check the
cited doc for load-bearing claims. A wrong tracker answer means a doc lacks
a `Status:` field or resolution marker (✅ / RESOLVED / ~~strike~~ / `[x]`):
fix the doc, then sync/push.

Field gotcha: an open item's `born` (and the `age_days` / "Nd old" derived
from it) is the **git-blame time of the flagged line**, NOT when the tracker
first ingested it. An item can read "3d old" on a tracker installed an hour
ago. Do not use it to reason about how long the tracker has been reporting
something, or whether an item post-dates the tracker's own install.

## How it stays current

A git post-commit hook POSTs `https://quipu.leavitt.dev/p/nelli/sync`; the hub also re-parses on
startup and every 10 minutes.

## Curated fields (survive every re-sync; form-POSTs, expect 302)

| Action | Request |
|---|---|
| Toggle RFC needs-help | `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/flag` |
| Toggle slice needs-help | `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/slice/flag -d slice="<name>"` |
| Add a note | `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/note -d body="..."` |
| Add manual edge | `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/edge -d dst=NNNN -d kind=related` |
| Delete manual edge | `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/edge/{edge_id}/delete` |
| Pin as next (exclusive; toggles) | `POST https://quipu.leavitt.dev/p/nelli/rfc/{n}/pin` |

## What NOT to do

- Never edit the tracker's SQLite directly; use the endpoints.
- Never "fix" tracker data by hand when the real fix is a stale `Status:`
  line or slice table in `docs/rfc/` — fix the doc, sync, done.
