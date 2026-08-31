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
curl -s https://quipu.leavitt.dev/p/nelli/api/summary

# One RFC, everything parsed: fields + open items + slices + notes.
curl -s https://quipu.leavitt.dev/p/nelli/api/rfc/0001

# Full-text search across statuses / open items / slices / streams.
curl -s 'https://quipu.leavitt.dev/p/nelli/api/search?q=term'

# Dependency graph (depends/related edges, parsed and manual).
curl -s https://quipu.leavitt.dev/p/nelli/api/graph
```

Useful jq one-liners:

```
# actually-complete list (review at floor, zero open items)
… /api/summary | jq -r '.rfcs[] | select(.clean_complete) | .number'
# blocked on the human right now
… /api/summary | jq -r '.awaiting_decision[] | .rfc + ": " + .text[0:100]'
# what should be worked next
… /api/summary | jq -r '.frontier[] | select(.unblocked) | .number'
```

Trust model: the tracker mirrors the DOCS (plus git metadata). It is the
cheap first answer, not a source of truth over the tree — spot-check the
cited doc for load-bearing claims. A wrong tracker answer means a doc lacks
a `Status:` field or resolution marker (✅ / RESOLVED / ~~strike~~ / `[x]`):
fix the doc, then sync/push.

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

## What NOT to do

- Never edit the tracker's SQLite directly; use the endpoints.
- Never "fix" tracker data by hand when the real fix is a stale `Status:`
  line or slice table in `docs/rfc/` — fix the doc, sync, done.
