+++
type  = "review"
id    = "0005-review"
title = "RFC-0005 code review ledger (0.9.1)"
state = "pending"
profile = "rfc-flow@6"
+++

# RFC-0005 code review ledger (0.9.1)

**Surface (fixed for the whole loop).**
`549dae8b7998985588b4cb7e6033cd52ffbcef68..edb1277f8ba3652778c98d5b6ccb8788a7db0396`
(v0.8.0 to the 0.9.1 integration head, wiring proven), paths `src/**`. That
is 43 files, +67,396/−6,767. The review is run after the fact: v0.9.0 shipped
without it, and its findings land in 0.9.1. Tests and docs are in scope only
as evidence.

**Rounds.**
- Round 1: the surface itself.

## Findings

| ID | Sev | Status | Lens | File | Finding | Test / reason |
|---|---|---|---|---|---|---|
