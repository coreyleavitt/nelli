# proptest symex — design records

This directory holds the committed architectural decision records (ADRs)
and supporting design notes for the symbolic execution capability tracked
in [proptest #100](https://github.com/coreyleavitt/proptest/issues/100).

The live build plan is one level up at [`../SYMEX_PLAN.md`](../SYMEX_PLAN.md).
The ADRs are the durable, individually-citable design artifacts that the
plan references. Future contributors reading an ADR in isolation should be
able to reproduce the reasoning without needing the plan.

## Index

| | Title | Status |
|---|---|---|
| [ADR-0001](ADR-0001-integer-semantics.md) | Integer semantics — BV[W] floor with selective `Z3Int` abstraction | Accepted 2026-05-31 |
| [ADR-0002](ADR-0002-dsl-factoring.md) | Predicate-DSL factoring — three-layer `proptest/smt/` split | Accepted 2026-05-31 |

## What is an ADR

A short document recording one architectural decision: the context that
forced the choice, the options considered, the resolution, and the
consequences (both intended and accepted-as-cost). When the decision is
later revisited, the ADR is amended in place with a "Superseded by …"
header and the new ADR cites the old one as background.

Reference: [Michael Nygard, *Documenting Architecture Decisions*, 2011](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions).

## Numbering

ADRs are numbered in acceptance order under the `symex/` namespace.
Other proptest subsystems may grow their own ADR directories in time;
each subsystem's numbering is independent.

## Deferred work

Each ADR may defer follow-on work to a separately-tracked issue.
Phase 0 of the plan files those issues on acceptance. The current set:

- Loop-invariant inference (ADR-0001 § Deferred)
- Assertion-based range refinement (ADR-0001 § Deferred)
- Refinement through user-defined function calls (ADR-0001 § Deferred)

Each lives as a GitHub issue under proptest's M15 milestone and links
back to the relevant ADR.
