# Migration notes

One file per release that needs one, named for the version you are upgrading
**to**. Read the one for your target version; if you are crossing several
releases, read each in order.

These are consumer-agnostic. They describe what changed in nelli and what you
have to do about it — nothing here tracks who consumes nelli, and nothing here
is a checklist for anybody else's repository.

## Why this replaced the per-RFC "downstream audit"

Earlier releases carried a `docs/rfc/NNNN-*.downstream-audit.md` alongside the
RFC. Those documents named specific downstream projects, told the reader to run
greps "from <consumer>'s root", and carried a release gate whose items were
*that consumer's* work — building their repo, reading their suite diff.

That was the wrong shape twice over. It contradicted this project's own rule
that consumers report what they hit rather than engine work blocking on a
consumer's chores; and it keyed migration facts to a *consumer* when they are
properties of a *release*. A downstream that appeared later, or one nobody had
thought of, was addressed by none of it.

nelli publishes version tags and a CHANGELOG. A downstream reads those and
manages its own upgrade. What nelli owes it is an accurate account of what
changed — which is what these files are.

## When a release needs one

Most do not; the CHANGELOG carries them. Write a migration note when the
CHANGELOG entry cannot do the work on its own:

- **A silent behaviour change** — code that compiles before and after and means
  something different. This is the case that most needs a document, because
  neither the compiler nor the version number can tell a reader which of their
  call sites moved. `0.8.0` is the type specimen.
- **A break that lands at a distance**, where the compile error names something
  other than the thing that changed.
- **A migration with a decision in it**, where the right action depends on what
  the caller meant and a mechanical rewrite would be wrong.

If the change announces itself with a clear compile error at the right place,
the CHANGELOG is enough. Do not write one of these out of habit.
