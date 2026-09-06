#!/usr/bin/env bash
# Build and run every examples/*.nim (RFC-0010 slice C3c).
#
# Why this exists. `examples/symex_loops.nim` stopped compiling at CR-9(b),
# when the resource caps moved onto a `budget` sub-object, and nobody noticed
# for months: `examples/` is built by neither `nimble test` nor any CI leg, so
# nothing ever looked at it. That is the same rot mechanism RFC-0010 found in
# the test suite itself, where four registered-nowhere suites had never run.
#
# What this buys, stated honestly. Adding examples to nelli.nimble's `test`
# task would have bought ZERO CI coverage, because nothing in CI runs that
# task. Real coverage needed a step on a leg that actually exists, so the gate
# has two halves:
#   * this script, for local use, and
#   * a build-and-run step in .github/workflows/symex-mingw.yaml's corpus
#     job (shard 0), which is the only leg with Z3 on Windows and therefore
#     the only one that can build these files at all.
#
# THIS COMMENT IS THE SINGLE SOURCE for why the gate runs rather than links;
# the workflow step points here instead of restating it.
#
# Both halves RUN each example, not just build it: a build-only check missed
# examples/symex_oob.nim going stale at CR-9 — it compiled fine and only
# failed at runtime, asserting the pre-refactor sxSat/witness shape after the
# engine moved to sxRaised/raisedWitness. An earlier version of the CI step
# built-and-linked only, on the unmeasured theory that several examples drive
# Z3 to a fixpoint and would dominate that leg's runtime. That theory was
# measured on Linux/podman during RFC-0010's stage-4 review and was simply
# false: every example ran in well under a second, against ~30s of compile
# time the link-only step was already paying. Run time was never the cost.
#
# No example count is stated here on purpose — both halves glob the directory,
# so a new example is picked up automatically, and a number in this comment
# would be one more thing to go stale (this review round found four such).
# Locally this uses dt-bounded.sh (not --compileOnly) so a hang is caught the
# same way a non-terminating test would be, rather than spinning forever.
#
# Usage: scripts/check-examples.sh [c|cpp]
set -uo pipefail
cd "$(dirname "$0")/.."
backend="${1:-c}"

failed=()
for f in examples/*.nim; do
  [ -e "$f" ] || continue
  printf '==> %s\n' "$f"
  if ! scripts/dt-bounded.sh "$backend" "$f" 600 >/dev/null 2>&1; then
    failed+=("$f")
  fi
done

if [ "${#failed[@]}" -gt 0 ]; then
  printf 'FAILED: %s\n' "${failed[*]}" >&2
  exit 1
fi
echo "All examples built and ran."
