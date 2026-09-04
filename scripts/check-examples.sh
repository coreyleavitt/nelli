#!/usr/bin/env bash
# Compile-and-link every examples/*.nim (RFC-0010 slice C3c).
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
#   * a compile step in .github/workflows/symex-mingw.yaml's corpus job
#     (shard 0), which is the only leg with Z3 on Windows and therefore the
#     only one that can build these files at all.
#
# Locally this RUNS each example (via dt-bounded.sh), because an example that
# builds but prints nothing is still broken documentation, and they all finish
# in well under the bound. The Windows leg only builds-and-links them: several
# drive Z3 to a fixpoint and would dominate that leg's runtime. Link, not
# --compileOnly, because linking is the phase that catches a missing symbol —
# which is exactly what a stale example is most likely to hit.
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
