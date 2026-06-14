#!/usr/bin/env bash
# Fast single-test runner using the prebuilt proptest-dev image (z3 baked in).
# Usage: scripts/dt.sh [c|cpp] tests/foo.nim
set -euo pipefail
backend="${1:?usage: dt.sh <c|cpp> <test.nim>}"; shift
test_file="${1:?usage: dt.sh <c|cpp> <test.nim>}"
podman run --rm -v "$PWD:/work" -v "$HOME/.cache/milpa:/.cache/milpa" -w /work \
  localhost/proptest-dev:nim2.2.0 \
  bash -c "nim $backend -r --threads:on --hints:off $test_file"
