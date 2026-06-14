#!/usr/bin/env bash
# Fast single-test runner using the proptest dev image (Corey's prebuilt Nim
# toolchain + Z3; built by scripts/build-dev-image.sh). Supports both backends.
# Usage: scripts/dt.sh [c|cpp] tests/foo.nim
set -euo pipefail
cd "$(dirname "$0")/.."
backend="${1:?usage: dt.sh <c|cpp> <test.nim>}"; shift
test_file="${1:?usage: dt.sh <c|cpp> <test.nim>}"
img=localhost/proptest-dev:latest
podman image exists "$img" || scripts/build-dev-image.sh
# Mount the milpa CAS at BOTH the canonical path and its host-absolute path so
# milpa's absolute dep symlinks (_deps/softlink -> ~/.cache/milpa/...) resolve
# inside the container.
podman run --rm \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work \
  "$img" \
  bash -c "nim $backend -r --threads:on --hints:off $test_file"
