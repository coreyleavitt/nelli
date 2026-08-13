#!/usr/bin/env bash
# Run a single nelli test inside the canonical podman dev container
# (Corey's prebuilt Nim toolchain + Z3; built by scripts/build-dev-image.sh).
# Usage:  scripts/runtest.sh tests/tsymex_phase1_arith.nim
# Mounts: the project + the milpa CAS (at both the canonical path and its
# host-absolute path, so milpa's absolute dep symlinks resolve in-container).
set -euo pipefail
cd "$(dirname "$0")/.."
test_file="${1:?usage: $0 <test.nim>}"
img=localhost/nelli-dev:latest
podman image exists "$img" || scripts/build-dev-image.sh
podman run --rm \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work \
  "$img" \
  bash -c "nim c -r --hints:off $test_file"
