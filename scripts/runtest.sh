#!/usr/bin/env bash
# Run a single proptest test inside the canonical podman dev container.
# Usage:  scripts/runtest.sh tests/tsymex_phase1_arith.nim
# Mounts: the project + the milpa CAS so cross-run cache hits work.
# Installs libz3-dev per-run because containers are --rm; the apt-get
# cache is tiny and reuses the apt-cache mount-warm copy.
set -euo pipefail
test_file="${1:?usage: $0 <test.nim>}"
podman run --rm \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -w /work \
  nimlang/nim:2.2.0 \
  bash -c '
    set -e
    apt-get update -qq 2>/dev/null
    apt-get install -y -qq libz3-dev 2>/dev/null
    nim c -r --hints:off "'"$test_file"'"
  '
