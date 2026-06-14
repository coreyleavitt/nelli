#!/usr/bin/env bash
# Build the proptest dev/test container image (Corey's prebuilt Nim toolchain
# + Z3). Idempotent; podman layer-caches. Produces localhost/proptest-dev:latest.
set -euo pipefail
cd "$(dirname "$0")/.."
podman build -t localhost/proptest-dev:latest -f scripts/Containerfile scripts/
