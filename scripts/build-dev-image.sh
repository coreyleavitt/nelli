#!/usr/bin/env bash
# Build the nelli dev/test container image (Corey's prebuilt Nim toolchain
# + Z3). Idempotent; podman layer-caches. Produces localhost/nelli-dev:latest.
set -euo pipefail
cd "$(dirname "$0")/.."
podman build -t localhost/nelli-dev:latest -f scripts/Containerfile scripts/
