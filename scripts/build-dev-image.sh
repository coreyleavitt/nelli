#!/usr/bin/env bash
# Build a nelli dev/test container image. Idempotent; podman layer-caches.
#
# Usage: scripts/build-dev-image.sh [variant]
#   (none)|latest  scripts/Containerfile              -> localhost/nelli-dev:latest
#                  (the CI-pinned patched Nim artifact, scripts/nim-toolchain.pin,
#                  + the distro Z3; check: scripts/check-toolchain-parity.sh)
#   parity         same Containerfile -> localhost/nelli-dev:parity (a trial tag
#                  to verify before retagging :latest)
#   <variant>      scripts/Containerfile.<variant>    -> localhost/nelli-dev:<variant>
#                  e.g. z3-4.13.4 (official Z3 4.13.4, the Windows legs' version);
#                  variants derive FROM :latest, which is built first if missing.
set -euo pipefail
cd "$(dirname "$0")/.."
variant="${1:-latest}"
if [ "$variant" = latest ] || [ "$variant" = parity ]; then
  cf=scripts/Containerfile
else
  cf="scripts/Containerfile.$variant"
  [ -f "$cf" ] || { echo "build-dev-image.sh: no $cf (unknown variant '$variant')" >&2; exit 2; }
  podman image exists localhost/nelli-dev:latest || "$0" latest
fi
build_args=()
if [ "$variant" = latest ] || [ "$variant" = parity ]; then
  # the toolchain pin (scripts/nim-toolchain.pin) feeds the Containerfile ARGs
  . scripts/nim-toolchain.pin
  build_args=(--build-arg "NIM_ARTIFACT_PACKAGE=$NIM_ARTIFACT_PACKAGE" --build-arg "NIM_ARTIFACT_TAG=$NIM_ARTIFACT_TAG" --build-arg "NIM_ARTIFACT_DIGEST=$NIM_ARTIFACT_DIGEST")
fi
podman build ${build_args[@]+"${build_args[@]}"} -t "localhost/nelli-dev:$variant" -f "$cf" scripts/
