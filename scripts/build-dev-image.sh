#!/usr/bin/env bash
# Build a nelli dev/test container image. Idempotent; podman layer-caches.
#
# Usage: scripts/build-dev-image.sh [variant]
#   (none)|latest  scripts/Containerfile              -> localhost/nelli-dev:latest
#                  (Corey's prebuilt Nim toolchain + the distro Z3)
#   <variant>      scripts/Containerfile.<variant>    -> localhost/nelli-dev:<variant>
#                  e.g. z3-4.13.4 (official Z3 4.13.4, the Windows legs' version);
#                  variants derive FROM :latest, which is built first if missing.
set -euo pipefail
cd "$(dirname "$0")/.."
variant="${1:-latest}"
if [ "$variant" = latest ]; then
  cf=scripts/Containerfile
else
  cf="scripts/Containerfile.$variant"
  [ -f "$cf" ] || { echo "build-dev-image.sh: no $cf (unknown variant '$variant')" >&2; exit 2; }
  podman image exists localhost/nelli-dev:latest || "$0" latest
fi
podman build -t "localhost/nelli-dev:$variant" -f "$cf" scripts/
