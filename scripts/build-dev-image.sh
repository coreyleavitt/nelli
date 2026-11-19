#!/usr/bin/env bash
# Build a nelli dev/test container image. Idempotent; podman layer-caches.
#
# Usage: scripts/build-dev-image.sh [variant]
#   (none)|latest  scripts/Containerfile              -> localhost/nelli-dev:latest
#                  (the CI-pinned patched Nim artifact and the CI-pinned Z3 release,
#                  both from scripts/nim-toolchain.pin; check:
#                  scripts/check-toolchain-parity.sh)
#   parity*        same Containerfile -> localhost/nelli-dev:<variant> (a trial tag,
#                  e.g. parity2, to verify before retagging :latest)
#   <variant>      scripts/Containerfile.<variant>    -> localhost/nelli-dev:<variant>
#                  e.g. z3-4.13.4 (official Z3 4.13.4, the Windows legs' version);
#                  variants derive FROM :latest, which is built first if missing.
#                  pcre-8.37-jit: PCRE 8.37 with the JIT, the Windows legs' engine
#                  (the native oracle for the 8.37 JIT model; pin PCRE_837_*).
#   <variant>-parity
#                  the same Containerfile.<variant>, derived FROM
#                  localhost/nelli-dev:$NELLI_BASE_TAG (default parity2) and tagged
#                  localhost/nelli-dev:<variant>-parity, a trial row to verify
#                  before retagging.
set -euo pipefail
cd "$(dirname "$0")/.."
variant="${1:-latest}"
. scripts/nim-toolchain.pin
build_args=()
case "$variant" in
  latest|parity*)
    cf=scripts/Containerfile
    build_args=(--build-arg "NIM_ARTIFACT_PACKAGE=$NIM_ARTIFACT_PACKAGE" --build-arg "NIM_ARTIFACT_TAG=$NIM_ARTIFACT_TAG" --build-arg "NIM_ARTIFACT_DIGEST=$NIM_ARTIFACT_DIGEST"
                --build-arg "Z3_VERSION=$Z3_VERSION" --build-arg "Z3_ASSET=$Z3_ASSET" --build-arg "Z3_SHA256=$Z3_SHA256"
                --build-arg "PCRE_VERSION=$PCRE_VERSION" --build-arg "PCRE_SHA256=$PCRE_SHA256")
    ;;
  *)
    row="${variant%-parity}"
    cf="scripts/Containerfile.$row"
    [ -f "$cf" ] || { echo "build-dev-image.sh: no $cf (unknown variant '$variant')" >&2; exit 2; }
    base="latest"
    [ "$row" = "$variant" ] || base="${NELLI_BASE_TAG:-parity2}"
    podman image exists "localhost/nelli-dev:$base" || "$0" "$base"
    build_args=(--build-arg "BASE_IMAGE=localhost/nelli-dev:$base")
    case "$row" in
      z3-4.13.4) build_args+=(--build-arg "Z3_VERSION=$Z3_4134_VERSION" --build-arg "Z3_ASSET=$Z3_4134_ASSET" --build-arg "Z3_SHA256=$Z3_4134_SHA256") ;;
      pcre-8.37-jit) build_args+=(--build-arg "PCRE_VERSION=$PCRE_837_VERSION" --build-arg "PCRE_SHA256=$PCRE_837_SHA256") ;;
    esac
    ;;
esac
podman build "${build_args[@]}" -t "localhost/nelli-dev:$variant" -f "$cf" scripts/
