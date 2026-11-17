#!/usr/bin/env bash
# Toolchain parity gate: the Nim the local dev image runs must be the Nim CI's
# symex-linux leg runs, by digest. Both read scripts/nim-toolchain.pin.
#
# Usage: scripts/check-toolchain-parity.sh [--image TAG] [--live]
#   (default)      static: the pin is well-formed; the Containerfile ARG defaults
#                  and setup-symex-linux both follow it (no hardcoded tag/digest);
#                  and, if localhost/nelli-dev:TAG exists (default latest), its
#                  label and /etc/nelli-toolchain record the pinned digest.
#   --image TAG    check localhost/nelli-dev:TAG instead of :latest.
#   --live         also ask the registry what the tag resolves to now; a
#                  republished tag (new digest) fails with the new digest named.
# Exit 0 = parity, 1 = drift, 2 = usage / unusable input.
set -uo pipefail
cd "$(dirname "$0")/.."
tag=latest; live=0
while [ $# -gt 0 ]; do
  case "$1" in
    --image) tag="${2:?--image needs a tag}"; shift 2 ;;
    --live) live=1; shift ;;
    *) echo "usage: check-toolchain-parity.sh [--image TAG] [--live]" >&2; exit 2 ;;
  esac
done
pin=scripts/nim-toolchain.pin
# shellcheck disable=SC1090
. "$pin" || exit 2
rc=0
fail() { echo "DRIFT: $*" >&2; rc=1; }
case "${NIM_ARTIFACT_DIGEST:-}" in
  sha256:????????????????????????????????????????????????????????????????) ;;
  *) echo "$pin: NIM_ARTIFACT_DIGEST is not a sha256 digest" >&2; exit 2 ;;
esac

# Containerfile ARG defaults mirror the pin.
for k in NIM_ARTIFACT_PACKAGE NIM_ARTIFACT_TAG NIM_ARTIFACT_DIGEST; do
  want="${!k}"
  got="$(sed -n "s/^ARG $k=//p" scripts/Containerfile)"
  [ "$got" = "$want" ] || fail "scripts/Containerfile ARG $k='$got', pin says '$want'"
done
# CI reads the pin instead of carrying its own copy.
act=.github/actions/setup-symex-linux/action.yml
command grep -q 'scripts/nim-toolchain.pin' "$act" || fail "$act does not read $pin"
if command grep -Eq 'tag: *[0-9]+\.[0-9]+\.[0-9]+-linux' "$act"; then
  fail "$act hardcodes a linux artifact tag instead of the pin"
fi

img="localhost/nelli-dev:$tag"
if command -v podman >/dev/null 2>&1 && podman image exists "$img"; then
  lbl="$(podman image inspect "$img" --format '{{index .Labels "dev.leavitt.nelli.nim-artifact-digest"}}')"
  rec="$(podman run --rm "$img" sed -n 's/^artifact_digest=//p' /etc/nelli-toolchain 2>/dev/null)"
  [ "$lbl" = "$NIM_ARTIFACT_DIGEST" ] || fail "$img label says '${lbl:-<none>}', pin says $NIM_ARTIFACT_DIGEST (rebuild: scripts/build-dev-image.sh)"
  [ "$rec" = "$NIM_ARTIFACT_DIGEST" ] || fail "$img /etc/nelli-toolchain says '${rec:-<none>}', pin says $NIM_ARTIFACT_DIGEST"
else
  echo "note: $img not present; image check skipped" >&2
fi

if [ "$live" = 1 ]; then
  tok="$(curl -fsS "https://ghcr.io/token?scope=repository:$NIM_ARTIFACT_PACKAGE:pull&service=ghcr.io" | sed -n 's/.*"token":"\([^"]*\)".*/\1/p')"
  now="$(curl -fsSI -H "Authorization: Bearer $tok" -H 'Accept: application/vnd.oci.image.manifest.v1+json' \
    "https://ghcr.io/v2/$NIM_ARTIFACT_PACKAGE/manifests/$NIM_ARTIFACT_TAG" | tr -d '\r' | sed -n 's/^[Dd]ocker-[Cc]ontent-[Dd]igest: //p')"
  [ -n "$now" ] || { echo "registry did not answer for $NIM_ARTIFACT_TAG" >&2; exit 2; }
  [ "$now" = "$NIM_ARTIFACT_DIGEST" ] || fail "registry tag $NIM_ARTIFACT_TAG now resolves to $now, pin says $NIM_ARTIFACT_DIGEST (republished; review, then update the pin and rebuild)"
fi
[ "$rc" = 0 ] && echo "toolchain parity ok: $NIM_ARTIFACT_TAG $NIM_ARTIFACT_DIGEST"
exit "$rc"
