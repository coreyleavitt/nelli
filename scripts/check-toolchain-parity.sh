#!/usr/bin/env bash
# Toolchain parity gate: the Nim and the Z3 the local dev image runs must be the
# ones CI's symex-linux leg runs, by digest / sha256. All read scripts/nim-toolchain.pin.
#
# Usage: scripts/check-toolchain-parity.sh [--image TAG] [--live]
#   (default)      static: the pin is well-formed; the Containerfile ARG defaults
#                  and setup-symex-linux both follow it (no hardcoded tag/digest);
#                  and, if localhost/nelli-dev:TAG exists (default latest), its
#                  label and /etc/nelli-toolchain record the pinned digest, its
#                  libz3 and headers are the pinned Z3 version, and no distro Z3
#                  package is installed. An image whose TAG starts with z3-4.13.4
#                  is held to the 4.13.4 row's pin (Z3_4134_*) instead.
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

# Z3: the pin, the Containerfile ARG defaults, CI's action defaults, the nightly
# matrix and the k8a script all name the same release zip hash.
for k in Z3_VERSION Z3_ASSET Z3_SHA256; do
  want="${!k}"
  got="$(sed -n "s/^ARG $k=//p" scripts/Containerfile)"
  [ "$got" = "$want" ] || fail "scripts/Containerfile ARG $k='$got', pin says '$want'"
done
for act in .github/actions/setup-z3-linux/action.yml .github/actions/setup-symex-linux/action.yml; do
  for v in "$Z3_VERSION" "$Z3_ASSET" "$Z3_SHA256"; do
    command grep -q "default: \"$v\"" "$act" || fail "$act has no default \"$v\" (the pin's Z3)"
  done
done
for v in "$Z3_VERSION $Z3_ASSET $Z3_SHA256" "$Z3_4134_VERSION $Z3_4134_ASSET $Z3_4134_SHA256"; do
  command grep -q "$v" scripts/k8a-nightly.sh || fail "scripts/k8a-nightly.sh does not carry the pinned Z3 row '$v'"
done
for h in "$Z3_SHA256" "$Z3_4134_SHA256"; do
  command grep -q "$h" .github/workflows/symex-nightly.yaml || fail "symex-nightly.yaml does not carry Z3 sha256 $h"
done
for k in Z3_VERSION Z3_ASSET Z3_SHA256; do
  kk="${k/Z3_/Z3_4134_}"; want="${!kk}"
  got="$(sed -n "s/^ARG $k=//p" scripts/Containerfile.z3-4.13.4)"
  [ "$got" = "$want" ] || fail "scripts/Containerfile.z3-4.13.4 ARG $k='$got', pin says '$want'"
done

img="localhost/nelli-dev:$tag"
zv="$Z3_VERSION"; zh="$Z3_SHA256"
case "$tag" in z3-4.13.4*) zv="$Z3_4134_VERSION"; zh="$Z3_4134_SHA256" ;; esac
if command -v podman >/dev/null 2>&1 && podman image exists "$img"; then
  lbl="$(podman image inspect "$img" --format '{{index .Labels "dev.leavitt.nelli.nim-artifact-digest"}}')"
  rec="$(podman run --rm "$img" sed -n 's/^artifact_digest=//p' /etc/nelli-toolchain 2>/dev/null)"
  [ "$lbl" = "$NIM_ARTIFACT_DIGEST" ] || fail "$img label says '${lbl:-<none>}', pin says $NIM_ARTIFACT_DIGEST (rebuild: scripts/build-dev-image.sh)"
  [ "$rec" = "$NIM_ARTIFACT_DIGEST" ] || fail "$img /etc/nelli-toolchain says '${rec:-<none>}', pin says $NIM_ARTIFACT_DIGEST"
  zl="$(podman image inspect "$img" --format '{{index .Labels "dev.leavitt.nelli.z3-sha256"}}')"
  zr="$(podman run --rm "$img" sed -n 's/^z3_sha256=//p' /etc/nelli-toolchain 2>/dev/null)"
  zrv="$(podman run --rm "$img" sed -n 's/^z3_version=//p' /etc/nelli-toolchain 2>/dev/null)"
  [ "$zl" = "$zh" ] || fail "$img Z3 label says '${zl:-<none>}', pin says $zh"
  [ "$zr" = "$zh" ] || fail "$img /etc/nelli-toolchain z3_sha256 says '${zr:-<none>}', pin says $zh"
  [ "$zrv" = "$zv" ] || fail "$img /etc/nelli-toolchain z3_version says '${zrv:-<none>}', pin says $zv"
  # What is actually installed, not just what the build recorded.
  have="$(podman run --rm "$img" sh -c 'sed -n "s/^#define Z3_FULL_VERSION[ ]*\"Z3 \([0-9.]*\)\"/\1/p" /opt/z3-headers/z3_version.h; echo "so:$(readlink -f /usr/lib64/libz3.so)"; echo "rpm:$(rpm -qa | grep -i "^\(lib\)\?z3" | tr "\n" " ")"' 2>/dev/null)"
  hv="$(printf '%s\n' "$have" | sed -n '1p')"
  case "$hv" in "$zv"*) ;; *) fail "$img headers say Z3 '${hv:-<none>}', pin says $zv" ;; esac
  case "$(printf '%s\n' "$have" | sed -n 's/^so://p')" in *"libz3.so.${zv%.*}"*) ;; *) fail "$img /usr/lib64/libz3.so does not resolve to libz3.so.${zv%.*}* ($(printf '%s' "$have" | sed -n 's/^so://p'))" ;; esac
  rp="$(printf '%s\n' "$have" | sed -n 's/^rpm://p' | tr -d ' ')"
  [ -z "$rp" ] || fail "$img has a distro Z3 package installed: $rp"
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
[ "$rc" = 0 ] && echo "toolchain parity ok: $NIM_ARTIFACT_TAG $NIM_ARTIFACT_DIGEST; Z3 $zv $zh"
exit "$rc"
