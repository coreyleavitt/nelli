#!/usr/bin/env bash
# RFC-0016 K1a-ids staleness check: the work-list tables in the RFC must equal
# the render of docs/rfc-data/0016-worklist.toml (scripts/render_worklist.nim).
#
# Usage: scripts/check-worklist.sh [check|write]     (default: check)
#        scripts/check-worklist.sh --self-test       a hand edit must fail it
# Env:   NELLI_HOST=1  run the host's nim (CI); else the nelli-dev container.
#        NELLI_NIM_FLAGS  extra nim flags (host runs name the C compiler).
# Exit:  0 = in step; 1 = stale or malformed (the diff is printed); 2 = misuse.
set -uo pipefail
cd "$(dirname "$0")/.."
nimrun() {  # nimrun <outdir> <mode>
  local out="$1"; shift
  if [ -n "${NELLI_HOST:-}" ]; then
    # shellcheck disable=SC2086
    nim c -r --hints:off ${NELLI_NIM_FLAGS:-} --nimcache:"$out/nc" -o:"$out/render_worklist" scripts/render_worklist.nim "$@"
  else
    local img=localhost/nelli-dev:latest
    podman image exists "$img" || scripts/build-dev-image.sh
    podman run --rm -v "$PWD:/work" -w /work "$img" \
      bash -c "nim c -r --hints:off --nimcache:$out/nc -o:$out/render_worklist scripts/render_worklist.nim $*"
  fi
}
if [ "${1:-}" = "--self-test" ]; then
  rfc=docs/rfc/0016-native-parity-hardening.md
  bash "$0" check >/dev/null || { echo "self-test: the committed RFC is stale" >&2; exit 1; }
  cp "$rfc" "$rfc.selftest.bak"
  trap 'mv -f "$rfc.selftest.bak" "$rfc"' EXIT
  sed -i '0,/^| SND-02 | /s//| SND-02 (hand edit) | /' "$rfc"
  if bash "$0" check >/dev/null 2>&1; then
    echo "self-test: the check passed after a hand edit to a table row" >&2; exit 1
  fi
  echo "self-test: ok (a hand-edited row fails the check)"
  exit 0
fi
mode="${1:-check}"
case "$mode" in check|write) ;; *) echo "usage: check-worklist.sh [check|write|--self-test]" >&2; exit 2;; esac
out="tests/.pins/worklist-build"   # git-ignored; the container sees it under /work
mkdir -p "$out"
nimrun "$out" "$mode"
