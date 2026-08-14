#!/usr/bin/env bash
# Bounded single-test runner: like dt.sh, but HARD-KILLS the run (and its
# podman container) after a timeout so a non-terminating symex query can never
# peg a core indefinitely. Born from the F5 incident, where an
# int2bv(bv2int(x)) mixed-theory query made Z3 spin a full core for 24min+ and
# left orphaned containers running for hours.
#
# Usage: scripts/dt-bounded.sh <c|cpp> tests/foo.nim [timeout_secs]
# Exit:  0 = passed/ran to completion; 137 = HUNG (killed at timeout);
#        other = compile/test failure.
set -uo pipefail
cd "$(dirname "$0")/.."
backend="${1:?usage: dt-bounded.sh <c|cpp> <test.nim> [timeout_secs]}"; shift
test_file="${1:?usage: dt-bounded.sh <c|cpp> <test.nim> [timeout_secs]}"; shift
timeout_secs="${1:-180}"
img=localhost/nelli-dev:latest
podman image exists "$img" || scripts/build-dev-image.sh

# Unique container name so we can guarantee teardown even if `timeout` kills
# only the podman client and leaves the container detached.
cname="dtbound_$(basename "$test_file" .nim)_${backend}_$$"
cleanup() { podman rm -f "$cname" >/dev/null 2>&1 || true; }
trap cleanup EXIT
cleanup

timeout --signal=KILL "$timeout_secs" podman run --rm --name "$cname" \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work \
  "$img" \
  bash -c 'nim "$1" -r --threads:on --hints:off "$2"' _ "$backend" "$test_file"
rc=$?
if [ "$rc" -eq 137 ] || [ "$rc" -eq 124 ]; then
  echo ">>> HUNG: $test_file ($backend) killed after ${timeout_secs}s — treat as an engine non-termination defect, not a slow test." >&2
  exit 137
fi
exit "$rc"
