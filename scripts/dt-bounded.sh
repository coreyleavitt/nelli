#!/usr/bin/env bash
# Bounded single-test runner: like dt.sh, but HARD-KILLS the run (and its
# podman container) after a timeout so a non-terminating symex query can never
# peg a core indefinitely. Born from the F5 incident, where an
# int2bv(bv2int(x)) mixed-theory query made Z3 spin a full core for 24min+ and
# left orphaned containers running for hours.
#
# Usage: scripts/dt-bounded.sh <c|cpp> tests/foo.nim [timeout_secs] [extra_nim_args]
# Exit:  0 = passed/ran to completion; 137 = HUNG (killed at timeout);
#        other = compile/test failure.
#
# extra_nim_args, if given, is one whitespace-separated string (e.g.
# "-d:symexQueryStats" or "-d:foo -d:bar") to compile in a suite's real
# assertions instead of a `when defined` skip branch. It is split into an
# array on OUR side of the podman boundary and each flag is then passed to
# the container as its own argv element -- never re-spliced into a string
# the inner shell re-parses -- so multiple flags word-split without ever
# reopening the injection class RFC-0002's L1 finding closed for
# $test_file in this same script. See scripts/sweep.sh's `extra_defines`
# table (itself derived from nelli.nimble, not hand-copied) for the seam
# that feeds this per-file for the whole-suite sweep -- it hands a
# multi-flag value to xargs as one NUL-delimited field (finding C7), never
# a whitespace-delimited one, so a value with embedded spaces reaches
# here as a single argv element instead of getting split mid-transport.
set -uo pipefail
cd "$(dirname "$0")/.."
backend="${1:?usage: dt-bounded.sh <c|cpp> <test.nim> [timeout_secs] [extra_nim_args]}"; shift
test_file="${1:?usage: dt-bounded.sh <c|cpp> <test.nim> [timeout_secs] [extra_nim_args]}"; shift
timeout_secs="${1:-180}"; [ $# -gt 0 ] && shift
extra_nim_args="${1:-}"
# Split on whitespace into real array elements now, while it is still a
# plain shell variable on the host side -- NOT inside the container's `bash
# -c` string, where an unquoted splice would hand the inner shell a single
# blob to word-split (and glob-expand) at execution time.
read -ra extra_args <<< "$extra_nim_args"
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
  bash -c 'b="$1"; f="$2"; shift 2; nim "$b" -r --threads:on --hints:off "$@" "$f"' \
  _ "$backend" "$test_file" "${extra_args[@]}"
rc=$?
if [ "$rc" -eq 137 ] || [ "$rc" -eq 124 ]; then
  echo ">>> HUNG: $test_file ($backend) killed after ${timeout_secs}s — treat as an engine non-termination defect, not a slow test." >&2
  exit 137
fi
exit "$rc"
