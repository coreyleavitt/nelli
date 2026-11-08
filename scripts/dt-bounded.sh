#!/usr/bin/env bash
# Bounded single-test runner: like dt.sh, but HARD-KILLS the run (and its
# podman container) after a timeout so a non-terminating symex query can never
# peg a core indefinitely. Born from the F5 incident, where an
# int2bv(bv2int(x)) mixed-theory query made Z3 spin a full core for 24min+ and
# left orphaned containers running for hours.
#
# Usage: scripts/dt-bounded.sh [-i IMAGE] <c|cpp> tests/foo.nim [timeout_secs]
#   -i IMAGE  dev image variant: runs localhost/nelli-dev:IMAGE (default
#             `latest`; `z3-4.13.4` is the Z3 4.13.4 row). Built on demand by
#             scripts/build-dev-image.sh if missing. Overrides $NELLI_IMAGE.
# Env:   NELLI_PIN_DIR  if set (created if missing), forwarded into the
#        container so files written there land on the host. Relative = relative
#        to the repo root; absolute inside the repo is rewritten to its /work
#        path; absolute outside the repo is bind-mounted at the same path.
#        Unset: nothing is forwarded (the in-repo default tests/.pins/ reaches
#        the host through the /work mount anyway).
#        NELLI_HOST=1  no podman: run scripts/run-one.sh directly on the host
#        under the same hard-kill timeout (`sweep.sh --host`). The compile
#        command is scripts/run-one.sh either way.
# Exit:  0 = passed/ran to completion; 137 = HUNG (killed at timeout);
#        other = compile/test failure.
set -uo pipefail
cd "$(dirname "$0")/.."
image="${NELLI_IMAGE:-latest}"
while getopts ":i:" opt; do
  case "$opt" in
    i) image="$OPTARG" ;;
    *) echo "usage: dt-bounded.sh [-i IMAGE] <c|cpp> <test.nim> [timeout_secs]" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
backend="${1:?usage: dt-bounded.sh [-i IMAGE] <c|cpp> <test.nim> [timeout_secs]}"; shift
test_file="${1:?usage: dt-bounded.sh [-i IMAGE] <c|cpp> <test.nim> [timeout_secs]}"; shift
timeout_secs="${1:-180}"; [ $# -gt 0 ] && shift
img="localhost/nelli-dev:$image"
host="${NELLI_HOST:-}"
[ -n "$host" ] || podman image exists "$img" || scripts/build-dev-image.sh "$image" >&2

# NELLI_PIN_DIR forwarding (see header).
pin_args=()
if [ -n "${NELLI_PIN_DIR:-}" ]; then
  mkdir -p "$NELLI_PIN_DIR"
  pin_abs="$(cd "$NELLI_PIN_DIR" && pwd -P)"
  case "$pin_abs/" in
    "$PWD"/*)  # inside the repo: visible through /work, at the /work path
      pin_args+=(-e "NELLI_PIN_DIR=/work${pin_abs#"$PWD"}") ;;
    *)         # outside: bind-mount at the same path
      pin_args+=(-e "NELLI_PIN_DIR=$pin_abs" -v "$pin_abs:$pin_abs") ;;
  esac
fi

if [ -n "$host" ]; then
  # `timeout` puts the child in its own process group and, on expiry, signals
  # the whole group, so the compiled test binary dies with nim.
  #
  # RFC-0016 CI-A3: the container gives each test a private /tmp and exactly
  # fds 0-2; a bare host gives it the sweep's shared /tmp and whatever fds the
  # CI runner leaked into the process tree. Both bit (run 42434354454):
  #   - tfuzzcovdump / tfuzzcovreset build into /tmp/ptcov_build_<backend>_<n>
  #     and, run side by side, one links the other's tu0.o (`undefined
  #     reference to helper`);
  #   - tfuzzworkerprocess (R23) / tfuzzworkerspawnfailshm (R53) tighten
  #     RLIMIT_NOFILE to (open-fd count + 1) so pipe() must fail, which holds
  #     only if the fds are contiguous; the runner's leaked fds 142 and 145
  #     put the limit at 7, below them, so pipe() took fds 4 and 5 and
  #     succeeded.
  # So the host run gets the same two things: its own TMPDIR, and fds above 2
  # closed before the test starts.
  host_tmp="$(mktemp -d)"
  trap 'rm -rf "$host_tmp"' EXIT
  TMPDIR="$host_tmp" timeout --signal=KILL "$timeout_secs" bash -c '
    for f in /proc/self/fd/*; do n="${f##*/}"; [ "$n" -gt 2 ] 2>/dev/null && eval "exec $n>&-"; done 2>/dev/null
    exec bash scripts/run-one.sh "$@"' _ "$backend" "$test_file"
else
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
    ${pin_args[@]+"${pin_args[@]}"} \
    "$img" \
    bash scripts/run-one.sh "$backend" "$test_file"
fi
rc=$?
if [ "$rc" -eq 137 ] || [ "$rc" -eq 124 ]; then
  echo ">>> HUNG: $test_file ($backend) killed after ${timeout_secs}s — treat as an engine non-termination defect, not a slow test." >&2
  exit 137
fi
exit "$rc"
