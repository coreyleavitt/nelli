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
#        NELLI_PIN_NOW  if set, forwarded: the clock the pin dates and the
#        seven-day freshness check read (unix seconds).
#        NELLI_NIM_FLAGS  if set, forwarded into the container (run-one.sh reads
#        it), so a caller can pass `-d:name=value` to the test build. A host
#        run reads it directly.
#        NELLI_MEM_MB  if set, a memory guard for the build and the run: a host
#        run applies `ulimit -v` (address space, so an over-budget compile
#        fails with an allocation error instead of taking the machine down); a
#        podman run passes `--memory` (the cgroup OOM-kills the container).
#        Either way the test exits non-zero and the caller names it.
#        NELLI_HOST=1  no podman: run scripts/run-one.sh directly on the host
#        under the same hard-kill timeout (`sweep.sh --host`). The compile
#        command is scripts/run-one.sh either way.
# Exit:  0 = passed/ran to completion; 137 = HUNG (killed at timeout);
#        other = compile/test failure.
set -uo pipefail
cd "$(dirname "$0")/.."
# --self-test: a host run must keep the child's stderr (and close the fds above 2).
if [ "${1:-}" = "--self-test" ]; then
  d="$(mktemp -d)"; trap 'rm -rf "$d"' EXIT
  printf '%s\n' 'echo "child-stdout"' 'echo "child-stderr Warning: x" >&2' 'ls /proc/self/fd | tr "\n" " " > "$FDLOG"' > "$d/stub.sh"
  exec 7>"$d/leaked"   # an fd above 2 that the run must not inherit
  FDLOG="$d/fds" NELLI_HOST=1 NELLI_RUN_ONE="$d/stub.sh" bash "$0" c tests/x.nim 20 >"$d/out" 2>"$d/err"
  exec 7>&-
  grep -q child-stdout "$d/out" || { echo "dt-bounded self-test FAILED: stdout lost"; exit 1; }
  grep -q 'child-stderr Warning' "$d/err" || { echo "dt-bounded self-test FAILED: the child's stderr was lost (an fd-closing loop took the saved stderr with it)"; exit 1; }
  # only fds 0-2 and the one `ls` itself opens may be open
  extra="$(tr ' ' '\n' < "$d/fds" | awk 'NF && $1 > 3')"
  [ -z "$extra" ] || { echo "dt-bounded self-test FAILED: fds above 3 inherited: $extra"; exit 1; }
  echo "dt-bounded self-test: ok"; exit 0
fi
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

# NELLI_WALK_UNITS_LOG (a file the walker appends one line per finished walk
# to: units, target, status -- RFC-0016 K7, how `walkRLimit`'s default is
# measured). An absolute path in the repo is rewritten to its /work path; one
# outside is reached by bind-mounting its directory at the same path.
if [ -n "${NELLI_WALK_UNITS_LOG:-}" ]; then
  wl_dir="$(cd "$(dirname "$NELLI_WALK_UNITS_LOG")" && pwd -P)"
  wl_abs="$wl_dir/$(basename "$NELLI_WALK_UNITS_LOG")"
  case "$wl_abs" in
    "$PWD"/*) pin_args+=(-e "NELLI_WALK_UNITS_LOG=/work${wl_abs#"$PWD"}") ;;
    *)        pin_args+=(-e "NELLI_WALK_UNITS_LOG=$wl_abs" -v "$wl_dir:$wl_dir") ;;
  esac
fi

# NELLI_PIN_NOW (unix seconds) fixes the pin clock (RFC-0016 K1a-last).
[ -n "${NELLI_PIN_NOW:-}" ] && pin_args+=(-e "NELLI_PIN_NOW=$NELLI_PIN_NOW")
# NELLI_UNIVERSE_ROW / NELLI_UNIVERSE_PARTIAL scope the universe join to one CI
# leg (RFC-0016 K1a-ci; scripts/universe-join.sh).
[ -n "${NELLI_UNIVERSE_ROW:-}" ] && pin_args+=(-e "NELLI_UNIVERSE_ROW=$NELLI_UNIVERSE_ROW")
[ -n "${NELLI_UNIVERSE_PARTIAL:-}" ] && pin_args+=(-e "NELLI_UNIVERSE_PARTIAL=$NELLI_UNIVERSE_PARTIAL")

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
  # The loop must carry NO redirection: bash saves the original fd 2 at a high
  # descriptor to restore a `done 2>/dev/null`, the loop then closes that copy, and
  # stderr stays /dev/null for everything after it -- a host sweep read zero compiler
  # warnings (and lost every test's stderr) for exactly this reason.
  # So the host run gets the same two things: its own TMPDIR, and fds above 2
  # closed before the test starts.
  host_tmp="$(mktemp -d)"
  trap 'rm -rf "$host_tmp"' EXIT
  TMPDIR="$host_tmp" timeout --signal=KILL "$timeout_secs" bash -c '
    [ -z "${NELLI_MEM_MB:-}" ] || ulimit -v $(( NELLI_MEM_MB * 1024 )) || exit 125
    for n in $(ls /proc/self/fd); do [ "$n" -gt 2 ] && eval "exec $n>&-"; done
    exec bash "${NELLI_RUN_ONE:-scripts/run-one.sh}" "$@"' _ "$backend" "$test_file"
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
    ${NELLI_MEM_MB:+--memory=${NELLI_MEM_MB}m --memory-swap=${NELLI_MEM_MB}m} \
    ${pin_args[@]+"${pin_args[@]}"} \
    ${NELLI_NIM_FLAGS:+-e NELLI_NIM_FLAGS} \
    "$img" \
    bash scripts/run-one.sh "$backend" "$test_file"
fi
rc=$?
if [ "$rc" -eq 137 ] || [ "$rc" -eq 124 ]; then
  echo ">>> HUNG: $test_file ($backend) killed after ${timeout_secs}s — treat as an engine non-termination defect, not a slow test." >&2
  exit 137
fi
exit "$rc"
