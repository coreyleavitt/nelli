#!/usr/bin/env bash
# Full-suite parallel sweep: runs every tests/t*.nim through
# scripts/dt-bounded.sh and writes one result line per (backend, file).
#
# Why this exists (RFC-0010 slice A0). Before it there was no way to run the
# whole suite at all:
#   * scripts/psweep.sh sweeps only tests/tsymex_*.nim.
#   * `nimble test` is a single serial loop that, when this was written,
#     included six tsymex_r6_* suites which hung forever on Linux/podman,
#     so it never finished in the container. (RFC-0005 S8k and S8q fixed
#     all six; see `known_linux_hangs` below.)
# Any RFC round whose purpose is detecting behavioural fallout across the
# suite needs a sweep it can actually run, twice, and diff — see
# scripts/sweep-diff.sh.
#
# The run set is the FILESYSTEM (tests/t*.nim), not nelli.nimble's
# hand-maintained list. Those two disagree: dozens of test files on disk are
# registered nowhere, so they run in no sweep and no CI. Sweeping the
# filesystem covers them; the drift report names them so the gap stays
# visible instead of silently widening.
#
# Deliberately no count here. This comment carried "92" until RFC-0010's
# stage-4 review found it had been stale in both directions -- the branch's
# own work had moved it to 88 while main was at 94. A number restated in
# prose next to the code that computes it is a number that goes stale; read
# <outlog>.drift, which is generated and therefore cannot lie.
#
# Usage: scripts/sweep.sh [--host] [--derive] [-j N] [-t SECS] [-b c|cpp] [-i IMAGE] [-f REGEX] <outlog>
#   --host    no podman (RFC-0016 CI-A2): run each test directly on this
#             machine through the same scripts/run-one.sh the container runs,
#             under the same hard-kill timeout. Needs `nim` and gcc on PATH,
#             Z3 reachable (LD_LIBRARY_PATH, and NELLI_Z3_INCLUDE for the
#             headers) and PCRE 1 for the regex suites -- what the CI-A1
#             setup-* actions provision. -i is ignored. The log, .summary,
#             .env, .drift and .warnings keep the podman shapes (the .env /
#             summary first line reads `host=... Z3=...` instead of `image=...
#             Z3=...`), so sweep-diff.sh compares a host log with a podman log.
#   --derive  take the run set from nelli.nimble's `test` task instead of the
#             tests/t*.nim glob: exactly the registered suite, which is what a
#             CI leg should run. .drift still reports files on disk that are
#             registered nowhere. A registered name with no file is reported
#             there and not run. Composes with -f.
#   -j N      parallel jobs (default 6)
#   -t SECS   per-test timeout passed to dt-bounded.sh (default 900)
#   -b BE     backend, c or cpp (default c; `nimble test` uses c only)
#   -i IMAGE  dev image variant, localhost/nelli-dev:IMAGE (default `latest`,
#             the distro Z3; `z3-4.13.4` is the Z3 4.13.4 row). Built on demand.
#             Passed to every dt-bounded.sh worker; composes with -b and -f.
#   -f REGEX  restrict the run set to basenames matching REGEX
#
# Output contract, one line per test, in completion order:
#
#     <rc> <backend> <file>
#
# A test PASSED iff the first field is exactly `0`. The first field is `skip`
# for the known-hang list below (empty since RFC-0005 S8t). Anything else is a failure; `137` specifically
# is a dt-bounded.sh timeout kill and is counted separately in the summary,
# because a kill and an assertion failure need different responses and look
# identical in a bare count.
#
# The default timeout is 900s and that number is load-bearing, not padding. At
# 300s this sweep reported five suites as rc=137 that all pass under 900s on a
# quiet machine -- and rc=137 is exactly what a genuinely-hanging suite
# reports, so a tight bound manufactures members of the known-hang class. If
# something else on the box is eating cores (check `podman stats` for orphaned
# containers), raise it further rather than reading the kills as hangs.
#
# This script's own exit status is 0 unless it could not run at all — the log
# is the sole source of truth, matching psweep.sh's contract.
#
# Side files written next to the log:
#   <outlog>.drift    registry drift against nelli.nimble
#   <outlog>.failures/  stdout+stderr tails of each non-zero test (only if any)
#   <outlog>.summary  the image/Z3 line, counts, and the failing set
#   <outlog>.env      the image and the libz3 version that actually ran, so a
#                     baseline is self-describing. (Kept out of <outlog>
#                     itself: sweep-diff.sh keys every line of that file.)
set -uo pipefail
cd "$(dirname "$0")/.."

jobs=6
timeout_secs=900
backend=c
filter=
image=latest
host=0
derive=0

# Long options first (getopts has none); everything else falls through.
args=()
for a in "$@"; do
  case "$a" in
    --host) host=1 ;;
    --derive) derive=1 ;;
    *) args+=("$a") ;;
  esac
done
set -- ${args[@]+"${args[@]}"}

usage="usage: sweep.sh [--host] [--derive] [-j N] [-t SECS] [-b c|cpp] [-i IMAGE] [-f REGEX] <outlog>"
while getopts ":j:t:b:i:f:" opt; do
  case "$opt" in
    j) jobs="$OPTARG" ;;
    t) timeout_secs="$OPTARG" ;;
    b) backend="$OPTARG" ;;
    i) image="$OPTARG" ;;
    f) filter="$OPTARG" ;;
    *) echo "$usage" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
outlog="${1:?$usage}"

case "$backend" in c|cpp) ;; *) echo "sweep.sh: backend must be c or cpp" >&2; exit 2 ;; esac

# Suites that hang INDEFINITELY under Linux/podman (verified, killed, not
# merely slow). Sweeping them costs a timeout kill each and tells us nothing we
# do not already know, so they are skipped and reported as `skip` rather than
# silently dropped.
#
# Every entry here must name its own reason, and the entry must cover exactly
# the suite that hangs -- no more. A skip-list entry that quietly covers more
# than it claims is how a real defect stays hidden: see the `trequiresinit`
# incident, where a stale "fails on Windows" ledger note had maintainers
# skip-listing a genuine bug that was red on BOTH platforms.
known_linux_hangs=(
  # The six r6 suites that hung under Linux/podman (verified to 1500s)
  # while PASSING on the symex-mingw Windows leg are all swept again.
  # RFC-0005 S8k (the `maxSeqLen` cap, `seqQueryRLimit`, byte tests in
  # character form, loop feasibility pruning) freed b1_stringbacked,
  # b3_scanpair, n10_coverage_matrix and nulwitness. RFC-0005 S8q freed
  # b7r_bytescan (a scan-pair offset param is an Int, not a bit-vector
  # bridged into the string query; a conjunctive `symexAssume` no longer
  # forks per conjunct) and b7r2_pathscope: measured under a concurrent
  # -j 6 gate sweep, b7r_bytescan 51s (c) / 54s (cpp) and b7r2_pathscope
  # 279s (c) / 277s (cpp), every check passing.
  # RFC-0005 S8t removed the last entry, tsymex_snd3_6_equality_loop (SND-3-6,
  # one Z3 query that ground past its rlimit when the entry was added). It now
  # passes all three checks in 26-49s (c) / 43-62s (cpp), measured at a58856d
  # and at S8t with the host at load average 20-24. The list is empty: nothing is known to hang
  # on Linux/podman. Add an entry only for a suite measured to hang (killed,
  # not merely slow), with its reason.
)

is_known_hang() {
  local n="$1" h
  for h in "${known_linux_hangs[@]}"; do [ "$n" = "$h" ] && return 0; done
  return 1
}

# ---- registry (nelli.nimble's test task) and disk -----------------------
# Needed before the run set (--derive) and again for the drift report below.
registered="$(mktemp)"; ondisk="$(mktemp)"
warn_dir="$(mktemp -d)"; export warn_dir
trap 'rm -f "$registered" "$ondisk"; rm -rf "$warn_dir"' EXIT

# Strip comments BEFORE extracting quoted names: the list is heavily
# commented, and a comment containing a quoted string (e.g. an explanatory
# `# a = (1, "alpha")`) was otherwise scraped as a registered suite and
# reported as "registered but MISSING on disk" -- a phantom that made the
# drift report cry wolf about a registration gap that did not exist.
sed -n '/for f in \[/,/\]:/p' nelli.nimble \
  | sed 's/#.*$//' \
  | grep -o '"[^"]*"' | tr -d '"' | LC_ALL=C sort -u > "$registered"
for f in tests/t*.nim; do [ -e "$f" ] && basename "$f" .nim; done \
  | LC_ALL=C sort -u > "$ondisk"


# ---- run set -------------------------------------------------------------
run_set=()
if [ "$derive" -eq 1 ]; then
  candidates=()
  while IFS= read -r name; do
    [ -e "tests/$name.nim" ] && candidates+=("tests/$name.nim")
  done < "$registered"
else
  candidates=(tests/t*.nim)
fi
for f in ${candidates[@]+"${candidates[@]}"}; do
  [ -e "$f" ] || continue
  name="$(basename "$f" .nim)"
  if [ -n "$filter" ]; then
    printf '%s' "$name" | grep -Eq "$filter" || continue
  fi
  run_set+=("$f")
done

if [ "${#run_set[@]}" -eq 0 ]; then
  echo "sweep.sh: run set is empty${filter:+ (filter: $filter)}" >&2
  exit 2
fi

: > "$outlog"

# ---- which Z3 ran ---------------------------------------------------------
# Ask the environment itself (compile and run a one-line C probe against its
# libz3) rather than trusting a tag or a version file, so the record cannot
# disagree with reality.
write_probe() {
  printf "%s\n" "#include <stdio.h>" "#include <z3.h>" \
    "int main(void){puts(Z3_get_full_version());return 0;}"
}
if [ "$host" -eq 1 ]; then
  command -v nim >/dev/null || { echo "sweep.sh --host: nim not on PATH" >&2; exit 2; }
  command -v gcc >/dev/null || { echo "sweep.sh --host: gcc not on PATH" >&2; exit 2; }
  probe_dir="$(mktemp -d)"
  write_probe > "$probe_dir/zv.c"
  probe_l=()
  IFS=: read -ra ld_dirs <<< "${LD_LIBRARY_PATH:-}"
  for d in ${ld_dirs[@]+"${ld_dirs[@]}"}; do [ -n "$d" ] && probe_l+=("-L$d"); done
  z3_full="$(gcc ${NELLI_Z3_INCLUDE:+-I"$NELLI_Z3_INCLUDE"} -o "$probe_dir/zv" "$probe_dir/zv.c" \
      ${probe_l[@]+"${probe_l[@]}"} -lz3 2>&1 && "$probe_dir/zv" 2>&1 | tail -n1)"
  z3_full="$(printf '%s\n' "$z3_full" | tail -n1)"
  rm -rf "$probe_dir"
  z3_full="${z3_full#Z3 }"
  [ -n "$z3_full" ] || z3_full="unknown"
  env_line="host=$(uname -sr) gcc=$(gcc -dumpfullversion) nim=$(nim --version | head -n1 | awk '{print $4}') Z3=$z3_full"
  # Same compile command as the container (scripts/run-one.sh); the Nim
  # artifact ships Nim alone, so the C compiler and Z3 headers are named here.
  export NELLI_HOST=1
  export NELLI_NIM_FLAGS="--cc:gcc --colors:off${NELLI_Z3_INCLUDE:+ --cincludes:$NELLI_Z3_INCLUDE}"
  warn_root="$PWD"
else
  podman image exists "localhost/nelli-dev:$image" || scripts/build-dev-image.sh "$image" >&2 || exit 2
  z3_full="$(podman run --rm "localhost/nelli-dev:$image" bash -c "$(declare -f write_probe); write_probe > /tmp/zv.c && gcc -o /tmp/zv /tmp/zv.c -lz3 && /tmp/zv" 2>&1 | tail -n1)"
  z3_full="${z3_full#Z3 }"
  [ -n "$z3_full" ] || z3_full="unknown"
  env_line="image=localhost/nelli-dev:$image Z3=$z3_full"
  warn_root=/work
fi
echo "$env_line" > "$outlog.env"
failure_dir="$outlog.failures"; rm -rf "$failure_dir"
export NELLI_IMAGE="$image" warn_root failure_dir

# ---- registry drift ------------------------------------------------------
# nelli.nimble's `test` task list is hand-maintained; symex-mingw derives its
# corpus from it and the fuzzer legs glob plus a named list. A file absent
# from it runs nowhere in CI. Report both directions.
drift="$outlog.drift"
{
  echo "# registry drift: tests/t*.nim on disk vs nelli.nimble's test task"
  echo "# generated by scripts/sweep.sh"
  echo
} > "$drift"

unregistered_n=$(LC_ALL=C comm -23 "$ondisk" "$registered" | wc -l | tr -d ' ')
missing_n=$(LC_ALL=C comm -13 "$ondisk" "$registered" | wc -l | tr -d ' ')
{
  echo "## on disk but UNREGISTERED ($unregistered_n) — run in no sweep task and no CI"
  LC_ALL=C comm -23 "$ondisk" "$registered"
  echo
  echo "## registered but MISSING on disk ($missing_n) — nimble test would fail"
  LC_ALL=C comm -13 "$ondisk" "$registered"
} >> "$drift"

# ---- skip-list hygiene (finding D4) --------------------------------------
# known_linux_hangs entries must still name a real, registered suite --
# mirrors the guard derive-ci-suites.ps1 already applies to ITS OWN skip
# list (throws if a skip-listed suite isn't present in the nimble task). A
# stale entry here (file deleted/renamed, or dropped from nelli.nimble)
# skip-lists nothing real while silently costing nothing to notice.
#
# Deliberately NOT attempted: detecting an entry whose hang was fixed
# upstream and is now just stale. That claim can only be proven by actually
# running the suite unbounded to confirm it terminates -- exactly the cost
# this skip list exists to avoid paying on every sweep. Left undone.
stale_skiplist=()
for h in "${known_linux_hangs[@]}"; do
  ok=1
  grep -qxF "$h" "$ondisk" || ok=0
  grep -qxF "$h" "$registered" || ok=0
  [ "$ok" -eq 1 ] || stale_skiplist+=("$h")
done
stale_n="${#stale_skiplist[@]}"
{
  echo
  echo "## known_linux_hangs entries STALE — no file on disk and/or not in nelli.nimble's test task ($stale_n)"
  printf '%s\n' "${stale_skiplist[@]}"
} >> "$drift"

# ---- sweep ---------------------------------------------------------------
# Compiler diagnostics matter here: the codebase deliberately uses
# compile-time `warning()` to report instrumentation gaps no other
# mechanism can detect (e.g. `{.jitterPoints.}` warning when it cannot
# instrument a proc). dt-bounded.sh already keeps compiler stderr separate
# from the test's own stdout (verified: Nim diagnostics land on stderr,
# `nim c -r` program output lands on stdout) -- no changes needed there.
# Capture that stderr per test instead of discarding it, filter it down to
# `Warning:` lines whose location is under this repo's own src/ or tests/
# (excluding stdlib and nimble-deps noise, which live under other paths
# inside the container, e.g. `/.cache/milpa/...`), and stash any hits under
# $warn_dir keyed by a name unique per (backend, file) so parallel workers
# never interleave into the same file. Never affects rc/pass-fail.
#
# The sidecar is written in a CANONICAL, path-relative, order-stable form,
# not the raw compiler line, because scripts/sweep-diff.sh diffs it against
# a baseline (this suite is never green/warning-free on a good day either,
# so "did any warnings appear" is as useless a question as "did the sweep
# pass" -- the delta is the signal). Concretely: the `/work/` container
# mount prefix is stripped (host-relative, so it matches a baseline taken
# from a different checkout path), and the `(line, col)` location is
# dropped entirely -- an edit that only shifts a warning's line number
# (e.g. inserting a comment above it) must not read as a resolved warning
# plus a new one. What survives is file + message + category, which is
# what actually identifies a distinct diagnostic. Identical (file,
# message, category) triples are then collapsed to one line with an
# `xN` occurrence-count suffix and the whole set is sorted, so the sidecar
# never varies with compile-order nondeterminism.
run_one() {
  local b="$1" f="$2" t="$3" name rc stderr_tmp filtered warn_n
  name="$(basename "$f" .nim)"
  stderr_tmp="$(mktemp)"; stdout_tmp="$(mktemp)"
  scripts/dt-bounded.sh "$b" "$f" "$t" >"$stdout_tmp" 2>"$stderr_tmp"
  rc=$?
  # A failure leaves its output tail in <outlog>.failures/ so a CI log that
  # only has "rc=1" is diagnosable. Sidecar only; never touches the log.
  if [ "$rc" -ne 0 ]; then
    mkdir -p "$failure_dir"
    { echo "## stdout (tail)"; tail -n 60 "$stdout_tmp"
      echo "## stderr (tail)"; tail -n 60 "$stderr_tmp"; } > "$failure_dir/$b.$name"
  fi
  rm -f "$stdout_tmp"
  filtered="$(grep -E "^$warn_root/(src|tests)/.*Warning:" "$stderr_tmp" 2>/dev/null || true)"
  if [ -n "$filtered" ]; then
    warn_n=$(printf '%s\n' "$filtered" | wc -l | tr -d ' ')
  else
    warn_n=0
  fi
  if [ "$warn_n" -gt 0 ]; then
    {
      echo "## $b $f ($warn_n warning(s))"
      printf '%s\n' "$filtered" \
        | sed -E "s#^$warn_root/##; s#\([0-9]+, *[0-9]+\) Warning: #: #" \
        | LC_ALL=C sort \
        | uniq -c \
        | awk '{c=$1; $1=""; sub(/^ /, ""); print (c > 1) ? $0 " x" c : $0}'
      echo
    } > "$warn_dir/$b.$name"
  fi
  rm -f "$stderr_tmp"
  echo "$rc $b $f $warn_n"
}
export -f run_one

{
  for f in "${run_set[@]}"; do
    name="$(basename "$f" .nim)"
    if is_known_hang "$name"; then
      echo "skip $backend $f 0" >> "$outlog"
      continue
    fi
    # NUL-delimit fields -- no shell string can ever contain a NUL byte, so
    # it can never collide with real field content (a path could otherwise
    # contain a space).
    printf '%s\0%s\0%s\0' "$backend" "$f" "$timeout_secs"
  done
} | xargs -0 -P"$jobs" -n3 bash -c 'run_one "$0" "$1" "$2"' >> "$outlog"

# ---- warnings sidecar -----------------------------------------------------
warnlog="$outlog.warnings"
{
  echo "# compiler warnings from THIS repo's src/ and tests/ (stdlib/deps filtered out)"
  echo "# generated by scripts/sweep.sh -- does not affect pass/fail"
  echo
  if [ -n "$(ls -A "$warn_dir" 2>/dev/null)" ]; then
    cat "$warn_dir"/* 2>/dev/null
  else
    echo "(none)"
  fi
} > "$warnlog"

# ---- summary -------------------------------------------------------------
summary="$outlog.summary"
derive_note=; [ "$derive" -eq 1 ] && derive_note=" derive=test-task"
pass=$(awk '$1 == "0"' "$outlog" | wc -l | tr -d ' ')
skip=$(awk '$1 == "skip"' "$outlog" | wc -l | tr -d ' ')
fail=$(awk '$1 != "0" && $1 != "skip"' "$outlog" | wc -l | tr -d ' ')
killed=$(awk '$1 == "137"' "$outlog" | wc -l | tr -d ' ')
warn_tests=$(awk '$4+0 > 0' "$outlog" | wc -l | tr -d ' ')
warn_total=$(awk '{s+=$4+0} END{print s+0}' "$outlog")
{
  echo "$env_line"
  echo "backend=$backend jobs=$jobs timeout=${timeout_secs}s${derive_note}${filter:+ filter=$filter}"
  echo "pass=$pass fail=$fail (of which timeout-killed=$killed) skip=$skip total=$((pass + fail + skip))"
  echo "unregistered=$unregistered_n missing=$missing_n stale_skiplist=$stale_n  (see $drift)"
  echo "warn_tests=$warn_tests warn_total=$warn_total  (see $warnlog) -- trend only, never zero; the gate is scripts/sweep-diff.sh's warnings delta against a baseline, not this total"
  if [ "$fail" -gt 0 ]; then
    echo
    echo "## failing"
    awk '$1 != "0" && $1 != "skip"' "$outlog" | LC_ALL=C sort -k3
  fi
} > "$summary"
cat "$summary" >&2
exit 0
