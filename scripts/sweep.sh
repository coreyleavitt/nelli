#!/usr/bin/env bash
# Full-suite parallel sweep: runs every tests/t*.nim through
# scripts/dt-bounded.sh and writes one result line per (backend, file).
#
# Why this exists (RFC-0010 slice A0). Before it there was no way to run the
# whole suite at all:
#   * scripts/psweep.sh sweeps only tests/tsymex_*.nim.
#   * `nimble test` is a single serial loop that includes the six
#     tsymex_r6_* suites which hang forever on Linux/podman, so it never
#     finishes in the container.
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
# Usage: scripts/sweep.sh [-j N] [-t SECS] [-b c|cpp] [-f REGEX] <outlog>
#   -j N      parallel jobs (default 6)
#   -t SECS   per-test timeout passed to dt-bounded.sh (default 900)
#   -b BE     backend, c or cpp (default c; `nimble test` uses c only)
#   -f REGEX  restrict the run set to basenames matching REGEX
#
# Output contract, one line per test, in completion order:
#
#     <rc> <backend> <file>
#
# A test PASSED iff the first field is exactly `0`. The first field is `skip`
# for the known-hang list below. Anything else is a failure; `137` specifically
# is a dt-bounded.sh timeout kill and is counted separately in the summary,
# because a kill and an assertion failure need different responses and look
# identical in a bare count.
#
# The default timeout is 900s and that number is load-bearing, not padding. At
# 300s this sweep reported five suites as rc=137 that all pass under 900s on a
# quiet machine -- and rc=137 is exactly what the six genuinely-hanging suites
# report, so a tight bound manufactures members of the known-hang class. If
# something else on the box is eating cores (check `podman stats` for orphaned
# containers), raise it further rather than reading the kills as hangs.
#
# This script's own exit status is 0 unless it could not run at all — the log
# is the sole source of truth, matching psweep.sh's contract.
#
# Two side files are written next to the log:
#   <outlog>.drift    registry drift against nelli.nimble
#   <outlog>.summary  counts plus the failing set
set -uo pipefail
cd "$(dirname "$0")/.."

jobs=6
timeout_secs=900
backend=c
filter=

while getopts ":j:t:b:f:" opt; do
  case "$opt" in
    j) jobs="$OPTARG" ;;
    t) timeout_secs="$OPTARG" ;;
    b) backend="$OPTARG" ;;
    f) filter="$OPTARG" ;;
    *) echo "usage: sweep.sh [-j N] [-t SECS] [-b c|cpp] [-f REGEX] <outlog>" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
outlog="${1:?usage: sweep.sh [-j N] [-t SECS] [-b c|cpp] [-f REGEX] <outlog>}"

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
  # The six r6 suites: hang under Linux/podman (verified to 1500s) while
  # PASSING on the symex-mingw Windows leg. Pre-existing on main.
  tsymex_r6_b1_stringbacked
  tsymex_r6_b3_scanpair
  tsymex_r6_nulwitness
  tsymex_r6_b7r_bytescan
  tsymex_r6_b7r2_pathscope
  tsymex_r6_n10_coverage_matrix
  # SND-3-6, split out of tsymex_snd3_loopdegrade.nim in round 10 of the #163
  # review. ONE Z3 query grinding: flat RSS (so not path growth), hangs at
  # maxLoopUnwind=1 (so not unrolling), hangs on BOTH backends (so not the
  # backend-divergence class SND-3 pins), terminates at queryRLimit=1 but not
  # at 20_000_000. Its parent file is deliberately NOT here: SND-3-1..5 pass in
  # seconds and are live soundness pins. Full measurements in the suite header.
  tsymex_snd3_6_equality_loop
)

is_known_hang() {
  local n="$1" h
  for h in "${known_linux_hangs[@]}"; do [ "$n" = "$h" ] && return 0; done
  return 1
}

# Per-file extra `-d:` defines, keyed by basename (no `tests/` prefix, no
# `.nim` suffix). Some suites gate their real assertions behind a define
# nothing else in the repo ever sets (round-10 #163 liveness finding:
# tprobe_n45stats was registered in nelli.nimble but ran skip() in every
# venue, including this sweep, because -d:symexQueryStats was never
# supplied here either). Keep this table in sync with nelli.nimble's
# `extraDefines` table in the `test` task -- each side names the other in
# a comment so the two cannot silently diverge.
declare -A extra_defines=(
  [tprobe_n45stats]="-d:symexQueryStats"
)

# ---- run set -------------------------------------------------------------
run_set=()
for f in tests/t*.nim; do
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

registered="$(mktemp)"; ondisk="$(mktemp)"
trap 'rm -f "$registered" "$ondisk"' EXIT

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

unregistered_n=$(LC_ALL=C comm -23 "$ondisk" "$registered" | wc -l | tr -d ' ')
missing_n=$(LC_ALL=C comm -13 "$ondisk" "$registered" | wc -l | tr -d ' ')
{
  echo "## on disk but UNREGISTERED ($unregistered_n) — run in no sweep task and no CI"
  LC_ALL=C comm -23 "$ondisk" "$registered"
  echo
  echo "## registered but MISSING on disk ($missing_n) — nimble test would fail"
  LC_ALL=C comm -13 "$ondisk" "$registered"
} >> "$drift"

# ---- sweep ---------------------------------------------------------------
run_one() {
  local b="$1" f="$2" t="$3" extra="$4" rc
  # xargs -n4 groups the flat token stream by count, so a row that dropped
  # its 4th field on an empty extra-define would shift every field after
  # it into the wrong row. NOFLAG is emitted for "no extra define" instead
  # of an empty string so every row always contributes exactly 4 tokens.
  [ "$extra" = "NOFLAG" ] && extra=""
  scripts/dt-bounded.sh "$b" "$f" "$t" "$extra" >/dev/null 2>&1
  rc=$?
  echo "$rc $b $f"
}
export -f run_one

{
  for f in "${run_set[@]}"; do
    name="$(basename "$f" .nim)"
    if is_known_hang "$name"; then
      echo "skip $backend $f" >> "$outlog"
      continue
    fi
    extra="${extra_defines[$name]:-NOFLAG}"
    # No test path, backend, or extra-define entry contains whitespace, so
    # a space-separated quadruple is safe here (same assumption psweep.sh
    # makes for its triple).
    printf '%s %s %s %s\n' "$backend" "$f" "$timeout_secs" "$extra"
  done
} | xargs -P"$jobs" -n4 bash -c 'run_one "$0" "$1" "$2" "$3"' >> "$outlog"

# ---- summary -------------------------------------------------------------
summary="$outlog.summary"
pass=$(awk '$1 == "0"' "$outlog" | wc -l | tr -d ' ')
skip=$(awk '$1 == "skip"' "$outlog" | wc -l | tr -d ' ')
fail=$(awk '$1 != "0" && $1 != "skip"' "$outlog" | wc -l | tr -d ' ')
killed=$(awk '$1 == "137"' "$outlog" | wc -l | tr -d ' ')
{
  echo "backend=$backend jobs=$jobs timeout=${timeout_secs}s${filter:+ filter=$filter}"
  echo "pass=$pass fail=$fail (of which timeout-killed=$killed) skip=$skip total=$((pass + fail + skip))"
  echo "unregistered=$unregistered_n missing=$missing_n  (see $drift)"
  if [ "$fail" -gt 0 ]; then
    echo
    echo "## failing"
    awk '$1 != "0" && $1 != "skip"' "$outlog" | LC_ALL=C sort -k3
  fi
} > "$summary"
cat "$summary" >&2
exit 0
