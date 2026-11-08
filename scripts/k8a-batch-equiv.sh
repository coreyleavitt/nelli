#!/usr/bin/env bash
# RFC-0016 K8a-job: the batch-equivalence check. Two batches of N/2 programs
# (-d:k8aFirst) must reproduce exactly the programs and verdicts of the same
# slice of one N-program run, for both runners the nightly drives:
#   tests/tsymex_0016_k8a_gen.nim   the `k8a-verdict` lines (every program and twin)
#   tests/s0016_k8a_threeway.nim    the `K8A3W` rows (head verdict + native)
# The nightly splits its budget into batches because one compile holds every
# program at once (about 0.2 GB each); this is what lets it do so.
#
# Usage: scripts/k8a-batch-equiv.sh [-n TOTAL (even, default 6)] [-s SEED] [-b c|cpp]
# Env:   as dt-bounded.sh (NELLI_HOST, NELLI_NIM_FLAGS).
# Exit:  0 = identical, 1 = a difference (shown as a diff), 2 = a run failed.
set -uo pipefail
cd "$(dirname "$0")/.."
total=6 seed=20261108 backend=c
while getopts ":n:s:b:" opt; do
  case "$opt" in
    n) total="$OPTARG" ;; s) seed="$OPTARG" ;; b) backend="$OPTARG" ;;
    *) echo "usage: k8a-batch-equiv.sh [-n TOTAL] [-s SEED] [-b c|cpp]" >&2; exit 2 ;;
  esac
done
[ $(( total % 2 )) -eq 0 ] && [ "$total" -ge 2 ] || { echo "k8a-batch-equiv: -n must be even and >= 2" >&2; exit 2; }
half=$(( total / 2 ))
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
base_flags="${NELLI_NIM_FLAGS:-}"

# run <test> <tag> <first> <count>
run() {
  NELLI_NIM_FLAGS="$base_flags -d:k8aSeed=$seed -d:k8aFirst=$3 -d:k8aCount=$4" \
    scripts/dt-bounded.sh "$backend" "$1" 900 > "$work/$2.log" 2>&1 \
    || { echo "k8a-batch-equiv: $1 ($2: first=$3 count=$4) failed, rc=$?" >&2; tail -20 "$work/$2.log" >&2; exit 2; }
}

bad=0
for spec in "tests/tsymex_0016_k8a_gen.nim:k8a-verdict" "tests/s0016_k8a_threeway.nim:K8A3W"; do
  test="${spec%%:*}" tag="${spec##*:}" n="$(basename "${spec%%:*}" .nim)"
  run "$test" "$n-whole" 0 "$total"
  run "$test" "$n-a" 0 "$half"
  run "$test" "$n-b" "$half" "$half"
  command grep -a "^$tag" "$work/$n-whole.log" | sort > "$work/$n.whole"
  { command grep -a "^$tag" "$work/$n-a.log"; command grep -a "^$tag" "$work/$n-b.log"; } | sort > "$work/$n.batches"
  lines="$(wc -l < "$work/$n.whole")"
  [ "$lines" -gt 0 ] || { echo "k8a-batch-equiv: $test produced no $tag lines" >&2; exit 2; }
  if diff -u "$work/$n.whole" "$work/$n.batches" > "$work/$n.diff"; then
    echo "k8a-batch-equiv: $test: $lines $tag lines, two batches of $half == one run of $total"
  else
    echo "k8a-batch-equiv: $test: DIFFERENCE between one run of $total and two batches of $half"
    cat "$work/$n.diff"
    bad=1
  fi
done
exit "$bad"
