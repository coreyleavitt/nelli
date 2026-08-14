#!/usr/bin/env bash
# Parallel regression sweep: runs every tests/tsymex_*.nim on both backends
# via scripts/dt-bounded.sh, xargs -P6. Writes one result line per (file,
# backend) to the given output log: "<rc> <backend> <file>".
#
# Exit-status contract: this script's own exit status does NOT reflect test
# outcomes — run_one always ends in an echo, so xargs never sees a failing
# child, and the script itself always exits 0. The outlog is the sole source
# of truth for pass/fail. Consumers must grep the rc column: any line not
# starting with "0 " is a failure (non-zero rc, including 137 for a
# dt-bounded.sh timeout kill).
set -uo pipefail
cd "$(dirname "$0")/.."
outlog="${1:?usage: psweep.sh <outlog> [timeout_secs]}"
timeout_secs="${2:-180}"
: > "$outlog"

run_one() {
  local b="$1" f="$2"
  local rc
  scripts/dt-bounded.sh "$b" "$f" "$timeout_secs" >/dev/null 2>&1
  rc=$?
  echo "$rc $b $f"
}
export -f run_one

{
  for f in tests/tsymex_*.nim; do
    for b in c cpp; do
      printf '%s %s\n' "$b" "$f"
    done
  done
} | xargs -P6 -n2 bash -c 'run_one "$0" "$1"' >> "$outlog"
