#!/usr/bin/env bash
# RFC-0016 CI-B, the "parser VM" cell (section 2.5): run the compile-time VM
# let-aliasing guard (src/nelli/smt/vm_alias_guard.nim) over a SAMPLED slice
# of the corpus.
#
# What the guard is. The symex parser runs in Nim's compile-time macro VM, where
# a `let` that aliases a mutable NimNode can be mutated through the alias
# (RFC-0005 S8x/S8ab/S8ah). vm_alias_guard walks every macro's typed body for
# that shape. It runs two ways: as the unconditional `check`s of
# tests/tsymex_rfc0005_s8ab_letaudit.nim, and as an opt-in BUILD-TIME gate
# (`doAssert`) wired into symex.nim's and concolic.nim's trailing
# `when defined(nelliVmAliasAudit)` blocks. A test that imports symex therefore
# audits at compile time when built with -d:nelliVmAliasAudit.
#
# What this runs. The guard's own suite plus a deterministic sample of the
# registered tsymex_* tests, each built and run with -d:nelliVmAliasAudit on
# the host (NELLI_HOST). The sample is every STRIDE-th test of the sorted
# list, starting at OFFSET, and the offset follows the day of the year, so the
# nightly slices rotate through the whole corpus in STRIDE days.
#
# Usage: scripts/vm-alias-slice.sh [-n COUNT] [-o OFFSET] [-t SECS] <outlog>
#   -n COUNT   about this many sampled tests (default 12)
#   -o OFFSET  slice offset (default: day of year modulo the stride)
#   -t SECS    per-test timeout (default 900)
# Output: <outlog> in sweep.sh's `<rc> <backend> <file> <warn>` shape,
# <outlog>.times, and <outlog>.summary. Exit 0 if the log was written; the
# gate reads the log (a non-zero rc is the finding).
set -uo pipefail
cd "$(dirname "$0")/.."
count=12; offset=; tmo=900
while getopts ":n:o:t:" o; do
  case "$o" in n) count="$OPTARG" ;; o) offset="$OPTARG" ;; t) tmo="$OPTARG" ;; *) sed -n 21,22p "$0" >&2; exit 2 ;; esac
done
shift $((OPTIND - 1))
outlog="${1:?usage: vm-alias-slice.sh [-n N] [-o OFF] [-t SECS] <outlog>}"

mapfile -t all < <(sed -n '/for f in \[/,/\]:/p' nelli.nimble | sed 's/#.*$//' \
  | grep -o '"[^"]*"' | tr -d '"' | grep '^tsymex_' | LC_ALL=C sort -u)
n=${#all[@]}
[ "$n" -ge 100 ] || { echo "vm-alias-slice.sh: only $n tsymex_ tests registered" >&2; exit 2; }
stride=$(( n / count )); [ "$stride" -ge 1 ] || stride=1
[ -n "$offset" ] || offset=$(( 10#$(date -u +%j) % stride ))
guard=tsymex_rfc0005_s8ab_letaudit
set_=("$guard")
for (( i = offset; i < n; i += stride )); do
  [ "${all[$i]}" = "$guard" ] || set_+=("${all[$i]}")
done

export NELLI_HOST=1
export NELLI_NIM_FLAGS="--cc:gcc --colors:off --path:src --path:_deps/z3/src --path:_deps/softlink/src${NELLI_Z3_INCLUDE:+ --cincludes:$NELLI_Z3_INCLUDE} -d:nelliVmAliasAudit"
: > "$outlog"; : > "$outlog.times"
echo "vm-alias-slice: ${#set_[@]} tests (stride $stride, offset $offset of $n registered)" >&2
for t in "${set_[@]}"; do
  f="tests/$t.nim"; t0=$EPOCHREALTIME
  scripts/dt-bounded.sh c "$f" "$tmo" > "$outlog.$t.out" 2>&1; rc=$?
  echo "$rc c $f 0" >> "$outlog"
  awk -v a="$t0" -v b="$EPOCHREALTIME" -v f="$f" 'BEGIN { printf "%.1f c %s\n", b - a, f }' >> "$outlog.times"
  [ "$rc" -eq 0 ] && rm -f "$outlog.$t.out" || { echo "FAILED rc=$rc: $t" >&2; tail -n 40 "$outlog.$t.out" >&2; }
done
{
  echo "vm_alias_guard slice: ${#set_[@]} tests, stride $stride, offset $offset, registered $n"
  echo "pass=$(awk '$1 == "0"' "$outlog" | wc -l | tr -d ' ') fail=$(awk '$1 != "0"' "$outlog" | wc -l | tr -d ' ')"
  awk '$1 != "0" {print "FAIL " $3}' "$outlog"
} > "$outlog.summary"
cat "$outlog.summary" >&2
exit 0
