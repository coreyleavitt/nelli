#!/usr/bin/env bash
# b11.sh <worktree> <tag> [413]: run the B1-1 probe, keep the query summary.
W="$1"; tag="$2"
S=/home/corey/.cache/claude-tmp/claude-1000/-home-corey-projects-nim-libs-proptest/23115f9f-e615-40e9-b7af-80f8c6ff8c9d/scratchpad
cd "$W"
if [ "${3:-}" = 413 ]; then
  "$S/s8o/dt413.sh" "$W" c tests/zz_b3_b11.nim 900 > "$S/b11-$tag.raw" 2>&1
else
  scripts/dt-bounded.sh c tests/zz_b3_b11.nim 900 > "$S/b11-$tag.raw" 2>&1
fi
grep -E '^sx|  q[0-9]|TOTAL' "$S/b11-$tag.raw" | awk '{print $1,$2,$5,$6,$7}' > "$S/b11-$tag.txt"
cat "$S/b11-$tag.txt"
