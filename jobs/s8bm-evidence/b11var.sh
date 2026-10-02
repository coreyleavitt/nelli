#!/usr/bin/env bash
# b11var.sh <tag> [defines...] [-- 413]: run the head probe with -d: defines.
S=/home/corey/.cache/claude-tmp/claude-1000/-home-corey-projects-nim-libs-proptest/23115f9f-e615-40e9-b7af-80f8c6ff8c9d/scratchpad
W=/home/corey/projects/nim/libs/proptest/.claude/worktrees/agent-a2d909c98f2f8f528
tag="$1"; shift
z=""
{ echo "-d:symexQueryStats"
  for d in "$@"; do
    if [ "$d" = 413 ]; then z=413; else echo "-d:$d"; fi
  done; } > "$W/tests/zz_b3_b11.nim.cfg"
bash "$S/b11.sh" "$W" "$tag" $z | grep -E 'q10|TOTAL'
