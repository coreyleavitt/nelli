#!/usr/bin/env bash
# b11prov.sh <dir>...: provision probe worktrees (nim.cfg, _deps, probe files)
S=/home/corey/.cache/claude-tmp/claude-1000/-home-corey-projects-nim-libs-proptest/23115f9f-e615-40e9-b7af-80f8c6ff8c9d/scratchpad
W=/home/corey/projects/nim/libs/proptest/.claude/worktrees/agent-a2d909c98f2f8f528
for d in "$@"; do
  G=$S/$d
  cp "$W/nim.cfg" "$G/"
  mkdir -p "$G/_deps"
  ln -sfn "$(realpath "$W/_deps/z3")" "$G/_deps/z3"
  ln -sfn "$(realpath "$W/_deps/softlink")" "$G/_deps/softlink"
  cp "$W/tests/zz_b3_b11.nim" "$W/tests/zz_b3_b11.nim.cfg" "$G/tests/"
done
