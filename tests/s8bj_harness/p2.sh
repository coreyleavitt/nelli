#!/usr/bin/env bash
# usage: p2.sh <worktree> <scratch/prog.nim> <scratch/input.txt>
# Compiles the probe program once (cached binary) and runs it on the input.
set -uo pipefail
wt="$1"; prog="$2"; input="$3"
cd "$wt"
bin="scratch/bin_$(basename "$prog" .nim)"
timeout --signal=KILL 600 podman run --rm -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work localhost/nelli-dev:latest bash -c '
  p="$1"; b="$2"; i="$3"
  if [ ! -x "$b" ] || [ "$p" -nt "$b" ]; then
    nim c -d:release --hints:off --warnings:off -o:"$b" "$p" >&2 || exit 9
  fi
  "$b" "$i"' _ "$prog" "$bin" "$input"
