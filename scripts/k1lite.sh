#!/usr/bin/env bash
# RFC-0016 K1-0: the property on one build row, as one sha- and build-pinned
# fact. Makes a FRESH pin directory, runs the W1 suites that write the seven
# section 5.0 pins into it, then runs tests/tsymex_0016_k1lite.nim over it.
# A stale directory cannot satisfy the join because there is none to reuse.
#
# Usage: scripts/k1lite.sh [-b c|cpp] [-i IMAGE] [-t SECS] [-k KEEPDIR]
#   -b BE    backend (default c)       -i IMAGE  dev image (e.g. z3-4.13.4)
#   -t SECS  per-test timeout (default 900)
#   -k DIR   use DIR (must not exist or be empty) instead of the default
#            tests/.pins/k1lite-<sha>-<be>-<image>-<time> (gitignored)
# Exit: 0 iff every suite and the join passed. A suite failing is reported and
# the join still runs, so the join names what is missing.
set -uo pipefail
cd "$(dirname "$0")/.."
be=c; img=(); secs=900; keep=""
while getopts ":b:i:t:k:" o; do
  case "$o" in
    b) be="$OPTARG" ;; i) img=(-i "$OPTARG") ;; t) secs="$OPTARG" ;; k) keep="$OPTARG" ;;
    *) echo "usage: k1lite.sh [-b c|cpp] [-i IMAGE] [-t SECS] [-k DIR]" >&2; exit 2 ;;
  esac
done
if [ -n "$keep" ]; then
  mkdir -p "$keep"
  [ -z "$(ls -A "$keep")" ] || { echo "k1lite: $keep is not empty" >&2; exit 2; }
  pins="$(cd "$keep" && pwd -P)"
else
  # Under the worktree (gitignored tests/.pins/): visible to the container
  # through /work with no extra mount. Named by sha, build row and start time so
  # a directory is one run of one build and never reused.
  sha="$(git rev-parse --short HEAD)"
  git diff --quiet HEAD -- 2>/dev/null || sha="$sha-dirty"
  pins="$PWD/tests/.pins/k1lite-$sha-$be-${img[1]:-latest}-$(date +%Y%m%dT%H%M%S)"
  mkdir -p "$pins"
fi
export NELLI_PIN_DIR="$pins"
suites=(w1a_exn_typeid w1b_localpragma panics w1e_floatwidth
        w1d1a_intminmod w1d1b_udivzero checksoff)
fail=0
out="$pins.out"; mkdir -p "$out"   # per-suite logs and rcs, beside the records
export K1_OUT="$out"
printf '%s\n' "${suites[@]}" | xargs -P 4 -I{} bash -c \
  'scripts/dt-bounded.sh "$@" '"$be"' tests/tsymex_0016_{}.nim '"$secs"' >"$K1_OUT/{}.log" 2>&1; echo "$? {}"' _ ${img[@]+"${img[@]}"} \
  > "$out/rcs" || true
cat "$out/rcs"
while read -r rc name; do [ "$rc" = 0 ] || fail=1; done < "$out/rcs"
scripts/dt-bounded.sh ${img[@]+"${img[@]}"} "$be" tests/tsymex_0016_k1lite.nim "$secs"
rc=$?
echo "k1lite: backend=$be pins=$pins suites_ok=$((1-fail)) join_rc=$rc"
[ "$rc" -eq 0 ] && [ "$fail" -eq 0 ]
