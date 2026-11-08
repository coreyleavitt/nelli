#!/usr/bin/env bash
# RFC-0016 K1a-ci: the post-shard universe join of one CI leg.
#
# Every leg's shards write pin records (NELLI_PIN_DIR, one JSON-lines file per
# test process) and upload them. This job downloads all of them, merges them
# into ONE directory and runs tests/tsymex_0016_universe.nim over it, scoped
# to the leg's build row (NELLI_UNIVERSE_ROW): the leg must evidence its own
# row and the cells the committed allowlists do not excuse, and it is not
# answerable for the other legs' rows.
#
# It FAILS, naming the leg, when
#   - the directory holds no non-empty record file (ZERO records is a failure,
#     never a pass: a leg whose sweep stopped writing records must not go green);
#   - the universe join reports an unclassified cell, a stale allowlist entry,
#     an empty record directory or a row whose newest record is over 7 days old.
#
# Usage: scripts/universe-join.sh [--partial] <leg> <row> <records-dir>
#        scripts/universe-join.sh --self-test
#   --partial  the run was narrowed (a tests_regex dispatch): the records are a
#              slice, so unclassified cells are not reported; stale allowlist
#              entries, the zero-record rule and freshness still are.
#   <row>      the leg's BuildRow: linux-c, linux-cpp, linux-c-z3-4.13.4,
#              mingw or msvc.
# Env: NELLI_HOST=1 (CI) runs the compile on the host; NELLI_NIM_FLAGS as for
#      scripts/dt-bounded.sh. UNIVERSE_JOIN_COLLECT_ONLY=1 stops after the
#      merge (the self-test).
set -uo pipefail
cd "$(dirname "$0")/.."

# collect <records-dir> <merged-dir>: copies every non-empty *.jsonl under the
# first into the second (numbered, so two shards' same-named files never
# collide) and prints the count.
collect() {
  local src="$1" dst="$2" n=0 f
  rm -rf "$dst"; mkdir -p "$dst"
  if [ -d "$src" ]; then
    while IFS= read -r -d '' f; do
      n=$((n + 1))
      cp "$f" "$dst/$(printf '%05d' "$n")-$(basename "$f")"
    done < <(find "$src" -name '*.jsonl' -size +0 -type f -print0 | sort -z)
  fi
  echo "$n"
}

if [ "${1:-}" = --self-test ]; then
  t="$(mktemp -d)"; trap 'rm -rf "$t"' EXIT
  bad=0
  expect() { # expect <0|nz> <needle> <desc> -- cmd...
    local want="$1" needle="$2" desc="$3" out rc; shift 4
    out="$("$@" 2>&1)"; rc=$?
    if { [ "$want" = 0 ] && [ $rc -ne 0 ]; } || { [ "$want" = nz ] && [ $rc -eq 0 ]; } \
       || ! printf '%s' "$out" | command grep -q -- "$needle"; then
      echo "universe-join self-test FAILED: $desc (rc=$rc, wanted $want / '$needle')"
      echo "$out" | sed 's/^/    /'; bad=1
    else
      echo "ok: $desc"
    fi
  }
  mkdir -p "$t/none"
  expect nz "ZERO pin records" "RED: an empty record directory fails" -- \
    scripts/universe-join.sh L linux-c "$t/none"
  expect nz "ZERO pin records" "RED: a missing record directory fails" -- \
    scripts/universe-join.sh L linux-c "$t/absent"
  mkdir -p "$t/zero/shard-0.log.pins"; : > "$t/zero/shard-0.log.pins/a.jsonl"
  expect nz "ZERO pin records" "RED: only zero-byte record files fail" -- \
    scripts/universe-join.sh L linux-c "$t/zero"
  mkdir -p "$t/two/s0/p" "$t/two/s1/p"
  echo '{}' > "$t/two/s0/p/a.jsonl"; echo '{}' > "$t/two/s1/p/a.jsonl"
  expect 0 "merged 2 record file" "GREEN: same-named files of two shards both merge" -- \
    env UNIVERSE_JOIN_COLLECT_ONLY=1 scripts/universe-join.sh L linux-c "$t/two"
  exit $bad
fi

partial=0
if [ "${1:-}" = --partial ]; then partial=1; shift; fi
leg="${1:?usage: universe-join.sh [--partial] <leg> <row> <records-dir>}"
row="${2:?usage: universe-join.sh [--partial] <leg> <row> <records-dir>}"
dir="${3:?usage: universe-join.sh [--partial] <leg> <row> <records-dir>}"

work="${UNIVERSE_JOIN_WORK:-$(mktemp -d)}"
merged="$work/merged"
n=$(collect "$dir" "$merged")
annotate() { [ -z "${GITHUB_ACTIONS:-}" ] || echo "::error title=universe join ($leg)::$1"; }
if [ "$n" -eq 0 ]; then
  echo "universe-join: LEG $leg (row $row) FAILED: ZERO pin records under $dir; a leg that writes no records cannot be joined, and an empty set is not a pass"
  annotate "ZERO pin records under $dir"
  exit 1
fi
echo "universe-join: leg $leg (row $row): merged $n record file(s) from $dir$([ $partial = 1 ] && echo ', PARTIAL run')"
[ -z "${UNIVERSE_JOIN_COLLECT_ONLY:-}" ] || exit 0

out="$work/join.out"
NELLI_PIN_DIR="$merged" NELLI_UNIVERSE_ROW="$row" \
  NELLI_UNIVERSE_PARTIAL="$([ $partial = 1 ] && echo 1)" \
  scripts/dt-bounded.sh c tests/tsymex_0016_universe.nim "${UNIVERSE_JOIN_TIMEOUT:-900}" > "$out" 2>&1
rc=$?
command grep -E 'universe:|unclassified cell|stale allowlist|empty record directory|days old|records\)' "$out" | head -80
if [ "$rc" -ne 0 ]; then
  echo "--- the failing part of the universe test ---"
  command grep -n -B2 -A12 -E '\[FAILED\]|Error:' "$out" | head -120
  echo "universe-join: LEG $leg (row $row) FAILED: the universe join exited $rc over $n record file(s) (messages above name the cell or record)"
  annotate "join exited $rc over $n record file(s); see the log"
  exit 1
fi
echo "universe-join: leg $leg (row $row) OK over $n record file(s)"
