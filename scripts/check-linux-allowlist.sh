#!/usr/bin/env bash
# RFC-0016 CI-A3: the symex-linux gate. Joins the shards' sweep logs against
# the committed known-red allowlist and the expected run set.
#
# Usage: scripts/check-linux-allowlist.sh [--self-test] <allowlist> <expected-names> <sweep.log>...
#   allowlist       tests/0016-allowlist/linux-host-known-red.txt: one test per
#                   line, `<name><whitespace><reason>`; `#` lines are comments.
#   expected-names  one test basename per line: the run set the shards were cut from.
#   sweep.log       the <rc> <backend> <file> <warn> logs of scripts/sweep.sh.
#
# Fails (exit 1) on:
#   1. a test in the expected set with no log line (a shard died or was cut);
#      a test with two lines; a line for a test outside the set;
#   2. a red test that is not in the allowlist (a new failure);
#   3. an allowlisted test that PASSED (a stale entry: the list cannot rot);
#   4. an allowlist entry with no reason, a duplicate, or a name outside the
#      expected set (a typo or a retired test would otherwise pass unseen).
# A shard job runs the same check over its own slice (expected-names = that
# shard's tests) with PARTIAL=1, so a red test fails the shard that ran it and
# the shard summary lists the known-red tests it absorbed; the `gate` job still
# owns the whole-suite checks (missing shards, typos, duplicates).
# PARTIAL=1 (a dispatch with a test filter) skips check 4's run-set test.
# A `skip` line counts as run-and-not-red. Prints each class by name.
set -uo pipefail

check() {
  local allow="$1" expect="$2"; shift 2
  local tmp; tmp="$(mktemp -d)"
  local rc=0
  cat "$@" | awk 'NF >= 3 { n = $3; sub(/^.*\//, "", n); sub(/\.nim$/, "", n); print $1, n }' \
    | LC_ALL=C sort -k2 > "$tmp/lines"
  awk '{print $2}' "$tmp/lines" | LC_ALL=C sort > "$tmp/ran"
  LC_ALL=C sort -u "$expect" > "$tmp/expect"
  awk '$1 != "0" && $1 != "skip" {print $2}' "$tmp/lines" | LC_ALL=C sort -u > "$tmp/red"
  awk '$1 == "0" {print $2}' "$tmp/lines" | LC_ALL=C sort -u > "$tmp/green"
  sed 's/#.*$//' "$allow" | awk 'NF {print $1}' | LC_ALL=C sort > "$tmp/allow.all"
  LC_ALL=C sort -u "$tmp/allow.all" > "$tmp/allow"
  sed 's/#.*$//' "$allow" | awk 'NF == 1 {print $1}' > "$tmp/noreason"

  report() { # title file
    if [ -s "$2" ]; then echo "FAIL: $1"; sed 's/^/  /' "$2"; rc=1; fi
  }
  LC_ALL=C comm -23 "$tmp/expect" "$tmp/ran" > "$tmp/missing"
  report "expected tests with no result line (shard died or was cut)" "$tmp/missing"
  LC_ALL=C comm -13 "$tmp/expect" "$tmp/ran" | uniq > "$tmp/extra"
  report "result lines for tests outside the run set" "$tmp/extra"
  uniq -d "$tmp/ran" > "$tmp/dupes"
  report "tests with more than one result line" "$tmp/dupes"
  LC_ALL=C comm -23 "$tmp/red" "$tmp/allow" > "$tmp/new"
  report "red tests NOT in the allowlist (new failures)" "$tmp/new"
  # Declared known-red tests that are red: expected, not a failure, but named
  # so a shard's step summary shows what the allowlist is absorbing.
  LC_ALL=C comm -12 "$tmp/red" "$tmp/allow" > "$tmp/known"
  if [ -s "$tmp/known" ]; then echo "known-red (allowlisted, still red; not failing):"; sed 's/^/  /' "$tmp/known"; fi
  LC_ALL=C comm -12 "$tmp/green" "$tmp/allow" > "$tmp/stale"
  report "allowlisted tests that PASSED (stale entries; delete them)" "$tmp/stale"
  uniq -d "$tmp/allow.all" > "$tmp/adupes"
  report "duplicate allowlist entries" "$tmp/adupes"
  report "allowlist entries with no reason" "$tmp/noreason"
  LC_ALL=C comm -23 "$tmp/allow" "$tmp/expect" > "$tmp/unknown"
  # A narrowed (dispatch) run legitimately omits most allowlisted tests.
  [ -n "${PARTIAL:-}" ] || report "allowlist entries outside the run set (typo or retired test)" "$tmp/unknown"

  echo "linux gate: expected=$(wc -l < "$tmp/expect" | tr -d ' ') ran=$(wc -l < "$tmp/ran" | tr -d ' ')" \
       "red=$(wc -l < "$tmp/red" | tr -d ' ') allowlisted=$(wc -l < "$tmp/allow" | tr -d ' ')" \
       "-> $([ "$rc" -eq 0 ] && echo PASS || echo FAIL)"
  rm -rf "$tmp"
  return "$rc"
}

self_test() {
  local d; d="$(mktemp -d)"; local bad=0
  local PARTIAL=
  printf 'ta\ntb\ntc\ntd\n' > "$d/expect"
  printf 'tb  known host defect\n' > "$d/allow"
  expect_rc() { # want label allow log...
    local want="$1" label="$2" allow="$3"; shift 3
    check "$allow" "$d/expect" "$@" > "$d/out" 2>&1; local got=$?
    if [ "$got" -ne "$want" ]; then echo "self-test FAILED: $label (want $want got $got)"; cat "$d/out"; bad=1; fi
  }
  printf '0 c tests/ta.nim 0\n1 c tests/tb.nim 0\n0 c tests/tc.nim 0\nskip c tests/td.nim 0\n' > "$d/ok.log"
  expect_rc 0 "baseline green" "$d/allow" "$d/ok.log"
  printf '0 c tests/ta.nim 0\n0 c tests/tb.nim 0\n0 c tests/tc.nim 0\n0 c tests/td.nim 0\n' > "$d/stale.log"
  expect_rc 1 "stale allowlist entry" "$d/allow" "$d/stale.log"
  printf '1 c tests/ta.nim 0\n1 c tests/tb.nim 0\n0 c tests/tc.nim 0\n0 c tests/td.nim 0\n' > "$d/new.log"
  expect_rc 1 "new red" "$d/allow" "$d/new.log"
  printf '0 c tests/ta.nim 0\n1 c tests/tb.nim 0\n0 c tests/tc.nim 0\n' > "$d/miss.log"
  expect_rc 1 "missing test" "$d/allow" "$d/miss.log"
  printf 'tb\n' > "$d/noreason"
  expect_rc 1 "entry without reason" "$d/noreason" "$d/ok.log"
  printf 'tzz  gone\ntb  x\n' > "$d/typo"
  expect_rc 1 "entry outside run set" "$d/typo" "$d/ok.log"
  printf '0 c tests/ta.nim 0\n1 c tests/tb.nim 0\n' > "$d/s1.log"
  printf '0 c tests/tc.nim 0\n0 c tests/td.nim 0\n' > "$d/s2.log"
  expect_rc 0 "two shard logs" "$d/allow" "$d/s1.log" "$d/s2.log"
  # Shard mode: one slice, PARTIAL=1 (allowlist entries of other shards are not typos).
  printf 'ta\ntb\n' > "$d/expect"
  printf 'tb  known host defect\ntz  lives in another shard\n' > "$d/allow2"
  printf '0 c tests/ta.nim 0\n1 c tests/tb.nim 0\n' > "$d/sh_ok.log"
  PARTIAL=1 check "$d/allow2" "$d/expect" "$d/sh_ok.log" > "$d/out" 2>&1; got=$?
  if [ "$got" -ne 0 ] || ! command grep -q 'known-red.*not failing' "$d/out" || ! command grep -qx '  tb' "$d/out"; then
    echo "self-test FAILED: shard known-red passes but is reported (rc=$got)"; cat "$d/out"; bad=1; fi
  printf '1 c tests/ta.nim 0\n1 c tests/tb.nim 0\n' > "$d/sh_new.log"
  PARTIAL=1 check "$d/allow2" "$d/expect" "$d/sh_new.log" > "$d/out" 2>&1; got=$?
  if [ "$got" -ne 1 ] || ! command grep -qx '  ta' "$d/out"; then echo "self-test FAILED: shard unlisted red must fail (rc=$got)"; cat "$d/out"; bad=1; fi
  printf '0 c tests/ta.nim 0\n0 c tests/tb.nim 0\n' > "$d/sh_stale.log"
  PARTIAL=1 check "$d/allow2" "$d/expect" "$d/sh_stale.log" > "$d/out" 2>&1; got=$?
  if [ "$got" -ne 1 ] || ! command grep -q 'PASSED' "$d/out"; then echo "self-test FAILED: shard stale entry must fail (rc=$got)"; cat "$d/out"; bad=1; fi
  rm -rf "$d"
  [ "$bad" -eq 0 ] && echo "check-linux-allowlist self-test: ok"
  return "$bad"
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi
[ "$#" -ge 3 ] || { sed -n 2,3p "$0" >&2; echo "usage: $0 [--self-test] <allowlist> <expected-names> <sweep.log>..." >&2; exit 2; }
check "$@"
