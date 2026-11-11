#!/usr/bin/env bash
# RFC-0016 CI-D (W-60): the per-test wall-time ceiling, as a ratchet.
#
# Usage: scripts/check-ceiling.sh [--self-test] [--offenders FILE] <times-file>...
#   times-file  `<seconds> <backend> <file>` lines: the `.times` sidecar of
#               scripts/sweep.sh (compile plus run, per test), or the same
#               shape written by a Windows shard.
#   --offenders FILE  the leg's committed offender list,
#               tests/0016-allowlist/ceiling-offenders-<leg>.txt: one test per
#               line, `<name><ws><seconds><ws><reason>`: the wall time recorded
#               when the test was listed, then the reason; `#` starts a comment. Without it the script only
#               REPORTS (exit 0), as CI-D first did.
# Env:    CEILING_SECS         the ceiling, default 60
#         CEILING_FACTOR       the new-offender margin over the ceiling, default 2.5
#         REGRESS_FACTOR       a listed test may run this many times its recorded seconds, default 2.5
#         CEILING_TESTS_DIR    where tests/<name>.nim live, default tests
#
# Prints every test over the ceiling, slowest first, as `<seconds> <test>`
# under a total line. With --offenders it is a gate (exit 1) on:
#   1. NEW offenders: an unlisted test over NEW_ABOVE (60 * 2.5 = 150 s);
#   2. a listed name with no tests/<name>.nim (a retired test), a duplicate
#      entry, an entry with no reason, or an entry with no recorded seconds;
#   3. a REGRESSION: a listed test that ran over REGRESS_FACTOR x its recorded
#      seconds (below). Listing a test is a ceiling on it, not an exemption;
#   4. no readable times: a times file with no test line fails (a leg whose
#      artifact was empty or malformed must not pass as clean).
# It WARNS (reported, exit unchanged, and a finding for the intake issues) on:
#   - an unlisted test over the ceiling but not over NEW_ABOVE;
#   - a STALE entry: a listed test that ran under the ceiling. A stale entry
#     costs nothing; the intake findings feed a periodic re-seed of the list.
# A listed test that is absent from the times (a dispatch run narrowed by
# tests_regex, a shard that was cut) is neither stale nor an error here; the
# sweep gate (check-linux-allowlist.sh) already names tests with no result.
#
# WHY ONE-SIDED. The gate exists to stop a genuinely slow test creeping in
# unnoticed. Wall time on a hosted runner is not stable enough for a symmetric
# band: over three full nightly runs (42487154319, 42494651488, 42508458773) the
# per-test ratio between two runs of the same test had p5 0.46 to 0.67 and p95
# 1.54 to 1.87 (msvc widest), and some msvc tests moved more than 3x. Any band
# narrow enough to mean something flapped on those tails (a 40/90 s band: cpp 16
# new and 0 stale, z3 1 new and 10 stale, msvc 13 new and 43 stale on the third
# run), so the stale edge is gone and only the new-offender edge fails.
#
# THE LISTED EDGE. The new-offender edge alone left a listed test unbounded: a
# test listed at 80 s could reach 800 s and pass. REGRESS_FACTOR bounds it by
# the same requirement NEW_ABOVE answers: a run-to-run margin that stays quiet
# on the measured noise. The recorded seconds are the LARGEST of three runs, so
# the noise a listed test shows against it is already biased downward; the
# widest observed p95 ratio is 1.87 (msvc). The factor is the same 2.5 as
# CEILING_FACTOR (a third above that p95), so a listed and an unlisted test
# are held to one relative margin and the two edges never disagree about what
# a noisy runner can do.
#
# NEW_ABOVE = ceiling * factor. Each leg's list is seeded with every test over
# 60 s in ANY of the three runs. Leave-one-out check (seed from two runs, test
# the third; unlisted tests over the new-offender edge in the held-out run):
#   cpp, z3-4.13.4: 0 in all three folds at every factor;
#   msvc: 0, 0 and 1 at 2.0. The one is tsymex_0016_k8a1_template_except_as,
#   12.3 s, 10.2 s, then 125.7 s (a 10x outlier, not a ratio tail), so 2.0
#   (120 s) is not enough. 2.1 (126 s) is the smallest one-decimal factor
#   giving 0 in every fold, but it clears that one outlier by 0.3 s, which is
#   fitting a single point, not a margin. 2.5 (150 s) is 0 in every fold and
#   sits a third above the widest observed p95 ratio (1.87) and a fifth above
#   the outlier. 3.0 is the cap; past it, re-seed the lists instead.
set -uo pipefail
ceiling="${CEILING_SECS:-60}"
factor="${CEILING_FACTOR:-2.5}"
regress="${REGRESS_FACTOR:-2.5}"   # see THE LISTED EDGE above
new_above="$(awk -v c="$ceiling" -v n="$factor" 'BEGIN { print c * n }')"   # NEW_ABOVE


# times -> `<seconds> <name>` per test (the last line for a name wins)
normalize() {
  cat "$@" | tr -d '\r' | LC_ALL=C awk 'NF >= 3 { n = $3; sub(/^.*\//, "", n); sub(/\.nim$/, "", n); t[n] = $1 + 0 }
    END { for (n in t) printf "%.1f %s\n", t[n], n }'
}

report() {
  normalize "$@" | LC_ALL=C awk -v c="$ceiling" '
    { all++; if ($1 > c) { over++; print } }
    END { printf "TOTAL ceiling %ds: %d of %d tests over\n", c, over + 0, all + 0 }' > "$tmpr"
  command grep -v '^TOTAL ' "$tmpr" | LC_ALL=C sort -rn
  command grep '^TOTAL ' "$tmpr" | sed 's/^TOTAL //'
}

gate() { # gate <offenders> <times>...
  local off="$1"; shift
  local d rc=0; d="$(mktemp -d)"
  normalize "$@" > "$d/times"
  sed 's/#.*$//' "$off" | awk 'NF { print $1 }' | LC_ALL=C sort > "$d/listed.all"
  sed 's/#.*$//' "$off" | awk 'NF == 1 { print $1 }' > "$d/noreason"
  # a listed test needs its recorded seconds (field 2) and a reason (field 3 on)
  sed 's/#.*$//' "$off" | awk 'NF >= 2 && $2 !~ /^[0-9]+(\.[0-9]+)?$/ { print $1 }' > "$d/notime"
  sed 's/#.*$//' "$off" | awk 'NF == 2 && $2 ~ /^[0-9]+(\.[0-9]+)?$/ { print $1 }' >> "$d/noreason"
  sed 's/#.*$//' "$off" | awk 'NF >= 2 && $2 ~ /^[0-9]+(\.[0-9]+)?$/ { print $1, $2 }' | LC_ALL=C sort > "$d/rec"
  if [ ! -s "$d/times" ]; then echo "FAIL: no test times readable (an empty or malformed times file must not pass)"; rc=1; fi
  LC_ALL=C sort -u "$d/listed.all" > "$d/listed"
  LC_ALL=C awk -v c="$ceiling" '$1 > c { print $2 }' "$d/times" | LC_ALL=C sort > "$d/over"
  LC_ALL=C awk -v c="$new_above" '$1 > c { print $2 }' "$d/times" | LC_ALL=C sort > "$d/over.hard"
  LC_ALL=C awk -v c="$ceiling" '$1 < c { print $2 }' "$d/times" | LC_ALL=C sort > "$d/fast"
  show() { # title file  (with seconds)
    if [ -s "$2" ]; then echo "FAIL: $1"; sed 's/^/  /' "$2"; rc=1; fi
  }
  secs() { LC_ALL=C join -1 1 -2 2 "$1" <(LC_ALL=C sort -k2 "$d/times") | awk '{ print $2, $1 }'; }
  LC_ALL=C comm -23 "$d/over" "$d/listed" > "$d/unlisted"
  LC_ALL=C comm -12 "$d/unlisted" "$d/over.hard" > "$d/new"
  LC_ALL=C comm -23 "$d/unlisted" "$d/over.hard" > "$d/warn"
  secs "$d/warn" | LC_ALL=C sort -rn > "$d/warn.s"
  if [ -s "$d/warn.s" ]; then
    echo "WARN: over ${ceiling} s but not over ${new_above} s, and not in $(basename "$off") (not a failure; intake finding; list or split if it repeats)"
    sed 's/^/  /' "$d/warn.s"
  fi
  secs "$d/new" | LC_ALL=C sort -rn > "$d/new.s"
  show "NEW offenders: over ${new_above} s and not in $(basename "$off") (split the test, or list it with a reason)" "$d/new.s"
  LC_ALL=C comm -12 "$d/fast" "$d/listed" > "$d/stale"
  secs "$d/stale" | LC_ALL=C sort -rn > "$d/stale.s"
  if [ -s "$d/stale.s" ]; then
    echo "WARN: stale entries: listed, but ran under ${ceiling} s (not a failure; intake finding; delete them from $(basename "$off") at the next re-seed)"
    sed 's/^/  /' "$d/stale.s"
  fi
  : > "$d/gone"
  while read -r n; do [ -e "${CEILING_TESTS_DIR:-tests}/$n.nim" ] || echo "$n" >> "$d/gone"; done < "$d/listed"
  show "listed tests with no ${CEILING_TESTS_DIR:-tests}/<name>.nim (retired; delete the entry)" "$d/gone"
  uniq -d "$d/listed.all" > "$d/dupes"; show "duplicate entries" "$d/dupes"
  show "entries with no reason" "$d/noreason"
  show "entries with no recorded seconds (the second column is the wall time when listed)" "$d/notime"
  # REGRESSIONS: a listed test over REGRESS_FACTOR x its recorded seconds
  LC_ALL=C sort -k2 "$d/times" | LC_ALL=C join -1 1 -2 2 "$d/rec" - | LC_ALL=C awk -v f="$regress" '$3 > $2 * f { printf "%s (recorded %s s, over %s x) %s\n", $3, $2, f, $1 }' | LC_ALL=C sort -rn > "$d/regress.s"
  if [ -s "$d/regress.s" ]; then echo "FAIL: REGRESSED: listed tests over ${regress} x their recorded seconds in $(basename "$off") (find the cause; re-seed only with it)"; sed 's/^/  /' "$d/regress.s"; rc=1; fi
  echo "ceiling ratchet: listed=$(wc -l < "$d/listed" | tr -d ' ') over=$(wc -l < "$d/over" | tr -d ' ')" \
       "warn=$(wc -l < "$d/warn" | tr -d ' ') new=$(wc -l < "$d/new" | tr -d ' ') stale=$(wc -l < "$d/stale" | tr -d ' ')" \
       "(ceiling ${ceiling} s, new above ${new_above} s; stale entries warn only) -> $([ "$rc" -eq 0 ] && echo PASS || echo FAIL)"
  rm -rf "$d"
  return "$rc"
}

# run_gate [--offenders FILE] <times>...: the report, then the gate when asked
run_gate() {
  local off=""
  if [ "${1:-}" = "--offenders" ]; then off="$2"; shift 2; fi
  tmpr="$(mktemp)"; report "$@"; rm -f "$tmpr"
  [ -z "$off" ] || gate "$off" "$@"
}

self_test() {
  local d rc=0 out; d="$(mktemp -d)"
  mkdir -p "$d/tests"
  : > "$d/tests/tnew.nim"; : > "$d/tests/tstale.nim"; : > "$d/tests/tband.nim"
  : > "$d/tests/tslow.nim"; : > "$d/tests/tfast.nim"; : > "$d/tests/tedge.nim"
  printf '%s\n' '# header' 'tstale  80.0  seed' 'tband  70.0  seed' 'tslow  300.0  seed' > "$d/off"
  printf '%s\n' '10.0 c tests/tfast.nim' '160.5 c tests/tnew.nim' '35.0 c tests/tstale.nim' \
    '50.0 c tests/tband.nim' '300.2 c tests/tslow.nim' '60.0 c tests/tedge.nim' > "$d/t"
  expect() { # name want-rc pattern...
    local name="$1" want="$2"; shift 2
    local got=0; out="$(CEILING_TESTS_DIR="$d/tests" run_gate "$@" 2>&1)" || got=$?
    if [ "$got" != "$want" ]; then echo "self-test $name: rc $got, want $want"; printf '%s\n' "$out"; rc=1; fi
  }
  has() { printf '%s\n' "$out" | command grep -q -- "$1" || { echo "self-test: missing '$1'"; printf '%s\n' "$out"; rc=1; }; }
  hasnt() { ! printf '%s\n' "$out" | command grep -q -- "$1" || { echo "self-test: unexpected '$1'"; printf '%s\n' "$out"; rc=1; }; }

  # report-only (no offenders file): exits 0, lists the offenders, td at exactly 60 is not over
  expect report 0 "$d/t"
  has '^300.2 tslow$'; has '^160.5 tnew$'; hasnt ' tedge$'; has '2 of 6 tests over'
  # gate: tnew over the new-offender edge and unlisted fails; tstale listed and under 60 is a
  # STALE warning only (it is not what fails the gate); tband listed at 50 warns too; tslow is quiet
  expect gate 1 --offenders "$d/off" "$d/t"
  has 'NEW offenders'; has '160.5 tnew'; has 'WARN: stale'; has 'tstale'; hasnt 'FAIL: STALE'; hasnt '  tslow'; hasnt '  tfast'
  # only a listed-and-fast (warn) and a still-slow case: green
  printf '%s\n' 'tband  50.0  seed' 'tslow  300.0  seed' > "$d/off2"
  printf '%s\n' '50.0 c tests/tband.nim' '300.2 c tests/tslow.nim' '10.0 c tests/tfast.nim' > "$d/t2"
  expect clean 0 --offenders "$d/off2" "$d/t2"; has 'PASS'
  # a listed test missing from the times (a narrowed run) is not stale
  expect partial 0 --offenders "$d/off2" "$d/t2" 
  printf '%s\n' '50.0 c tests/tband.nim' '10.0 c tests/tfast.nim' > "$d/t3"
  expect absent 0 --offenders "$d/off2" "$d/t3"
  # the edges (ceiling 60, factor 2.5: new offender above 150; a stale entry never fails)
  : > "$d/tests/tw.nim"; : > "$d/tests/tl.nim"
  printf '%s\n' 'tl  60.0  seed' > "$d/offl"; : > "$d/offnone"
  printf '%s\n' '75.0 c tests/tw.nim' > "$d/tw75"
  expect warn75 0 --offenders "$d/offnone" "$d/tw75"; has 'WARN: over'; has '75.0 tw'; hasnt 'FAIL'; has 'PASS'
  printf '%s\n' '145.0 c tests/tw.nim' > "$d/tw145"
  expect warn145 0 --offenders "$d/offnone" "$d/tw145"; has 'WARN: over'; has '145.0 tw'; hasnt 'FAIL'
  printf '%s\n' '155.0 c tests/tw.nim' > "$d/tw155"
  expect new155 1 --offenders "$d/offnone" "$d/tw155"; has 'NEW offenders'; has '155.0 tw'
  printf '%s\n' '150.0 c tests/tw.nim' > "$d/tw150"
  expect edge150 0 --offenders "$d/offnone" "$d/tw150"; has 'WARN: over'
  printf '%s\n' '50.0 c tests/tl.nim' > "$d/tl50"
  expect listed50 0 --offenders "$d/offl" "$d/tl50"; has 'WARN: stale'; has '50.0 tl'; hasnt 'FAIL'; has 'PASS'
  printf '%s\n' '20.0 c tests/tl.nim' > "$d/tl20"
  expect listed20 0 --offenders "$d/offl" "$d/tl20"; has 'WARN: stale'; has '20.0 tl'; hasnt 'FAIL'; has 'PASS'
  printf '%s\n' '60.0 c tests/tl.nim' > "$d/tl60"
  expect listed60 0 --offenders "$d/offl" "$d/tl60"; hasnt 'WARN'
  # a listed name with no tests/<name>.nim is a retired test; a duplicate and a bare name are malformed
  printf '%s\n' 'tgone  60.0  seed' > "$d/off3"; expect retired 1 --offenders "$d/off3" "$d/t3"; has 'tgone'
  printf '%s\n' 'tband  50.0  a' 'tband  50.0  b' > "$d/off4"; expect dupe 1 --offenders "$d/off4" "$d/t3"
  printf '%s\n' 'tband' > "$d/off5"; expect noreason 1 --offenders "$d/off5" "$d/t3"
  printf '%s\n' 'tband  50.0' > "$d/off5b"; expect noreason2 1 --offenders "$d/off5b" "$d/t3"
  # a listed test with no recorded seconds (the old `<name> <reason>` shape) fails
  printf '%s\n' 'tband  seed' > "$d/off6"; expect notime 1 --offenders "$d/off6" "$d/t3"; has 'no recorded seconds'
  # REGRESSION: a listed test over 2.5 x its recorded seconds fails; at the edge it does not
  printf '%s\n' 'tslow  100.0  seed' > "$d/off7"
  printf '%s\n' '300.2 c tests/tslow.nim' > "$d/t7"
  expect regress 1 --offenders "$d/off7" "$d/t7"; has 'REGRESSED'; has '300.2 (recorded 100.0 s'
  printf '%s\n' '250.0 c tests/tslow.nim' > "$d/t7e"
  expect regressedge 0 --offenders "$d/off7" "$d/t7e"; hasnt 'REGRESSED'
  # a listed test that got faster is not a regression
  printf '%s\n' '70.0 c tests/tslow.nim' > "$d/t7f"
  expect faster 0 --offenders "$d/off7" "$d/t7f"; hasnt 'REGRESSED'
  # unreadable times: an empty times file (or one with no test lines) fails the gate
  : > "$d/empty"
  expect empty 1 --offenders "$d/off2" "$d/empty"; has 'no test times readable'
  printf '%s\n' 'garbage' > "$d/garbage"
  expect garbage 1 --offenders "$d/off2" "$d/garbage"; has 'no test times readable'
  # a Windows shard writes CRLF lines: the name must not carry the CR
  printf '%s\r\n' '50.0 vcc tests/tband.nim' '300.2 vcc tests/tslow.nim' > "$d/t4"
  expect crlf 0 --offenders "$d/off2" "$d/t4"; has 'PASS'
  rm -rf "$d"
  if [ "$rc" = 0 ]; then echo "check-ceiling self-test: ok"; else echo "check-ceiling self-test FAILED"; fi
  return "$rc"
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi
[ "$#" -ge 1 ] || { sed -n 2,13p "$0" >&2; exit 2; }
args=("$@")
[ "${args[0]}" = "--offenders" ] && { [ -r "${args[1]:-}" ] || { echo "check-ceiling.sh: cannot read the offenders file ${args[1]:-}" >&2; exit 2; }; args=("${args[@]:2}"); }
[ "${#args[@]}" -ge 1 ] || { echo "check-ceiling.sh: no times file" >&2; exit 2; }
for f in "${args[@]}"; do [ -r "$f" ] || { echo "check-ceiling.sh: cannot read $f" >&2; exit 2; }; done
run_gate "$@"
