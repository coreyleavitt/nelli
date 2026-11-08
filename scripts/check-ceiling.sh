#!/usr/bin/env bash
# RFC-0016 CI-D (W-60): the per-test wall-time ceiling, as a ratchet.
#
# Usage: scripts/check-ceiling.sh [--self-test] [--offenders FILE] <times-file>...
#   times-file  `<seconds> <backend> <file>` lines: the `.times` sidecar of
#               scripts/sweep.sh (compile plus run, per test), or the same
#               shape written by a Windows shard.
#   --offenders FILE  the leg's committed offender list,
#               tests/0016-allowlist/ceiling-offenders-<leg>.txt: one test per
#               line, `<name><whitespace><reason>`, `#` starts a comment (the
#               shape of the other allowlists). Without it the script only
#               REPORTS (exit 0), as CI-D first did.
# Env:    CEILING_SECS         the ceiling, default 60
#         CEILING_STALE_BELOW  stale-entry line, default 45 (the hysteresis band)
#         CEILING_TESTS_DIR    where tests/<name>.nim live, default tests
#
# Prints every test over the ceiling, slowest first, as `<seconds> <test>`
# under a total line. With --offenders it is a gate (exit 1) on:
#   1. NEW offenders: a test over the ceiling that is not listed. The list only
#      shrinks, so a test cannot slow past the line unseen;
#   2. STALE entries: a listed test that ran UNDER the stale line. The entry is
#      deleted in the commit that made the test fast;
#   3. a listed name with no tests/<name>.nim (a retired test), a duplicate
#      entry, or an entry with no reason.
# A listed test that is absent from the times (a dispatch run narrowed by
# tests_regex, a shard that was cut) is neither stale nor an error here; the
# sweep gate (check-linux-allowlist.sh) already names tests with no result.
#
# THE BAND. Wall time on a hosted runner moves by tens of percent between two
# runs of the same test (cold caches, a congested pool, cpp against c). One
# cutoff for both directions would make a test near 60 s flip between "new
# offender" and "stale" from night to night. So the list is entered above the
# ceiling (60 s) but left only below the stale line (45 s): a listed test that
# measures 45 to 60 s is in the band and passes quietly. A test over 60 that
# is unlisted still fails at once: that direction has no band, because the
# ratchet's job is to refuse a new slow test. A test that sits at 55 s and
# spikes to 61 s on a slow night is a new offender; list it (with the
# reason) or split it.
set -uo pipefail
ceiling="${CEILING_SECS:-60}"
stale_below="${CEILING_STALE_BELOW:-45}"


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
  LC_ALL=C sort -u "$d/listed.all" > "$d/listed"
  LC_ALL=C awk -v c="$ceiling" '$1 > c { print $2 }' "$d/times" | LC_ALL=C sort > "$d/over"
  LC_ALL=C awk -v s="$stale_below" '$1 < s { print $2 }' "$d/times" | LC_ALL=C sort > "$d/fast"
  show() { # title file  (with seconds)
    if [ -s "$2" ]; then echo "FAIL: $1"; sed 's/^/  /' "$2"; rc=1; fi
  }
  secs() { LC_ALL=C join -1 1 -2 2 "$1" <(LC_ALL=C sort -k2 "$d/times") | awk '{ print $2, $1 }'; }
  LC_ALL=C comm -23 "$d/over" "$d/listed" > "$d/new"
  secs "$d/new" | LC_ALL=C sort -rn > "$d/new.s"
  show "NEW offenders: over ${ceiling} s and not in $(basename "$off") (split the test, or list it with a reason)" "$d/new.s"
  LC_ALL=C comm -12 "$d/fast" "$d/listed" > "$d/stale"
  secs "$d/stale" | LC_ALL=C sort -rn > "$d/stale.s"
  show "STALE entries: listed, but ran under ${stale_below} s (delete them from $(basename "$off"))" "$d/stale.s"
  : > "$d/gone"
  while read -r n; do [ -e "${CEILING_TESTS_DIR:-tests}/$n.nim" ] || echo "$n" >> "$d/gone"; done < "$d/listed"
  show "listed tests with no ${CEILING_TESTS_DIR:-tests}/<name>.nim (retired; delete the entry)" "$d/gone"
  uniq -d "$d/listed.all" > "$d/dupes"; show "duplicate entries" "$d/dupes"
  show "entries with no reason" "$d/noreason"
  echo "ceiling ratchet: listed=$(wc -l < "$d/listed" | tr -d ' ') over=$(wc -l < "$d/over" | tr -d ' ')" \
       "new=$(wc -l < "$d/new" | tr -d ' ') stale=$(wc -l < "$d/stale" | tr -d ' ')" \
       "(ceiling ${ceiling} s, stale below ${stale_below} s) -> $([ "$rc" -eq 0 ] && echo PASS || echo FAIL)"
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
  printf '%s\n' '# header' 'tstale  seed 80.0' 'tband  seed 70.0' 'tslow  seed 90.0' > "$d/off"
  printf '%s\n' '10.0 c tests/tfast.nim' '61.5 c tests/tnew.nim' '44.9 c tests/tstale.nim' \
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
  has '^300.2 tslow$'; has '^61.5 tnew$'; hasnt ' tedge$'; has '2 of 6 tests over'
  # gate: tnew over and unlisted = new offender; tstale listed and under 45 = stale;
  # tband listed at 50 = in the band, quiet; tslow listed and still slow = quiet
  expect gate 1 --offenders "$d/off" "$d/t"
  has 'NEW offenders'; has '61.5 tnew'; has 'STALE'; has 'tstale'; hasnt '  tband'; hasnt '  tslow'; hasnt '  tfast'
  # only the in-band and still-slow cases: green
  printf '%s\n' 'tband  seed' 'tslow  seed' > "$d/off2"
  printf '%s\n' '50.0 c tests/tband.nim' '300.2 c tests/tslow.nim' '10.0 c tests/tfast.nim' > "$d/t2"
  expect clean 0 --offenders "$d/off2" "$d/t2"; has 'PASS'
  # a listed test missing from the times (a narrowed run) is not stale
  expect partial 0 --offenders "$d/off2" "$d/t2" 
  printf '%s\n' '50.0 c tests/tband.nim' '10.0 c tests/tfast.nim' > "$d/t3"
  expect absent 0 --offenders "$d/off2" "$d/t3"
  # a listed name with no tests/<name>.nim is a retired test; a duplicate and a bare name are malformed
  printf '%s\n' 'tgone  seed' > "$d/off3"; expect retired 1 --offenders "$d/off3" "$d/t3"; has 'tgone'
  printf '%s\n' 'tband  a' 'tband  b' > "$d/off4"; expect dupe 1 --offenders "$d/off4" "$d/t3"
  printf '%s\n' 'tband' > "$d/off5"; expect noreason 1 --offenders "$d/off5" "$d/t3"
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
