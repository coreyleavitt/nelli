#!/usr/bin/env bash
# RFC-0016 CI-D (W-60): the 60 s per-test ceiling, as a FINDING and not a gate.
#
# Usage: scripts/check-ceiling.sh [--self-test] <times-file>...
#   times-file  `<seconds> <backend> <file>` lines: the `.times` sidecar of
#               scripts/sweep.sh (compile plus run, per test), or the same
#               shape written by a Windows shard.
# Env:    CEILING_SECS  default 60
#
# Prints every test over the ceiling, slowest first, as
#   `<seconds> <test>` under a one-line header, then a total. The row in
# F-tests-finishline.md reads "flag any file over 60 s compile+run as a `ci`
# finding rather than letting it accumulate": the offenders are reported in the
# job summary and the leg's artifact (and named in the intake issue body), but
# they do not turn the leg red, because dozens of registered tests are over
# the line today (the split of each is a work-list row, not a CI change) and a
# gate that is red from the first run carries no signal. Exit status is 0
# unless the input is unreadable.
set -uo pipefail
ceiling="${CEILING_SECS:-60}"

run() {
  local tmp; tmp="$(mktemp)"
  cat "$@" | LC_ALL=C awk -v c="$ceiling" '
    NF >= 3 { n = $3; sub(/^.*\//, "", n); sub(/\.nim$/, "", n); t[n] = $1 + 0 }
    END {
      for (n in t) { all++; if (t[n] > c) { over++; printf "%.1f %s\n", t[n], n } }
      printf "TOTAL ceiling %ds: %d of %d tests over\n", c, over + 0, all + 0
    }' > "$tmp"
  grep -v '^TOTAL ' "$tmp" | LC_ALL=C sort -rn
  grep '^TOTAL ' "$tmp" | sed 's/^TOTAL //'
  rm -f "$tmp"
}

self_test() {
  local d; d="$(mktemp -d)"
  printf '12.0 c tests/ta.nim\n61.5 c tests/tb.nim\n300.2 c tests/tc.nim\n60.0 c tests/td.nim\n' > "$d/t"
  local out; out="$(run "$d/t")"
  rm -rf "$d"
  if printf '%s\n' "$out" | grep -q '^300.2 tc$' && printf '%s\n' "$out" | grep -q '^61.5 tb$' \
     && ! printf '%s\n' "$out" | grep -q ' td$' && printf '%s\n' "$out" | grep -q '2 of 4 tests over'; then
    echo "check-ceiling self-test: ok"; return 0
  fi
  echo "check-ceiling self-test FAILED"; printf '%s\n' "$out"; return 1
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi
[ "$#" -ge 1 ] || { sed -n 2,4p "$0" >&2; exit 2; }
for f in "$@"; do [ -r "$f" ] || { echo "check-ceiling.sh: cannot read $f" >&2; exit 2; }; done
run "$@"
