#!/usr/bin/env bash
# RFC-0016 K2-s: read-only construct census. Gates nothing; K2a / K2a-fail
# later consume its counts. Pure bash/awk, no toolchain, no side effects.
#
# Five kinds are counted (one TSV row per occurrence):
#   case_n_kind  every `case n.kind` in src/nelli/**/*.nim (the walker's
#                dispatch sites; the construct axis of K2a).
#   case_kind    every `case <expr>.kind` dispatch (and `case kind(<expr>)`) in
#                src/nelli, whatever the scrutinee is called. A superset of
#                case_n_kind (the RFC's literal row, kept as is); this is the
#                row K2a means by "every node-kind dispatch".
#   survivors    every `Survivors(` literal in src/nelli. K7a introduces the
#                type, so until it lands the count is 0 (the script still
#                runs and reports it).
#   degrade      every `Degrade(` literal in src/nelli. Matched on a word
#                boundary, so `allocDegrade(` and `lowerDegrade(` do not
#                count; only the constructor does.
#   bare_skip    every `skip(` call in tests/**/*.nim. "Bare" follows the RFC
#                (section "Skips are records"): a skip that records no pin
#                record, i.e. unittest's `skip()`, which takes no reason or
#                kind. `skipCell(...)` (a different identifier) is the
#                recorded form and is not counted. Platform arms lacking a
#                skipCell are a separate K2a item and are NOT counted here.
#
# Comment text is ignored: everything from the first `#` on a line is dropped
# before matching (a `#` inside a string literal can hide a later match; the
# census is a ratchet over an allowlist, so that bias is stable, not silent
# drift). Several matches on one line yield several rows.
#
# Output (stable, sorted, diffable; paths are repo-relative):
#   census<TAB>kind<TAB>file:line<TAB>context      one per occurrence
#   summary<TAB>kind<TAB>total<TAB>-               per kind
#   summary<TAB>kind:<file><TAB>count<TAB>-        per kind and file
#
# Usage: scripts/census-k2.sh [--root DIR]    (DIR holds src/nelli and tests;
#                                              default: the repo root)
#        scripts/census-k2.sh --self-test     (census of tests/fixtures/k2census)
#        scripts/census-k2.sh --help
# Exit:  0 always on a completed census (it gates nothing); 2 = misuse.
set -uo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"

usage() { sed -n '2,/^set -uo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; }

census() {  # $1 = root; emits unsorted-then-sorted census + summary on stdout
  local root="$1"
  (
    cd "$root" || exit 2
    { [ -d src/nelli ] && find src/nelli -name '*.nim' -type f; \
      [ -d tests ] && find tests -name '*.nim' -type f; } | LC_ALL=C sort | \
    while IFS= read -r f; do
      case "$f" in
        tests/fixtures/*) [ "$root" = "$here" ] && continue ;;
      esac
      awk -v F="$f" '
        function emit(kind, line,   c) { c = line; gsub(/^[ \t]+|[ \t]+$/, "", c); gsub(/\t/, " ", c)
          printf "census\t%s\t%s:%d\t%s\n", kind, F, NR, c }
        {
          s = $0; i = index(s, "#"); if (i) s = substr(s, 1, i - 1)
          if (F ~ /^src\/nelli\//) {
            t = s; while (match(t, /(^|[^A-Za-z0-9_])case[ \t]+n\.kind([^A-Za-z0-9_]|$)/)) { emit("case_n_kind", $0); t = substr(t, RSTART + RLENGTH) }
            t = s; while (match(t, /(^|[^A-Za-z0-9_])case[ \t]+(([A-Za-z_][]A-Za-z0-9_.()[]*\.kind([^A-Za-z0-9_]|$))|kind\()/)) { emit("case_kind", $0); t = substr(t, RSTART + RLENGTH) }
            t = s; while (match(t, /(^|[^A-Za-z0-9_])Survivors\(/)) { emit("survivors", $0); t = substr(t, RSTART + RLENGTH) }
            t = s; while (match(t, /(^|[^A-Za-z0-9_])Degrade\(/)) { emit("degrade", $0); t = substr(t, RSTART + RLENGTH) }
          } else {
            t = s; while (match(t, /(^|[^A-Za-z0-9_])skip\(/)) { emit("bare_skip", $0); t = substr(t, RSTART + RLENGTH) }
          }
        }' "$f"
    done
  ) > "${2:?}"
}

report() {  # $1 = raw census file
  local raw="$1"
  LC_ALL=C sort -t$'\t' -k2,2 -k3,3V "$raw"
  awk -F'\t' '
    { tot[$2]++; split($3, p, ":"); per[$2 ":" p[1]]++ }
    END {
      n = split("case_n_kind case_kind survivors degrade bare_skip", ks, " ")
      for (i = 1; i <= n; i++) printf "summary\t%s\t%d\t-\n", ks[i], tot[ks[i]] + 0
      for (k in per) printf "summary\t%s\t%d\t-\n", k, per[k]
    }' "$raw" | LC_ALL=C sort -t$'\t' -k2,2
}

run() {
  local root="$1" raw; raw="$(mktemp)"; trap 'rm -f "$raw"' RETURN
  census "$root" "$raw" || return 2
  report "$raw"
}

case "${1:-}" in
  -h|--help) usage; exit 0 ;;
  --self-test)
    out="$(run "$here/tests/fixtures/k2census")" || { echo "self-test: census failed" >&2; exit 1; }
    for want in $'summary\tcase_n_kind\t2' $'summary\tsurvivors\t2' \
                $'summary\tcase_kind\t5' $'summary\tdegrade\t2' $'summary\tbare_skip\t2'; do
      printf '%s\n' "$out" | command grep -qF -- "$want" \
        || { echo "self-test: missing '$want'" >&2; printf '%s\n' "$out" >&2; exit 1; }
    done
    echo "census-k2: self-test ok (fixture counts n_kind 2, case_kind 5, 2/2/2; comments, allocDegrade, skipCell ignored)"
    exit 0 ;;
  --root) [ -n "${2:-}" ] && [ -d "$2" ] || { echo "--root needs a directory" >&2; exit 2; }
          run "$(cd "$2" && pwd)"; exit $? ;;
  "") run "$here"; exit $? ;;
  *) echo "usage: $0 [--root DIR | --self-test | --help]" >&2; exit 2 ;;
esac
