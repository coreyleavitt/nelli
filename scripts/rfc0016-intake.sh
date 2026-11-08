#!/usr/bin/env bash
# RFC-0016 CI-B: a red scheduled run opens or updates an `rfc-0016-intake`
# issue, one per (leg, test).
#
# Usage: scripts/rfc0016-intake.sh [--self-test] --mode dry-run|live
#            --run-url URL --sha SHA --event EVENT <findings.tsv>
#   findings.tsv   `<leg><TAB><test><TAB><reason>` per line; build it from the
#                  gates' output with scripts/rfc0016-intake.sh --extract.
#   --extract <leg> <gate.txt>   print findings.tsv lines for one leg's
#                  scripts/check-linux-allowlist.sh output on stdout.
# Env:   GH_TOKEN, GITHUB_REPOSITORY  for `gh` in live mode (permissions
#        `issues: write`). MAX_PER_LEG (default 10).
#
# DEDUP KEY. Every issue body carries `<!-- rfc0016-intake-key: <leg>:<test> -->`.
# A finding whose key is already on an OPEN `rfc-0016-intake` issue adds a
# comment (run URL, sha, reason) and opens nothing; otherwise a new issue is
# opened. More than MAX_PER_LEG findings on one leg collapse into ONE issue
# keyed `<leg>:*` (a toolchain break reds hundreds of tests, and one issue per
# test would bury the signal). The open issues are listed with ONE `gh` call.
#
# `dry-run` prints what `live` would do and never calls the issue-writing
# endpoints. The workflow files issues only when github.event_name is
# `schedule`, or on a dispatch that chose `live` (default: dry-run).
set -uo pipefail

LABEL=rfc-0016-intake
MAX_PER_LEG="${MAX_PER_LEG:-10}"

extract() { # leg gate.txt
  awk -v leg="$1" '
    /^FAIL: / { title = substr($0, 7); next }
    /^  [^ ]/ && title != "" { sub(/^  /, ""); printf "%s\t%s\t%s\n", leg, $0, title; next }
    { title = (/^linux gate:/ ? "" : title) }' "$2"
}

# plan <findings.tsv> <open-issues.json> -> lines `NEW|COMMENT<TAB>key<TAB>number<TAB>title<TAB>reason`
plan() {
  local findings="$1" open="$2"
  awk -F'\t' -v max="$MAX_PER_LEG" '
    { leg[NR] = $1; test[NR] = $2; why[NR] = $3; cnt[$1]++ }
    END {
      for (i = 1; i <= NR; i++) {
        if (cnt[leg[i]] > max) {
          k = leg[i] ":*"
          if (!(k in seen)) { seen[k] = 1; printf "%s\t%s\t%d findings on this leg (more than %d): see the run\n", k, k, cnt[leg[i]], max }
          list[k] = list[k] " " test[i]
        } else printf "%s:%s\t%s:%s\t%s\n", leg[i], test[i], leg[i], test[i], why[i]
      }
    }' "$findings" | while IFS=$'\t' read -r key title why; do
      num="$(jq -r --arg k "<!-- rfc0016-intake-key: $key -->" \
        '[.[] | select(.body | contains($k))][0].number // empty' "$open")"
      printf '%s\t%s\t%s\t%s\t%s\n' "${num:+COMMENT}${num:-NEW}" "$key" "${num:-0}" "$title" "$why"
    done
}

body_for() { # key reason
  printf '%s\n\nNightly symex run (%s, %s, sha %s): %s\n\nRun: %s\n\n<!-- rfc0016-intake-key: %s -->\n' \
    "Red on the scheduled CI-B matrix: \`$1\`." "$EVENT" "$(date -u +%F)" "${SHA:0:12}" "$2" "$RUN_URL" "$1"
}

apply() { # mode plan-file
  local mode="$1" planfile="$2" action key num title why
  while IFS=$'\t' read -r action key num title why; do
    if [ "$mode" = dry-run ]; then
      if [ "$action" = NEW ]; then echo "[dry-run] would OPEN issue '[nightly] $title' label $LABEL key $key: $why"
      else echo "[dry-run] would COMMENT on #$num (key $key): $why"; fi
      continue
    fi
    if [ "$action" = NEW ]; then
      gh issue create --title "[nightly] $title" --label "$LABEL" --body "$(body_for "$key" "$why")" || return 1
    else
      gh issue comment "$num" --body "$(body_for "$key" "$why")" || return 1
    fi
  done < "$planfile"
}

self_test() {
  local d; d="$(mktemp -d)"; local bad=0
  printf 'FAIL: red tests NOT in the allowlist (new failures)\n  tsymex_a\n  tsymex_b\nFAIL: allowlisted tests that PASSED (stale entries; delete them)\n  tsymex_c\nlinux gate: expected=3 ran=3 -> FAIL\n' > "$d/gate.txt"
  extract c-z3-4.13.4 "$d/gate.txt" > "$d/f.tsv"
  [ "$(wc -l < "$d/f.tsv")" = 3 ] || { echo "self-test FAILED: extract gave $(wc -l < "$d/f.tsv") lines"; bad=1; }
  printf '[{"number":7,"body":"x\\n<!-- rfc0016-intake-key: c-z3-4.13.4:tsymex_a -->"}]\n' > "$d/open.json"
  plan "$d/f.tsv" "$d/open.json" > "$d/plan.txt"
  grep -q '^COMMENT.*c-z3-4.13.4:tsymex_a	7' "$d/plan.txt" || { echo "self-test FAILED: dedup"; cat "$d/plan.txt"; bad=1; }
  grep -q '^NEW.*c-z3-4.13.4:tsymex_b' "$d/plan.txt" || { echo "self-test FAILED: new"; bad=1; }
  MAX_PER_LEG=2 plan "$d/f.tsv" "$d/open.json" > "$d/plan2.txt"
  [ "$(wc -l < "$d/plan2.txt")" = 1 ] && grep -q 'c-z3-4.13.4:\*' "$d/plan2.txt" || { echo "self-test FAILED: collapse"; bad=1; }
  # the dry run must not reach gh at all
  gh() { echo "self-test FAILED: dry-run called gh $*"; bad=1; }
  apply dry-run "$d/plan.txt" > "$d/out.txt"
  grep -q 'would OPEN' "$d/out.txt" || { echo "self-test FAILED: dry-run output"; bad=1; }
  rm -rf "$d"
  [ "$bad" -eq 0 ] && echo "rfc0016-intake self-test: ok"
  return "$bad"
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi
if [ "${1:-}" = "--extract" ]; then extract "$2" "$3"; exit 0; fi
MODE=; RUN_URL=; SHA=; EVENT=
while [ "$#" -gt 1 ]; do
  case "$1" in
    --mode) MODE="$2"; shift 2 ;; --run-url) RUN_URL="$2"; shift 2 ;;
    --sha) SHA="$2"; shift 2 ;; --event) EVENT="$2"; shift 2 ;;
    *) break ;;
  esac
done
findings="${1:?usage: rfc0016-intake.sh --mode dry-run|live --run-url U --sha S --event E <findings.tsv>}"
case "$MODE" in dry-run|live) ;; *) echo "rfc0016-intake.sh: --mode dry-run|live" >&2; exit 2 ;; esac
if [ ! -s "$findings" ]; then echo "rfc0016-intake: no findings, nothing to file"; exit 0; fi
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
if [ "$MODE" = live ]; then
  gh label create "$LABEL" --color D93F0B --description "RFC-0016 CI intake" >/dev/null 2>&1 || true
  gh issue list --label "$LABEL" --state open --limit 200 --json number,body > "$tmp/open.json" || exit 1
else
  # dry-run reads (never writes); without a token it plans against an empty list.
  gh issue list --label "$LABEL" --state open --limit 200 --json number,body > "$tmp/open.json" 2>/dev/null || echo '[]' > "$tmp/open.json"
fi
plan "$findings" "$tmp/open.json" > "$tmp/plan.txt"
apply "$MODE" "$tmp/plan.txt"
