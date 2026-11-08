#!/usr/bin/env bash
# RFC-0016 CI-A3 watchdog (liveness rows 24 and 55): the sinks must have a
# consumer. Fails when
#   (a) the K8a heartbeat is over MAX_AGE_DAYS (7) days old, or
#   (b) an open `rfc-0016-intake` issue is over MAX_AGE_DAYS days old with no
#       F row naming it.
#
# Usage: scripts/rfc0016-watchdog.sh [--self-test]
# Env:   GH_TOKEN / GITHUB_REPOSITORY   for `gh` (the workflow's GITHUB_TOKEN,
#        permissions `issues: read` and `actions: read`)
#        MAX_AGE_DAYS                   default 7
#        NOW_EPOCH                      override the clock (self-test)
#
# (a) THE HEARTBEAT. K8a-job (the nightly Linux fuzz job, §10) "writes a dated
# heartbeat into the artifact". The contract this watchdog reads: a workflow
# file `.github/workflows/k8a-*.yaml` uploads an artifact named
# `k8a-heartbeat` on every nightly run; the artifact's `created_at` is the
# heartbeat's date (it is the server's clock, so a job cannot forge it, and it
# needs no download). Artifacts expire (retention-days must be at least 14,
# or the watchdog cannot tell "stale" from "expired": both fail, which is the
# point, but only a longer retention yields the age in the message).
#
# ABSENT-HEARTBEAT POLICY, chosen deliberately: the check is ARMED by the
# existence of a `.github/workflows/k8a-*.yaml` file in the checked-out tree.
#   - No such workflow (K8a-job not landed): there is nothing that could have
#     beaten, so the heartbeat check is reported as NOT ARMED, loudly (a
#     warning annotation and a step-summary line naming the arming rule), and
#     does not fail. It cannot fail every run before K8a exists.
#   - The workflow exists: a missing `k8a-heartbeat` artifact, or one older
#     than MAX_AGE_DAYS, FAILS. It cannot silently never check: landing K8a-job
#     arms the check with no further edit, and K8a-job's own slice is not done
#     until this step is green after its first nightly.
#
# (b) THE F ROW. An issue "has an F row" when a row of the handoff's F ledger
# (docs/rfc/0016-native-parity-hardening.handoff.md, rows starting `| F-`)
# names it as `#<number>` (or its full /issues/<number> URL). Put the issue
# in the row's `source` cell. The F ledger had no issue reference before this
# check; `#N` in a row is the convention it adds.
set -uo pipefail
cd "$(dirname "$0")/.."

MAX_AGE_DAYS="${MAX_AGE_DAYS:-7}"
LEDGER="${LEDGER:-docs/rfc/0016-native-parity-hardening.handoff.md}"
WORKFLOWS_DIR="${WORKFLOWS_DIR:-.github/workflows}"
now() { echo "${NOW_EPOCH:-$(date -u +%s)}"; }
epoch() { date -u -d "$1" +%s; }
summary() { if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then echo "$*" >> "$GITHUB_STEP_SUMMARY"; fi; echo "$*"; }

# heartbeat_check <artifacts-json>  (the `gh api .../artifacts?name=...` body)
heartbeat_check() {
  local json="$1" armed=0
  compgen -G "$WORKFLOWS_DIR/k8a-*.yaml" > /dev/null && armed=1
  if [ "$armed" -eq 0 ]; then
    echo "::warning title=K8a heartbeat NOT ARMED::no $WORKFLOWS_DIR/k8a-*.yaml yet (K8a-job has not landed); the heartbeat check arms itself when that workflow exists"
    summary "- K8a heartbeat: NOT ARMED (no \`k8a-*.yaml\` workflow; arms when K8a-job lands)"
    return 0
  fi
  local newest
  newest="$(printf '%s' "$json" | jq -r '[.artifacts[] | select(.name == "k8a-heartbeat" and (.expired | not))] | sort_by(.created_at) | last | .created_at // empty')"
  if [ -z "$newest" ]; then
    echo "::error title=K8a heartbeat missing::a k8a-*.yaml workflow exists but no unexpired k8a-heartbeat artifact does"
    summary "- K8a heartbeat: FAIL, no unexpired \`k8a-heartbeat\` artifact"
    return 1
  fi
  local age_days=$(( ( $(now) - $(epoch "$newest") ) / 86400 ))
  if [ "$age_days" -gt "$MAX_AGE_DAYS" ]; then
    echo "::error title=K8a heartbeat stale::last heartbeat $newest is $age_days days old (limit $MAX_AGE_DAYS)"
    summary "- K8a heartbeat: FAIL, $age_days days old ($newest; limit $MAX_AGE_DAYS)"
    return 1
  fi
  summary "- K8a heartbeat: ok, $age_days days old ($newest)"
}

# intake_check <issues-json>  (array of {number,createdAt,title}, open, label rfc-0016-intake)
intake_check() {
  local json="$1" rc=0 n created title age
  local frows; frows="$(command grep -E '^\| *F-[0-9]+' "$LEDGER" 2>/dev/null || true)"
  local count=0
  while IFS=$'\t' read -r n created title; do
    [ -n "$n" ] || continue
    count=$((count + 1))
    age=$(( ( $(now) - $(epoch "$created") ) / 86400 ))
    if printf '%s\n' "$frows" | command grep -Eq "(#|/issues/)$n([^0-9]|\$)"; then continue; fi
    if [ "$age" -gt "$MAX_AGE_DAYS" ]; then
      echo "::error title=intake issue without an F row::#$n is $age days old with no F row in the handoff ledger: $title"
      summary "- intake #$n: FAIL, $age days old, no F row ($title)"
      rc=1
    else
      summary "- intake #$n: ok, $age days old, F row due by day $MAX_AGE_DAYS ($title)"
    fi
  done < <(printf '%s' "$json" | jq -r '.[] | [.number, .createdAt, .title] | @tsv')
  summary "- intake issues open: $count"
  return "$rc"
}

self_test() {
  local d bad=0; d="$(mktemp -d)"
  export NOW_EPOCH; NOW_EPOCH="$(date -u -d 2026-11-20T00:00:00Z +%s)"
  export WORKFLOWS_DIR="$d/wf"; mkdir -p "$WORKFLOWS_DIR"
  export LEDGER="$d/ledger.md"
  printf '| F-0001 | 2026-11-06 | soundness | x | issue #12 | shape | V | W1-a | closed |\n| F-0002 | d | c | v | s #1234 | | | | |\n' > "$LEDGER"
  t() { local want="$1" label="$2"; shift 2; "$@" > "$d/out" 2>&1; local got=$?
        [ "$got" -eq "$want" ] || { echo "self-test FAILED: $label (want $want got $got)"; cat "$d/out"; bad=1; }; }
  local fresh='{"artifacts":[{"name":"k8a-heartbeat","expired":false,"created_at":"2026-11-19T03:00:00Z"}]}'
  local old='{"artifacts":[{"name":"k8a-heartbeat","expired":false,"created_at":"2026-11-01T03:00:00Z"}]}'
  local none='{"artifacts":[]}'
  t 0 "unarmed, no workflow, no artifact" heartbeat_check "$none"
  grep -q 'NOT ARMED' "$d/out" || { echo "self-test FAILED: unarmed is not loud"; bad=1; }
  : > "$WORKFLOWS_DIR/k8a-nightly.yaml"
  t 0 "armed, fresh heartbeat" heartbeat_check "$fresh"
  t 1 "armed, stale heartbeat" heartbeat_check "$old"
  t 1 "armed, no heartbeat" heartbeat_check "$none"
  t 1 "armed, only expired heartbeat" heartbeat_check '{"artifacts":[{"name":"k8a-heartbeat","expired":true,"created_at":"2026-11-19T03:00:00Z"}]}'
  t 0 "no intake issues" intake_check '[]'
  t 0 "old issue with an F row" intake_check '[{"number":12,"createdAt":"2026-11-01T00:00:00Z","title":"a"}]'
  t 1 "old issue without an F row" intake_check '[{"number":123,"createdAt":"2026-11-01T00:00:00Z","title":"b"}]'
  t 0 "young issue without an F row" intake_check '[{"number":9,"createdAt":"2026-11-18T00:00:00Z","title":"c"}]'
  t 1 "#123 is not matched by F-0002's #1234" intake_check '[{"number":123,"createdAt":"2026-11-01T00:00:00Z","title":"d"}]'
  rm -rf "$d"
  [ "$bad" -eq 0 ] && echo "rfc0016-watchdog self-test: ok"
  return "$bad"
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi

rc=0
repo="${GITHUB_REPOSITORY:?GITHUB_REPOSITORY unset}"
summary "### RFC-0016 watchdog"
arts="$(gh api "repos/$repo/actions/artifacts?name=k8a-heartbeat&per_page=100")" || { echo "::error::could not list artifacts"; exit 1; }
heartbeat_check "$arts" || rc=1
issues="$(gh issue list --repo "$repo" --label rfc-0016-intake --state open --limit 200 --json number,createdAt,title)" \
  || { echo "::error::could not list rfc-0016-intake issues"; exit 1; }
intake_check "$issues" || rc=1
exit "$rc"
