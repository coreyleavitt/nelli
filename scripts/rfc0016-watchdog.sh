#!/usr/bin/env bash
# RFC-0016 CI-A3 watchdog (liveness rows 24 and 55): the sinks must have a
# consumer. Fails when
#   (a) the K8a heartbeat is over MAX_AGE_DAYS (7) days old, or
#   (b) an open `rfc-0016-intake` issue is over MAX_AGE_DAYS days old with no
#       F row naming it, or
#   (c) a record-producing leg has no successful run on main within
#       MAX_AGE_DAYS days, or its workflow is disabled (RFC section 8.2: "a dead
#       leg is a failure, not an absence").
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
#   - FIRST-HEARTBEAT GRACE: between the commit that adds the workflow and its
#     first run there is necessarily no heartbeat (workflow_dispatch needs the
#     file on the default branch). For GRACE_DAYS (default 2: the next 03:17
#     cron plus a day's margin) after the workflow's first commit, a missing
#     heartbeat is a loud warning, not a failure. The age is the committer
#     date of the earliest commit touching `k8a-*.yaml` reachable from
#     GITHUB_SHA, read from the GitHub API (a shallow checkout cannot answer
#     it: every file looks added in the one commit it has). An unreadable age
#     grants no grace. A stale heartbeat, or an expired one, never gets grace.
#
# (b) THE F ROW. An issue "has an F row" when a [[row]] of
# docs/rfc-data/0016-worklist.toml that carries an F id (its `id`, a `source`
# of exactly `F-NNNN`, or an entry of `aliases`) names it as `#<number>` (or
# its full /issues/<number> URL) anywhere in the row; the `note` is the
# natural place. The handoff's markdown F table is history, not read here.
#
# (c) THE LEGS. GitHub disables scheduled workflows after 60 days without
# repository activity, and a leg that stopped running leaves no failing run to
# notice. The universe test's freshness check (freshnessProblems) judges only
# the pin directory it is handed, which is always fresh, so this is the check
# that sees a dead leg. For each entry of LEGS below it reads, on main,
#   - the workflow's `state` (anything but `active` fails), and
#   - the newest successful run (the whole run for a workflow-level leg, the
#     named job for a job-level leg, so one dead nightly leg is not hidden by
#     its siblings), failing past MAX_AGE_DAYS or when none is found among the
#     RUN_WINDOW most recent completed runs. The date logic is `leg_check`,
#     `runs_newest_success` and `jobs_newest_success`, tested offline.
set -uo pipefail
cd "$(dirname "$0")/.."

MAX_AGE_DAYS="${MAX_AGE_DAYS:-7}"
RUN_WINDOW="${RUN_WINDOW:-15}"
LEDGER="${LEDGER:-docs/rfc-data/0016-worklist.toml}"
WORKFLOWS_DIR="${WORKFLOWS_DIR:-.github/workflows}"
GRACE_DAYS="${GRACE_DAYS:-2}"
now() { echo "${NOW_EPOCH:-$(date -u +%s)}"; }
epoch() { date -u -d "$1" +%s; }
summary() { if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then echo "$*" >> "$GITHUB_STEP_SUMMARY"; fi; echo "$*"; }

# heartbeat_check <artifacts-json> [armed-since-epoch]
#   (the `gh api .../artifacts?name=...` body; the epoch of the workflow's
#   first commit, empty when unknown)
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
  local since="${2:-}"
  if [ -z "$newest" ] && [ -n "$since" ] && [ $(( $(now) - since )) -le $(( GRACE_DAYS * 86400 )) ]; then
    local hrs=$(( ( $(now) - since ) / 3600 ))
    echo "::warning title=K8a heartbeat awaiting first run::the k8a workflow landed ${hrs}h ago and has not beaten yet; this fails after ${GRACE_DAYS} days"
    summary "- K8a heartbeat: ARMED, awaiting the first run (workflow ${hrs}h old; grace ${GRACE_DAYS} days)"
    return 0
  fi
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

# f_rows <worklist.toml>: one line per [[row]] that carries an F id (its id, a
# source of exactly F-NNNN, or an alias), the row's whole text on that line.
f_rows() {
  [ -f "$1" ] || return 0
  awk '
    function flush() {
      if (blk ~ /(^|\n) *(id|source) *= *"F-[0-9][0-9][0-9][0-9]"/ ||
          blk ~ /(^|\n) *aliases *= *\[[^]]*"F-[0-9][0-9][0-9][0-9]"/) {
        gsub(/\n/, " ", blk); print blk
      }
      blk = ""
    }
    /^\[\[/ { flush(); next }
    { blk = blk "\n" $0 }
    END { flush() }' "$1"
}

# intake_check <issues-json>  (array of {number,createdAt,title}, open, label rfc-0016-intake)
intake_check() {
  local json="$1" rc=0 n created title age
  local frows; frows="$(f_rows "$LEDGER")"
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

# --- (c) the legs ----------------------------------------------------------
# label|workflow file|job name ("" = the whole run)
LEGS=(
  "symex-nightly cpp|symex-nightly.yaml|gate (cpp)"
  "symex-nightly z3-4.13.4|symex-nightly.yaml|gate (z3-4.13.4)"
  "symex-nightly msvc|symex-nightly.yaml|gate (msvc)"
  "symex-mingw|symex-mingw.yaml|"
  "symex-linux (main)|symex-linux.yaml|"
)

# runs_newest_success <runs-json>: the `.../runs?branch=main` body; prints the
# newest successful main run's updated_at, or nothing.
runs_newest_success() {
  printf '%s' "$1" | jq -r '[.workflow_runs[]? | select(.conclusion == "success" and .head_branch == "main")] | sort_by(.updated_at) | last | .updated_at // empty'
}

# jobs_newest_success <jobs-json> <job-name>: one run's `.../jobs` body; prints
# the named job's completed_at when it succeeded, or nothing.
jobs_newest_success() {
  printf '%s' "$1" | jq -r --arg n "$2" '[.jobs[]? | select(.name == $n and .conclusion == "success")] | sort_by(.completed_at) | last | .completed_at // empty'
}

# leg_check <label> <workflow-state> <newest-success-iso|"">
leg_check() {
  local label="$1" state="$2" newest="$3"
  if [ "$state" != "active" ]; then
    echo "::error title=leg disabled::$label: its workflow state is '${state:-unknown}', not active (GitHub disables scheduled workflows after 60 days of inactivity)"
    summary "- leg $label: FAIL, workflow is '${state:-unknown}'"
    return 1
  fi
  if [ -z "$newest" ]; then
    echo "::error title=leg dead::$label: no successful run on main among the last $RUN_WINDOW completed runs"
    summary "- leg $label: FAIL, no successful run on main in the last $RUN_WINDOW runs"
    return 1
  fi
  local age_days=$(( ( $(now) - $(epoch "$newest") ) / 86400 ))
  if [ "$age_days" -gt "$MAX_AGE_DAYS" ]; then
    echo "::error title=leg stale::$label: last success on main $newest is $age_days days old (limit $MAX_AGE_DAYS)"
    summary "- leg $label: FAIL, last success $age_days days old ($newest; limit $MAX_AGE_DAYS)"
    return 1
  fi
  summary "- leg $label: ok, last success $age_days days old ($newest)"
}

# legs_check: query every leg through gh and judge it.
legs_check() {
  local rc=0 spec label wf job state runs newest id jobs
  for spec in "${LEGS[@]}"; do
    IFS='|' read -r label wf job <<< "$spec"
    state="$(gh api "repos/$repo/actions/workflows/$wf" -q .state 2>/dev/null)" || state=""
    runs="$(gh api "repos/$repo/actions/workflows/$wf/runs?branch=main&status=completed&per_page=$RUN_WINDOW" 2>/dev/null)" || runs='{}'
    if [ -z "$job" ]; then
      newest="$(runs_newest_success "$runs")"
    else
      newest=""
      # newest first; only runs that finished success or failure can hold the job
      for id in $(printf '%s' "$runs" | jq -r '[.workflow_runs[]? | select(.conclusion == "success" or .conclusion == "failure")] | sort_by(.updated_at) | reverse | .[].id'); do
        jobs="$(gh api "repos/$repo/actions/runs/$id/jobs?per_page=100" 2>/dev/null)" || continue
        newest="$(jobs_newest_success "$jobs" "$job")"
        [ -n "$newest" ] && break
      done
    fi
    leg_check "$label" "$state" "$newest" || rc=1
  done
  return "$rc"
}

self_test() {
  local d bad=0; d="$(mktemp -d)"
  export NOW_EPOCH; NOW_EPOCH="$(date -u -d 2026-11-20T00:00:00Z +%s)"
  export WORKFLOWS_DIR="$d/wf"; mkdir -p "$WORKFLOWS_DIR"
  export LEDGER="$d/worklist.toml"
  cat > "$LEDGER" <<'TOML'
[[table]]
name = "5.0"
[[row]]
id = "W-01"
note = "see #99 (an unrelated row has no F id)"
[[row]]
id = "W-02"
note = "issue #12"
aliases = ["F-0001"]
[[row]]
id = "W-03"
source = "F-0002"
note = "tracked in #1234"
[[row]]
id = "F-0003"
note = "issue #7"
TOML
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
  local young old_since
  young="$(date -u -d 2026-11-19T12:00:00Z +%s)"; old_since="$(date -u -d 2026-11-10T00:00:00Z +%s)"
  t 0 "armed 12h ago, no heartbeat yet: grace" heartbeat_check "$none" "$young"
  grep -q 'awaiting the first run' "$d/out" || { echo "self-test FAILED: grace is not loud"; bad=1; }
  t 1 "armed 10 days ago, no heartbeat: grace over" heartbeat_check "$none" "$old_since"
  t 1 "armed 12h ago but the heartbeat is stale: no grace" heartbeat_check "$old" "$young"
  t 1 "armed, age unknown, no heartbeat: no grace" heartbeat_check "$none" ""
  t 1 "armed, only expired heartbeat" heartbeat_check '{"artifacts":[{"name":"k8a-heartbeat","expired":true,"created_at":"2026-11-19T03:00:00Z"}]}'
  t 0 "no intake issues" intake_check '[]'
  t 0 "old issue with an F row" intake_check '[{"number":12,"createdAt":"2026-11-01T00:00:00Z","title":"a"}]'
  t 1 "old issue without an F row" intake_check '[{"number":123,"createdAt":"2026-11-01T00:00:00Z","title":"b"}]'
  t 0 "young issue without an F row" intake_check '[{"number":9,"createdAt":"2026-11-18T00:00:00Z","title":"c"}]'
  t 1 "#123 is not matched by F-0002's #1234" intake_check '[{"number":123,"createdAt":"2026-11-01T00:00:00Z","title":"d"}]'
  t 0 "an issue named by an own F row" intake_check '[{"number":7,"createdAt":"2026-11-01T00:00:00Z","title":"e"}]'
  t 1 "a number in a row with no F id is not an F row" intake_check '[{"number":99,"createdAt":"2026-11-01T00:00:00Z","title":"f"}]'
  # (c) the legs, offline
  local runs jobs
  runs='{"workflow_runs":[{"conclusion":"success","head_branch":"main","updated_at":"2026-11-19T01:00:00Z"},{"conclusion":"success","head_branch":"feat","updated_at":"2026-11-20T00:00:00Z"},{"conclusion":"failure","head_branch":"main","updated_at":"2026-11-19T20:00:00Z"}]}'
  [ "$(runs_newest_success "$runs")" = "2026-11-19T01:00:00Z" ] || { echo "self-test FAILED: runs_newest_success"; bad=1; }
  [ -z "$(runs_newest_success '{"workflow_runs":[{"conclusion":"failure","head_branch":"main","updated_at":"2026-11-19T01:00:00Z"}]}')" ] || { echo "self-test FAILED: a failed run counted"; bad=1; }
  [ -z "$(runs_newest_success '{"total_count":0,"workflow_runs":[]}')" ] || { echo "self-test FAILED: no runs"; bad=1; }
  jobs='{"jobs":[{"name":"gate (cpp)","conclusion":"success","completed_at":"2026-11-18T04:00:00Z"},{"name":"gate (msvc)","conclusion":"failure","completed_at":"2026-11-18T05:00:00Z"}]}'
  [ "$(jobs_newest_success "$jobs" 'gate (cpp)')" = "2026-11-18T04:00:00Z" ] || { echo "self-test FAILED: jobs_newest_success"; bad=1; }
  [ -z "$(jobs_newest_success "$jobs" 'gate (msvc)')" ] || { echo "self-test FAILED: a red job counted"; bad=1; }
  [ -z "$(jobs_newest_success "$jobs" 'gate (z3-4.13.4)')" ] || { echo "self-test FAILED: an absent job counted"; bad=1; }
  t 0 "leg: active, fresh success" leg_check L active 2026-11-19T01:00:00Z
  t 0 "leg: success exactly 7 days old" leg_check L active 2026-11-13T00:00:00Z
  t 1 "leg: success 8 days old" leg_check L active 2026-11-12T00:00:00Z
  t 1 "leg: no success in the window" leg_check L active ""
  t 1 "leg: disabled workflow with a fresh success" leg_check L disabled_inactivity 2026-11-19T01:00:00Z
  t 1 "leg: unreadable workflow state" leg_check L "" 2026-11-19T01:00:00Z
  rm -rf "$d"
  [ "$bad" -eq 0 ] && echo "rfc0016-watchdog self-test: ok"
  return "$bad"
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi

rc=0
repo="${GITHUB_REPOSITORY:?GITHUB_REPOSITORY unset}"
summary "### RFC-0016 watchdog"
arts="$(gh api "repos/$repo/actions/artifacts?name=k8a-heartbeat&per_page=100")" || { echo "::error::could not list artifacts"; exit 1; }
since=""
if compgen -G "$WORKFLOWS_DIR/k8a-*.yaml" > /dev/null; then
  for f in "$WORKFLOWS_DIR"/k8a-*.yaml; do
    d="$(gh api --paginate "repos/$repo/commits?path=$f&sha=${GITHUB_SHA:-HEAD}&per_page=100" -q '.[].commit.committer.date' 2>/dev/null | tail -1)"
    [ -n "$d" ] || continue
    e="$(epoch "$d")"; { [ -z "$since" ] || [ "$e" -lt "$since" ]; } && since="$e"
  done
fi
heartbeat_check "$arts" "$since" || rc=1
issues="$(gh issue list --repo "$repo" --label rfc-0016-intake --state open --limit 200 --json number,createdAt,title)" \
  || { echo "::error::could not list rfc-0016-intake issues"; exit 1; }
intake_check "$issues" || rc=1
legs_check || rc=1
exit "$rc"
