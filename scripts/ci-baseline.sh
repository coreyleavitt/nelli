#!/usr/bin/env bash
# RFC-0016 CI-C: fetch the sweep baseline a nightly leg is diffed against.
#
# Usage: scripts/ci-baseline.sh <leg> <outdir>
# Env:   GH_TOKEN, GITHUB_REPOSITORY (permissions: actions: read, contents: read)
#        DEFAULT_BRANCH   the branch whose runs are baselines (default main)
# Prints one word on stdout, the baseline KIND:
#   nightly   the newest unexpired `nightly-<leg>-merged` artifact produced by
#             a run on DEFAULT_BRANCH (a scheduled run, or a dispatch on main).
#             A REGRESSED test against it turns the leg red: "what moved"
#             since the last recorded night is the verdict, not the pass rate.
#   release   no main artifact yet: the 0.9.1 baseline release asset of the
#             matching row (tests/0016-baselines.txt). Informational only: it
#             was recorded under podman from the tests/t*.nim glob, so its
#             pass/fail differs from a host run for reasons the allowlist
#             already carries.
#   none      neither exists (the symex-msvc leg before its first main run);
#             this run's artifact becomes the baseline.
# Files land in <outdir>/baseline.log and its .warnings/.env/.summary/.drift.
# Two `gh api` calls and one `gh run`-free download at most.
set -uo pipefail
leg="${1:?usage: ci-baseline.sh <leg> <outdir>}"; out="${2:?}"
repo="${GITHUB_REPOSITORY:?}"; branch="${DEFAULT_BRANCH:-main}"
mkdir -p "$out"

id="$(gh api "repos/$repo/actions/artifacts?name=nightly-$leg-merged&per_page=30" \
  --jq "[.artifacts[] | select(.expired == false and .workflow_run.head_branch == \"$branch\")][0].id // empty" 2>/dev/null)"
if [ -n "$id" ]; then
  tmpz="$(mktemp -d)"
  if gh api "repos/$repo/actions/artifacts/$id/zip" > "$tmpz/a.zip" 2>/dev/null \
     && python3 -I -c 'import sys,zipfile; zipfile.ZipFile(sys.argv[1]).extractall(sys.argv[2])' "$tmpz/a.zip" "$tmpz/x"; then
    for f in "$tmpz"/x/merged.log*; do [ -e "$f" ] && cp "$f" "$out/baseline.log${f##*merged.log}"; done
    rm -rf "$tmpz"
    if [ -s "$out/baseline.log" ]; then echo nightly; exit 0; fi
  fi
  rm -rf "$tmpz"
fi

case "$leg" in cpp) row=cpp ;; z3-4.13.4) row=z3-4.13.4 ;; *) row= ;; esac
if [ -n "$row" ]; then
  d="$(mktemp -d)"
  if gh release download v0.9.1 -p "sweep-0.9.1-$row.log*" -D "$d" >/dev/null 2>&1 && [ -s "$d/sweep-0.9.1-$row.log" ]; then
    for f in "$d"/sweep-0.9.1-"$row".log*; do cp "$f" "$out/baseline.log${f##*"sweep-0.9.1-$row.log"}"; done
    rm -rf "$d"; echo release; exit 0
  fi
  rm -rf "$d"
fi
echo none
