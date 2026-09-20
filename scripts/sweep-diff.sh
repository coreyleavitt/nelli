#!/usr/bin/env bash
# Compare two scripts/sweep.sh logs and report what MOVED.
#
# Why this exists (RFC-0010 slice A0). A sweep of this suite is not green on
# a good day — some suites are slow, some are platform-sensitive, and the
# known Linux hangers are skipped by policy. So "did the sweep pass?" is the
# wrong question and answering it invites the two failure modes this RFC is
# about: reading pre-existing red as a regression, or waving a real
# regression through because the sweep was already red. The right question is
# "what changed against a recorded baseline?", which is what this answers.
#
# Usage: scripts/sweep-diff.sh [-s] <baseline.log> <current.log>
#   -s   subset run: the current log covers only some of the baseline, so
#        suppress the GONE section. A slice that touches eight files is
#        verified with `sweep.sh -f`, and without this every one of the ~450
#        untouched baseline entries reports as GONE and buries the two lines
#        that matter.
#
# Sections other than REGRESSED are capped at 10 entries; REGRESSED is never
# truncated, because that is the one a caller must read in full.
#
# Also diffs the `<log>.warnings` sidecars scripts/sweep.sh writes (R13-1
# follow-up), if both exist. Same principle as pass/fail: this suite is
# never warning-free on a good day (~8000 pre-existing UnusedImport/
# Deprecated warnings across the tree at last count), so an absolute count
# is noise and the DELTA is the signal -- exactly the reasoning that made
# pass/fail a baseline-diff problem instead of a "did it pass" one. Reported
# as three kinds: NEW WARNINGS (never capped -- a single new diagnostic,
# e.g. a `{.jitterPoints.}` instrumentation-gap warning, must not be
# buried), RESOLVED WARNINGS, and WARNING COUNT CHANGED (same diagnostic,
# different occurrence count -- e.g. a second call site starts hitting an
# already-known deprecation). Comparisons are restricted to tests present
# in BOTH logs, the same rule the pass/fail diff uses for regressed/fixed,
# which makes this automatically subset-safe with no extra -s handling:
# a test outside the comparison window can contribute neither a NEW nor a
# RESOLVED warning. Never affects exit status -- surfacing is the fix,
# escalation is a separate decision (same rule sweep.sh's summary follows).
#
# Exit: 0 if nothing regressed and nothing appeared already-failing;
#       1 if there are REGRESSED or NEW-FAILING entries;
#       2 on usage/IO error.
set -uo pipefail

subset=0
while getopts ":s" opt; do
  case "$opt" in
    s) subset=1 ;;
    *) echo "usage: sweep-diff.sh [-s] <baseline.log> <current.log>" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))

base="${1:?usage: sweep-diff.sh [-s] <baseline.log> <current.log>}"
cur="${2:?usage: sweep-diff.sh [-s] <baseline.log> <current.log>}"
[ -r "$base" ] || { echo "sweep-diff.sh: cannot read $base" >&2; exit 2; }
[ -r "$cur" ]  || { echo "sweep-diff.sh: cannot read $cur" >&2; exit 2; }

awk -v subset="$subset" '
  function classify(rc) { return (rc == "0") ? "pass" : (rc == "skip" ? "skip" : "fail") }

  # Print a section, capped so one noisy class cannot bury the rest.
  function section(title, arr, n, cap,    k, shown) {
    if (!n) return
    print "## " title " (" n ")"
    shown = 0
    for (k in arr) {
      if (cap && shown >= cap) { print "  ... and " (n - shown) " more"; break }
      print "  " k "   " arr[k]
      shown++
    }
    print ""
  }

  NR == FNR { b[$2 " " $3] = classify($1); brc[$2 " " $3] = $1; next }
  {
    key = $2 " " $3
    c = classify($1)
    seen[key] = 1
    if (!(key in b)) {
      if (c == "fail") { newfail[key] = "rc=" $1; nnewfail++ } else { added[key] = c; nadded++ }
      next
    }
    if (b[key] == "pass" && c == "fail")      { regressed[key] = brc[key] " -> " $1; nreg++ }
    else if (b[key] == "fail" && c == "pass") { fixed[key] = brc[key] " -> 0";       nfix++ }
    else if (b[key] != c)                     { moved[key] = b[key] " -> " c;        nmov++ }
    else                                      { same++ }
  }

  END {
    for (key in b) if (!(key in seen)) { gone[key] = "was " b[key]; ngone++ }

    section("REGRESSED — passed in baseline, fails now", regressed, nreg, 0)
    section("NEW, ALREADY FAILING — not in baseline", newfail, nnewfail, 10)
    section("FIXED", fixed, nfix, 10)
    section("SKIP-STATE CHANGED", moved, nmov, 10)
    section("NEW, PASSING OR SKIPPED", added, nadded, 10)
    if (!subset) section("GONE — in baseline, absent now", gone, ngone, 10)

    printf "unchanged=%d regressed=%d new-failing=%d fixed=%d skip-changed=%d new-ok=%d gone=%d\n", \
           same, nreg, nnewfail, nfix, nmov, nadded, ngone
    exit (nreg + nnewfail > 0) ? 1 : 0
  }
' "$base" "$cur"
rc=$?

# ---- warnings diff --------------------------------------------------------
base_warn="$base.warnings"
cur_warn="$cur.warnings"
if [ ! -r "$base_warn" ] || [ ! -r "$cur_warn" ]; then
  # Name the side that is actually missing. An "and/or" message sends the
  # reader to check a file that is present and fine -- and a diagnostic that
  # misdirects is worse than none, which is the whole point of R13-1.
  missing=""
  [ -r "$base_warn" ] || missing="baseline sidecar $base_warn"
  if [ ! -r "$cur_warn" ]; then
    [ -n "$missing" ] && missing="$missing and current sidecar $cur_warn" \
                      || missing="current sidecar $cur_warn"
  fi
  echo "sweep-diff.sh: warnings diff skipped -- $missing not found." >&2
  if [ -r "$cur_warn" ]; then
    echo "sweep-diff.sh:   the current run DID capture warnings; only the baseline lacks them," >&2
    echo "sweep-diff.sh:   so this run establishes no delta. Capture a baseline sidecar by running" >&2
    echo "sweep-diff.sh:   sweep.sh in the pinned baseline worktree, or adopt a known-good run as" >&2
    echo "sweep-diff.sh:   the warnings reference. Until then the warnings gate is INERT." >&2
  fi
else
  awk -v basefile="$base" -v curfile="$cur" -v basewarn="$base_warn" -v curwarn="$cur_warn" '
    function section(title, arr, n, cap,    k, shown) {
      if (!n) return
      print "## " title " (" n ")"
      shown = 0
      for (k in arr) {
        if (cap && shown >= cap) { print "  ... and " (n - shown) " more"; break }
        print "  " k "   " arr[k]
        shown++
      }
      print ""
    }
    # A sidecar line is either a bare diagnostic identity ("file: message
    # [Cat]") or one with a trailing " xN" occurrence-count suffix. Split
    # the two apart and record the count under the same (test, identity)
    # composite key so a later count-only change is distinguishable from
    # the identity appearing/disappearing.
    function recordwarn(idset, cnt, key, line,   n, id) {
      if (match(line, / x[0-9]+$/)) {
        n = substr(line, RSTART + 2, RLENGTH - 2) + 0
        id = substr(line, 1, RSTART - 1)
      } else {
        n = 1
        id = line
      }
      idset[key SUBSEP id] = 1
      cnt[key SUBSEP id] = n
    }

    FILENAME == basefile { buniv[$2 " " $3] = 1; next }
    FILENAME == curfile  { cuniv[$2 " " $3] = 1; next }

    FILENAME == basewarn {
      if ($0 ~ /^## /) { bkey = $2 " " $3; next }
      if ($0 ~ /^#/)   { next }
      if ($0 == "")    { bkey = ""; next }
      if (bkey != "")  { recordwarn(bwarn, bcnt, bkey, $0) }
      next
    }
    FILENAME == curwarn {
      if ($0 ~ /^## /) { ckey = $2 " " $3; next }
      if ($0 ~ /^#/)   { next }
      if ($0 == "")    { ckey = ""; next }
      if (ckey != "")  { recordwarn(cwarn, ccnt, ckey, $0) }
      next
    }

    END {
      for (combo in bwarn) {
        split(combo, parts, SUBSEP); key = parts[1]; id = parts[2]
        if (!(key in cuniv)) continue
        if (!(combo in cwarn))          { resolved[key "   " id] = "was x" bcnt[combo]; nres++ }
        else if (bcnt[combo] != ccnt[combo]) { changed[key "   " id] = bcnt[combo] " -> " ccnt[combo]; nchg++ }
      }
      for (combo in cwarn) {
        split(combo, parts, SUBSEP); key = parts[1]; id = parts[2]
        if (!(key in buniv)) continue
        if (!(combo in bwarn)) { added[key "   " id] = "now x" ccnt[combo]; nnew++ }
      }

      section("NEW WARNINGS — not in baseline", added, nnew, 0)
      section("RESOLVED WARNINGS — were in baseline, gone now", resolved, nres, 10)
      section("WARNING COUNT CHANGED — same diagnostic, different occurrence count", changed, nchg, 10)

      printf "new-warnings=%d resolved-warnings=%d count-changed=%d  (informational -- never affects exit status)\n", \
             nnew, nres, nchg
    }
  ' "$base" "$cur" "$base_warn" "$cur_warn"
fi

exit "$rc"
