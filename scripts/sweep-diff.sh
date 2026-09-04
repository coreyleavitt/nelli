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
