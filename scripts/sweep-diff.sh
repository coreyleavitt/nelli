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
# Usage: scripts/sweep-diff.sh <baseline.log> <current.log>
#
# Exit: 0 if nothing regressed and nothing appeared already-failing;
#       1 if there are REGRESSED or NEW-FAILING entries;
#       2 on usage/IO error.
set -uo pipefail

base="${1:?usage: sweep-diff.sh <baseline.log> <current.log>}"
cur="${2:?usage: sweep-diff.sh <baseline.log> <current.log>}"
[ -r "$base" ] || { echo "sweep-diff.sh: cannot read $base" >&2; exit 2; }
[ -r "$cur" ]  || { echo "sweep-diff.sh: cannot read $cur" >&2; exit 2; }

awk '
  function classify(rc) { return (rc == "0") ? "pass" : (rc == "skip" ? "skip" : "fail") }

  NR == FNR { b[$2 " " $3] = classify($1); brc[$2 " " $3] = $1; next }
  {
    key = $2 " " $3
    c = classify($1)
    seen[key] = 1
    if (!(key in b)) {
      if (c == "fail") { newfail[key] = $1; nnewfail++ } else { added[key] = c; nadded++ }
      next
    }
    if (b[key] == "pass" && c == "fail")      { regressed[key] = brc[key] " -> " $1; nreg++ }
    else if (b[key] == "fail" && c == "pass") { fixed[key] = brc[key] " -> 0";       nfix++ }
    else if (b[key] != c)                     { moved[key] = b[key] " -> " c;        nmov++ }
    else                                      { same++ }
  }

  END {
    for (key in b) if (!(key in seen)) { gone[key] = b[key]; ngone++ }

    if (nreg) { print "## REGRESSED (" nreg ") — passed in baseline, fails now"
                for (k in regressed) print "  " k "   " regressed[k]; print "" }
    if (nnewfail) { print "## NEW, ALREADY FAILING (" nnewfail ") — not in baseline"
                for (k in newfail) print "  " k "   rc=" newfail[k]; print "" }
    if (nfix) { print "## FIXED (" nfix ")"
                for (k in fixed) print "  " k "   " fixed[k]; print "" }
    if (nmov) { print "## SKIP-STATE CHANGED (" nmov ")"
                for (k in moved) print "  " k "   " moved[k]; print "" }
    if (nadded) { print "## NEW, PASSING OR SKIPPED (" nadded ")"
                for (k in added) print "  " k "   " added[k]; print "" }
    if (ngone) { print "## GONE (" ngone ") — in baseline, absent now"
                for (k in gone) print "  " k "   was " gone[k]; print "" }

    printf "unchanged=%d regressed=%d new-failing=%d fixed=%d skip-changed=%d new-ok=%d gone=%d\n", \
           same, nreg, nnewfail, nfix, nmov, nadded, ngone
    exit (nreg + nnewfail > 0) ? 1 : 0
  }
' "$base" "$cur"
