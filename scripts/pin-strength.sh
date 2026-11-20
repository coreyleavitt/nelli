#!/usr/bin/env bash
# RFC-0016 K9e: the pin-strength measurement.
#
# For each mutant `scripts/pin-strength-mutants.py` enumerates over the
# walker's arithmetic and raise arms (`src/nelli/smt/lower_expr.nim` and the
# raise drains of `src/nelli/smt/walk_expr.nim`), build a
# scratch copy of TREE with that one mutant applied and run the committed pin
# suites (`tests/0016-pinstrength.suites`) against it with
# `scripts/dt-bounded.sh`, in order, stopping at the first that fails:
#
#   killed     a suite failed (column `by`: `pin` when its log names
#              `PinFailure`, the native disagreement a K9 verb raises;
#              `assert` when another assertion of the suite caught it)
#   survived   every suite passed: a finding (see docs/rfc-data/0016-k9e.md)
#   timeout    no suite failed, and one was killed at SUITE_TIMEOUT (rc 137):
#              not counted either way, listed for a rerun
#   stillborn  the mutant does not compile (a Nim or C compile error in
#              `src/`): not a mutant of the walker, not counted
#
# The figure is killed / (killed + survived), one decimal, as a percentage.
#
# Usage: scripts/pin-strength.sh TREE OUTDIR
#   TREE    a checkout at the sha being measured, with its `nim.cfg` and
#           `_deps` (each `_deps` link is re-made absolute in the copies, so a
#           relative milpa link works in the container too). Never edited:
#           every mutant is applied to a copy under OUTDIR/work.
#   OUTDIR  results: `results.tsv` (one row per mutant, appended as each
#           finishes, so a rerun with the same OUTDIR resumes), `mutants.tsv`
#           (the generator's list), `logs/<id>.<suite>.log` for each killing
#           or timed-out suite, and `figure.tsv` (the results with the header
#           `tests/0016-pinstrength.tsv` is a copy of).
# Env:
#   P              mutants run at once (default 4); each runs its suites one
#                  at a time, so P is the number of concurrent compiles
#   SUITE_TIMEOUT  seconds per suite run, compile included (default 600)
#   BACKEND        c (default) or cpp
#   IDS            a file of mutant ids, one per line: run only these (a
#                  sample, or a rerun of the timeouts)
#   SKIP_BASELINE  1: do not first run the suites on the unmutated copy (by
#                  default a suite that fails there aborts the run: a kill
#                  must be the mutant's)
#   KEEP           1: keep each mutant's copy (default: removed when done)
#   NELLI_IMAGE / NELLI_HOST / NELLI_MEM_MB pass through to dt-bounded.sh.
set -uo pipefail

tree="${1:?usage: pin-strength.sh TREE OUTDIR}"
out="${2:?usage: pin-strength.sh TREE OUTDIR}"
tree="$(cd "$tree" && pwd -P)" || exit 2
mkdir -p "$out/work" "$out/logs"
out="$(cd "$out" && pwd -P)"
P="${P:-4}"
SUITE_TIMEOUT="${SUITE_TIMEOUT:-600}"
BACKEND="${BACKEND:-c}"
export SUITE_TIMEOUT BACKEND

[ -f "$tree/nim.cfg" ] || { echo "pin-strength: $tree has no nim.cfg (copy it from a milpa checkout)" >&2; exit 2; }
[ -d "$tree/_deps" ] || { echo "pin-strength: $tree has no _deps" >&2; exit 2; }

mapfile -t suites < <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$tree/tests/0016-pinstrength.suites")
[ "${#suites[@]}" -gt 0 ] || { echo "pin-strength: no suites in tests/0016-pinstrength.suites" >&2; exit 2; }
printf '%s\n' "${suites[@]}" > "$out/suites.txt"

python3 "$tree/scripts/pin-strength-mutants.py" list "$tree" > "$out/mutants.tsv" || exit 2
total=$(wc -l < "$out/mutants.tsv")
sha=$(git -C "$tree" rev-parse --short=8 HEAD 2>/dev/null || echo unknown)

if [ -z "${NELLI_HOST:-}" ]; then
  bash "$tree/scripts/check-toolchain-parity.sh" --image "${NELLI_IMAGE:-latest}" >&2 || exit 2
fi

# A copy of TREE: the tracked files (the index, so a work-tree edit is
# never measured), nim.cfg, and _deps with each link made absolute.
mkcopy() {
  local dst="$1"
  /bin/rm -rf "$dst"; mkdir -p "$dst/_deps"
  git -C "$tree" ls-files -z | (cd "$tree" && tar --null -T - -cf -) | tar -xf - -C "$dst"
  /bin/cp -f "$tree/nim.cfg" "$dst/nim.cfg"
  local l
  for l in "$tree"/_deps/*; do
    ln -s "$(readlink -f "$l")" "$dst/_deps/$(basename "$l")"
  done
}

# Run the suites in DIR; print "status suite by".
runsuites() {
  local dir="$1" tag="$2" s rc log timedout=""
  for s in "${suites[@]}"; do
    log="$out/logs/$tag.$s.log"
    (cd "$dir" && bash scripts/dt-bounded.sh "$BACKEND" "tests/$s.nim" "$SUITE_TIMEOUT") > "$log" 2>&1
    rc=$?
    if [ "$rc" -eq 0 ]; then
      /bin/rm -f "$log"
      continue
    fi
    if [ "$rc" -eq 137 ]; then
      timedout="$s"
      continue
    fi
    if grep -Eq '/src/nelli/[^ ]*\.nim\([0-9]+, [0-9]+\) Error:|execution of an external compiler program' "$log"; then
      echo "stillborn $s -"
    elif grep -q 'PinFailure' "$log"; then
      echo "killed $s pin"
    else
      echo "killed $s assert"
    fi
    return
  done
  if [ -n "$timedout" ]; then echo "timeout $timedout -"; else echo "survived - -"; fi
}

one() {
  local id="$1" kind="$2" scope="$3" line="$4" dir t0 res src
  dir="$out/work/$id"
  t0=$(date +%s)
  mkcopy "$dir"
  # `apply` prints the source it edited, relative to the copy's root.
  if ! src="$(python3 "$dir/scripts/pin-strength-mutants.py" apply "$id" "$dir")" || [ -z "$src" ]; then
    printf '%s\t%s\t%s:%s\t%s\t%s\t%s\t%s\n' "$id" "$kind" "$scope" "$line" "error" "-" "-" "0" >> "$out/results.tsv"
    return
  fi
  if cmp -s "$dir/$src" "$tree/$src"; then
    res="equivalent - -"
  else
    res="$(runsuites "$dir" "$id")"
  fi
  read -r st su by <<< "$res"
  printf '%s\t%s\t%s:%s\t%s\t%s\t%s\t%s\n' "$id" "$kind" "$scope" "$line" "$st" "$su" "$by" "$(( $(date +%s) - t0 ))" >> "$out/results.tsv"
  [ "${KEEP:-}" = 1 ] || /bin/rm -rf "$dir"
}

if [ "${SKIP_BASELINE:-}" != 1 ]; then
  echo "pin-strength: baseline (${#suites[@]} suites, unmutated)" >&2
  mkcopy "$out/work/base"
  read -r st su by <<< "$(runsuites "$out/work/base" base)"
  [ "${KEEP:-}" = 1 ] || /bin/rm -rf "$out/work/base"
  if [ "$st" != survived ]; then
    echo "pin-strength: the baseline is not green ($st in $su; log $out/logs/base.$su.log)" >&2
    exit 1
  fi
fi

touch "$out/results.tsv"
todo="$out/todo.tsv"
if [ -n "${IDS:-}" ]; then
  grep -F -f "$IDS" "$out/mutants.tsv" > "$todo.all" || true
else
  /bin/cp -f "$out/mutants.tsv" "$todo.all"
fi
cut -f1 "$out/results.tsv" > "$todo.done"
grep -v -F -f "$todo.done" "$todo.all" > "$todo" 2>/dev/null || /bin/cp -f "$todo.all" "$todo"
[ -s "$todo.done" ] || /bin/cp -f "$todo.all" "$todo"
echo "pin-strength: $(wc -l < "$todo") of $total mutants to run, P=$P, ${#suites[@]} suites" >&2

while IFS=$'\t' read -r id kind scope line _; do
  while [ "$(jobs -rp | wc -l)" -ge "$P" ]; do wait -n; done
  one "$id" "$kind" "$scope" "$line" &
done < "$todo"
wait

# The figure.
k=$(awk -F'\t' '$4=="killed"' "$out/results.tsv" | wc -l)
kp=$(awk -F'\t' '$4=="killed" && $6=="pin"' "$out/results.tsv" | wc -l)
s=$(awk -F'\t' '$4=="survived"' "$out/results.tsv" | wc -l)
t=$(awk -F'\t' '$4=="timeout"' "$out/results.tsv" | wc -l)
b=$(awk -F'\t' '$4=="stillborn" || $4=="equivalent" || $4=="error"' "$out/results.tsv" | wc -l)
run=$(wc -l < "$out/results.tsv")
fig=$(awk -v k="$k" -v s="$s" 'BEGIN { if (k + s == 0) print "0.0"; else printf "%.1f", 100 * k / (k + s) }')
{
  echo "# RFC-0016 K9e pin strength (scripts/pin-strength.sh; see docs/rfc-data/0016-k9e.md)."
  echo "# sha: $sha  backend: $BACKEND  mutants: $total  run: $run  suites: ${#suites[@]}"
  echo "# killed: $k (by a pin: $kp)  survived: $s  timeout: $t  stillborn/equivalent: $b"
  echo "# figure: killed / (killed + survived) = $k / $((k + s)) = $fig"
  printf 'id\tkind\tsite\tstatus\tsuite\tby\tsecs\n'
  sort -t$'\t' -k1,1 "$out/results.tsv"
} > "$out/figure.tsv"
echo "pin-strength: killed $k (pin $kp), survived $s, timeout $t, stillborn $b; figure $fig% ($out/figure.tsv)" >&2
