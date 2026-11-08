#!/usr/bin/env bash
# RFC-0016 K8a-job: the driver behind .github/workflows/k8a-differential.yaml.
# The workflow is thin; everything that can be run and tested without a runner
# lives here.
#
#   k8a-nightly.sh plan [--date YYYY-MM-DD] [--row ROW] [--seed N]
#       Prints key=value lines (the workflow appends them to $GITHUB_OUTPUT):
#       date, row, backend, image, seed, z3_version, z3_asset, z3_sha256.
#       The row ROTATES: day-of-year (UTC) mod 3 over ROWS below, so each
#       Linux build row runs every third night. The seed is the date as
#       YYYYMMDD. Both are pure functions of the date; --row and --seed
#       override (workflow_dispatch inputs).
#   k8a-nightly.sh run -r ROW -s SEED -n COUNT -o OUTDIR [-t TAG|none] [-T SECS]
#       The nightly body. Writes into OUTDIR:
#         differential.log   the K8a-gen test's whole output (the disagreement
#                            report: FINDING blocks, distribution, declines)
#         findings.txt       the FINDING blocks alone (empty = no disagreement)
#         pins/              the pin records (NELLI_PIN_DIR)
#         threeway.tsv       the three-way table (below)
#         heartbeat/heartbeat.txt   the dated heartbeat (always written last)
#       Exit status: the differential test's (0 = no disagreement).
#       -t TAG   the release tag whose engine fills the release column
#                (default: the newest `v*` tag without a prerelease suffix;
#                `none` skips the column and records `skipped`).
#       -T SECS  hard-kill timeout per test run (default 3000).
#       Env: NELLI_HOST=1 runs on the host (CI); NELLI_NIM_FLAGS then carries
#       the host compile flags. Unset, it runs in podman, the z3 row on the
#       `z3-4.13.4` image.
#   k8a-nightly.sh --self-test     determinism of the rotation and the seed,
#                                  and the three-way classification.
#
# THE RELEASE COLUMN. The last tag has no K8a generator and no pin machinery.
# So the PROGRAMS come from head (the generator is pure: same seed, same
# programs) and only the ENGINE is the tag's: a `git worktree` of the tag gets
# head's `tests/s0016_k8a_gen.nim` and `tests/s0016_k8a_threeway.nim` copied in
# (the threeway runner uses only symexFind, symexCaptureBegin/End and the
# generator's pure half, which the tag also has), plus head's dt-bounded.sh /
# run-one.sh (the harness, not the engine), the generated nim.cfg and a
# dereferenced copy of _deps. The same runner then runs at the tag and at head.
# If the tag cannot compile the runner, the whole release column is
# `compile-stop`: per §2.4 that is itself a datum (a compile stop on the
# release against a false verdict on head counts as worse), not an error.
#
# THREE-WAY TABLE (threeway.tsv), the W1-z layout (handoff "Three-way rows"),
# one row per generated program, original variant only:
#   seed  row  cell_key  release  head  native  vs_release
# row = `progN Shape type`; cell_key = `construct:k8a-gen/Shape`; release and
# head = the walker's verdict (`sxSat trusted`, `sxUnknown untrusted`, ...);
# native = what the head build's native run did (the programs are the same, so
# one native column serves both); vs_release = better | same |
# worse (precision) | worse (soundness). A false trusted verdict ranks above
# a decline (and a release compile stop) ranks as a decline, which is what
# §2.4 says; "worse (soundness)" is the column that blocks a tag.
set -uo pipefail
cd "$(dirname "$0")/.."

ROWS=(linux-c linux-cpp linux-c-z3-4.13.4)
Z3_DEFAULT=(5.1.0 z3-5.1.0-x64-glibc-2.39 f47be8d27d3230e823bf1eeede2fe0abaca55bb78d0b59974370e6689a92284a)
# The release asset the z3-4.13.4 dev image installs (scripts/Containerfile.z3-4.13.4).
Z3_413=(4.13.4 z3-4.13.4-x64-glibc-2.35 93f91f9c6f4a00a041c19fc7a74adc1f441c8244ce70d486e19abcd89c6a014b)

die() { echo "k8a-nightly: $*" >&2; exit 2; }

# row_for_date YYYY-MM-DD -> row name
row_for_date() {
  local doy; doy="$(date -u -d "$1" +%j)" || return 1
  echo "${ROWS[$(( 10#$doy % ${#ROWS[@]} ))]}"
}
seed_for_date() { date -u -d "$1" +%Y%m%d; }

plan() {
  local date row="" seed=""
  date="$(date -u +%F)"
  while [ $# -gt 0 ]; do
    case "$1" in
      --date) date="$2"; shift 2 ;;
      --row)  row="$2"; shift 2 ;;
      --seed) seed="$2"; shift 2 ;;
      *) die "plan: unknown argument $1" ;;
    esac
  done
  date -u -d "$date" +%F > /dev/null 2>&1 || die "plan: bad date '$date'"
  date="$(date -u -d "$date" +%F)"
  [ -n "$row" ] || row="$(row_for_date "$date")"
  [ -n "$seed" ] || seed="$(seed_for_date "$date")"
  case " ${ROWS[*]} " in *" $row "*) ;; *) die "plan: unknown row '$row' (rows: ${ROWS[*]})" ;; esac
  case "$seed" in ''|*[!0-9]*) die "plan: seed must be a non-negative integer, got '$seed'" ;; esac
  local backend=c image=latest z3=("${Z3_DEFAULT[@]}")
  case "$row" in
    linux-cpp) backend=cpp ;;
    linux-c-z3-4.13.4) image=z3-4.13.4; z3=("${Z3_413[@]}") ;;
  esac
  echo "date=$date"
  echo "row=$row"
  echo "backend=$backend"
  echo "image=$image"
  echo "seed=$seed"
  echo "z3_version=${z3[0]}"
  echo "z3_asset=${z3[1]}"
  echo "z3_sha256=${z3[2]}"
}

# verdict_rank <walker verdict> <native>: 0 correct, 1 declined, 2 false
verdict_rank() {
  local v="$1" n="$2" hit=0 raise=0
  case "$n" in hit*) hit=1 ;; esac
  case "$n" in *raise*) raise=1 ;; esac
  case "$v" in
    compile-stop*|skipped*|*untrusted*|sxUnknown*) echo 1 ;;
    sxSat*)    [ "$hit" -eq 1 ] && echo 0 || echo 2 ;;
    sxUnsat*)  [ "$hit" -eq 1 ] && echo 2 || echo 0 ;;
    sxRaised*) [ "$raise" -eq 1 ] && echo 0 || echo 2 ;;
    *) echo 1 ;;
  esac
}

# vs_release <release rank> <head rank>
vs_release() {
  if [ "$2" -lt "$1" ]; then echo better
  elif [ "$2" -eq "$1" ]; then echo same
  elif [ "$2" -eq 2 ]; then echo "worse (soundness)"
  else echo "worse (precision)"; fi
}

# join_threeway <head.tsv> <tag.tsv or ""> <release-label>: the table on stdout.
# Input lines: K8A3W seed prog shape type walker native
join_threeway() {
  local head="$1" tag="$2" label="$3" seed prog shape ty walker native rel rrank hrank
  printf 'seed\trow\tcell_key\trelease\thead\tnative\tvs_release\n'
  while IFS=$'\t' read -r _ seed prog shape ty walker native; do
    [ -n "$prog" ] || continue
    rel="$label"
    if [ -n "$tag" ]; then
      rel="$(awk -F'\t' -v p="$prog" '$1 == "K8A3W" && $3 == p { print $6; exit }' "$tag")"
      [ -n "$rel" ] || rel="not run"
    fi
    rrank="$(verdict_rank "$rel" "$native")"
    hrank="$(verdict_rank "$walker" "$native")"
    printf '%s\tprog%s %s %s\tconstruct:k8a-gen/%s\t%s\t%s\t%s\t%s\n' \
      "$seed" "$prog" "$shape" "$ty" "$shape" "$rel" "$walker" "$native" \
      "$(vs_release "$rrank" "$hrank")"
  done < <(grep -a '^K8A3W' "$head")
}

newest_release_tag() {
  git tag -l 'v*' --sort=-v:refname | grep -v -- '-' | head -1
}

# test_run <worktree> <image-or-""> <backend> <test.nim> <log> <extra -d flags>
test_run() {
  local wt="$1" image="$2" backend="$3" test="$4" log="$5" flags="$6" rc
  local -a ia=()
  [ -n "$image" ] && [ "$image" != latest ] && [ -z "${NELLI_HOST:-}" ] && ia=(-i "$image")
  ( cd "$wt" && NELLI_NIM_FLAGS="${NELLI_NIM_FLAGS:-} $flags" \
      scripts/dt-bounded.sh ${ia[@]+"${ia[@]}"} "$backend" "$test" "$TIMEOUT" ) > "$log" 2>&1
  rc=$?
  return "$rc"
}

run() {
  local row="" seed="" count="" out="" tag="" TIMEOUT=3000 opt
  OPTIND=1
  while getopts ":r:s:n:o:t:T:" opt; do
    case "$opt" in
      r) row="$OPTARG" ;; s) seed="$OPTARG" ;; n) count="$OPTARG" ;;
      o) out="$OPTARG" ;; t) tag="$OPTARG" ;; T) TIMEOUT="$OPTARG" ;;
      *) die "run: bad option -$OPTARG" ;;
    esac
  done
  [ -n "$row" ] && [ -n "$seed" ] && [ -n "$count" ] && [ -n "$out" ] \
    || die "usage: run -r ROW -s SEED -n COUNT -o OUTDIR [-t TAG|none] [-T SECS]"
  local backend image
  eval "$(plan --row "$row" --seed "$seed" | grep -E '^(backend|image)=')"
  mkdir -p "$out/pins" "$out/heartbeat"
  out="$(cd "$out" && pwd -P)"
  [ -n "$tag" ] || tag="$(newest_release_tag)"
  [ -n "$tag" ] || tag=none
  echo "k8a-nightly: row=$row backend=$backend image=$image seed=$seed count=$count tag=$tag"
  local flags="-d:k8aSeed=$seed -d:k8aCount=$count"

  # 1. head: the differential (orig and twins vs native).
  local drc=0
  NELLI_PIN_DIR="$out/pins" test_run . "$image" "$backend" tests/tsymex_0016_k8a_gen.nim \
    "$out/differential.log" "$flags" || drc=$?
  awk '/^FINDING /{p=1} p && /^[[:space:]]*\[(OK|FAILED|SKIPPED)\]|^\[(Suite|Summary)\]|^k8a-gen /{p=0} p' \
    "$out/differential.log" > "$out/findings.txt"
  echo "k8a-nightly: differential rc=$drc, findings: $(grep -c '^FINDING ' "$out/findings.txt")"

  # 2. head: the three-way runner (head verdict + native).
  test_run . "$image" "$backend" tests/s0016_k8a_threeway.nim "$out/threeway-head.log" "$flags" \
    || echo "k8a-nightly: head threeway runner rc=$?"
  grep -a '^K8A3W' "$out/threeway-head.log" > "$out/head.tsv" || true

  # 3. the release engine, same programs.
  local label="" tagtsv=""
  if [ "$tag" = none ]; then
    label=skipped
  else
    local wt="$out/tagwt"
    git worktree remove --force "$wt" > /dev/null 2>&1 || true
    if git worktree add --detach "$wt" "$tag" > /dev/null 2>&1; then
      mkdir -p "$wt/scripts" "$wt/tests"
      cp tests/s0016_k8a_gen.nim tests/s0016_k8a_threeway.nim "$wt/tests/"
      cp scripts/dt-bounded.sh scripts/run-one.sh "$wt/scripts/"
      [ -f nim.cfg ] && cp nim.cfg "$wt/nim.cfg"
      rm -rf "$wt/_deps"; mkdir -p "$wt/_deps"
      for dep in _deps/*; do   # each entry is a link into the milpa cache; copy its target
        [ -e "$dep" ] && { mkdir -p "$wt/$dep"; cp -a "$dep/." "$wt/$dep/" 2>/dev/null; }
      done
      test_run "$wt" "$image" "$backend" tests/s0016_k8a_threeway.nim "$out/threeway-tag.log" "$flags" \
        || echo "k8a-nightly: tag threeway runner rc=$?"
      grep -a '^K8A3W' "$out/threeway-tag.log" > "$out/tag.tsv" || true
      if [ -s "$out/tag.tsv" ]; then tagtsv="$out/tag.tsv"; else label=compile-stop; fi
      git worktree remove --force "$wt" > /dev/null 2>&1 || rm -rf "$wt"
    else
      label="not run (no checkout of $tag)"
    fi
  fi
  join_threeway "$out/head.tsv" "$tagtsv" "$label" > "$out/threeway.tsv"
  echo "k8a-nightly: three-way table:"; cat "$out/threeway.tsv"

  # 4. the heartbeat, last: it says the job got this far, whatever it found.
  {
    echo "k8a-heartbeat $(date -u +%Y-%m-%dT%H:%M:%SZ) row=$row backend=$backend seed=$seed count=$count tag=$tag differential_rc=$drc"
  } > "$out/heartbeat/heartbeat.txt"
  cat "$out/heartbeat/heartbeat.txt"
  return "$drc"
}

self_test() {
  local bad=0 got
  eq() { [ "$2" = "$3" ] || { echo "self-test FAILED: $1: want '$3' got '$2'"; bad=1; }; }
  # rotation: day-of-year mod 3, deterministic, and every row gets a night in any 3-day run
  eq "2026-01-01 (doy 1)" "$(row_for_date 2026-01-01)" linux-cpp
  eq "2026-01-03 (doy 3)" "$(row_for_date 2026-01-03)" linux-c
  eq "2026-11-08 (doy 312)" "$(row_for_date 2026-11-08)" linux-c
  eq "2026-11-09 (doy 313)" "$(row_for_date 2026-11-09)" linux-cpp
  eq "2026-11-10 (doy 314)" "$(row_for_date 2026-11-10)" linux-c-z3-4.13.4
  eq "same date twice" "$(row_for_date 2026-11-08)" "$(row_for_date 2026-11-08)"
  got="$(for d in 2026-12-01 2026-12-02 2026-12-03; do row_for_date $d; done | sort -u | wc -l)"
  eq "three consecutive nights cover three rows" "$got" 3
  # seed
  eq "seed from date" "$(seed_for_date 2026-11-08)" 20261108
  eq "plan seed" "$(plan --date 2026-11-08 | sed -n 's/^seed=//p')" 20261108
  eq "plan is stable" "$(plan --date 2026-11-08)" "$(plan --date 2026-11-08)"
  # overrides and per-row provisioning
  eq "row override" "$(plan --date 2026-11-08 --row linux-cpp | sed -n 's/^row=//p')" linux-cpp
  eq "cpp backend" "$(plan --row linux-cpp | sed -n 's/^backend=//p')" cpp
  eq "seed override" "$(plan --seed 77 | sed -n 's/^seed=//p')" 77
  eq "z3 row version" "$(plan --row linux-c-z3-4.13.4 | sed -n 's/^z3_version=//p')" 4.13.4
  eq "z3 row image" "$(plan --row linux-c-z3-4.13.4 | sed -n 's/^image=//p')" z3-4.13.4
  eq "default z3" "$(plan --row linux-c | sed -n 's/^z3_version=//p')" 5.1.0
  ( plan --row windows-msvc > /dev/null 2>&1 ) && { echo "self-test FAILED: a non-Linux row was accepted"; bad=1; }
  ( plan --seed 1x > /dev/null 2>&1 ) && { echo "self-test FAILED: a bad seed was accepted"; bad=1; }
  # classification
  eq "sat+hit" "$(verdict_rank 'sxSat trusted' 'hit (0,0)')" 0
  eq "sat+nohit is false" "$(verdict_rank 'sxSat trusted' nohit)" 2
  eq "unsat+hit is false" "$(verdict_rank 'sxUnsat trusted' 'hit (1,1)')" 2
  eq "unknown declines" "$(verdict_rank 'sxUnknown untrusted' nohit)" 1
  eq "compile-stop declines" "$(verdict_rank compile-stop nohit)" 1
  eq "worse soundness" "$(vs_release 0 2)" "worse (soundness)"
  eq "worse precision" "$(vs_release 0 1)" "worse (precision)"
  eq "false to decline is better" "$(vs_release 2 1)" better
  eq "same" "$(vs_release 1 1)" same
  # the join, end to end on fixtures
  local d; d="$(mktemp -d)"
  printf 'K8A3W\t7\t0\tDivLit\tint\tsxSat trusted\thit (0,0)\nK8A3W\t7\t1\tNeg\tint8\tsxUnknown untrusted\tnohit\n' > "$d/h"
  printf 'K8A3W\t7\t0\tDivLit\tint\tsxUnsat trusted\thit (0,0)\n' > "$d/t"
  got="$(join_threeway "$d/h" "$d/t" '' | tail -n +2 | cut -f2,4,5,7 | tr '\n' '|')"
  eq "join with a tag" "$got" 'prog0 DivLit int	sxUnsat trusted	sxSat trusted	better|prog1 Neg int8	not run	sxUnknown untrusted	same|'
  got="$(join_threeway "$d/h" "" compile-stop | tail -n +2 | cut -f4,7 | tr '\n' '|')"
  eq "join, release compile-stop" "$got" 'compile-stop	better|compile-stop	same|'
  rm -rf "$d"
  [ "$bad" -eq 0 ] && echo "k8a-nightly self-test: ok"
  return "$bad"
}

case "${1:-}" in
  plan) shift; plan "$@" ;;
  run) shift; run "$@" ;;
  --self-test) self_test ;;
  *) die "usage: k8a-nightly.sh plan|run|--self-test (see the header)" ;;
esac
