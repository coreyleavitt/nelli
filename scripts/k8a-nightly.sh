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
#                      [-b BATCH] [-m MB|0]
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
#       -b BATCH programs per build (default 25, env K8A_BATCH); see BATCHING.
#       -m MB    memory guard per build+run (default 12288, env K8A_MEM_MB;
#                0 = off): NELLI_MEM_MB for scripts/dt-bounded.sh.
#       Env: NELLI_HOST=1 runs on the host (CI); NELLI_NIM_FLAGS then carries
#       the host compile flags. Unset, it runs in podman, the z3 row on the
#       `z3-4.13.4` image.
#   k8a-nightly.sh --self-test     determinism of the rotation and the seed,
#                                  and the three-way classification.
#
# BATCHING. A test build holds EVERY program of its run in the compiler at
# once (the generator is a compile-time const and symexFind walks each program
# and twin during the compile). Measured in the dev image: compile peak RSS
# 3.5 GB at 6 programs, 7.7 GB at 25, 12.6 GB at 50, a slope of about 0.2 GB per
# program over a 2.7 GB base, so 250 programs need about 50 GB against the
# 16 GB of a hosted runner (the first two attempts of run 42493251144 died 3 min
# 23 s in, the runner agent killed by the kernel). The RUN is cheap (about
# 100 MB, seconds). So `run` splits COUNT into batches of BATCH programs
# (plan_batches: [0, COUNT) covered exactly once), each a separate bounded
# build and run with -d:k8aFirst=F -d:k8aCount=N (programs [F, F+N) of the
# seed's stream, ids absolute, so seed + program id still reproduce a finding),
# and merges the per-batch logs, findings and three-way rows into the one
# layout above. A batch whose build or run dies (the memory guard, the
# timeout, a crash) fails the driver with exit 3 and the batch named; it never
# reaches the heartbeat. scripts/k8a-batch-equiv.sh checks that batches
# reproduce a single run's verdicts.
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
# Batching (see "BATCHING" in the header). 25 programs peak at about 7.7 GB in
# the compile; the guard is 12 GB, inside a 16 GB hosted runner with room for
# the agent and the OS.
DEFAULT_BATCH=25
DEFAULT_MEM_MB=12288
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

# plan_batches COUNT SIZE: "first n" lines that cover [0, COUNT) exactly once.
plan_batches() {
  local count="$1" size="$2" first=0 n
  case "$count" in ''|*[!0-9]*) return 1 ;; esac
  case "$size" in ''|*[!0-9]*|0) return 1 ;; esac
  [ "$count" -gt 0 ] || return 1
  while [ "$first" -lt "$count" ]; do
    n=$(( count - first )); [ "$n" -le "$size" ] || n="$size"
    echo "$first $n"
    first=$(( first + n ))
  done
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
  ( cd "$wt" && NELLI_MEM_MB="${MEM_MB:-}" NELLI_NIM_FLAGS="${NELLI_NIM_FLAGS:-} $flags" \
      scripts/dt-bounded.sh ${ia[@]+"${ia[@]}"} "$backend" "$test" "$TIMEOUT" ) > "$log" 2>&1
  rc=$?
  return "$rc"
}

run() {
  local row="" seed="" count="" out="" tag="" TIMEOUT=3000 opt
  local BATCH="${K8A_BATCH:-$DEFAULT_BATCH}" MEM_MB="${K8A_MEM_MB-$DEFAULT_MEM_MB}"
  OPTIND=1
  while getopts ":r:s:n:o:t:T:b:m:" opt; do
    case "$opt" in
      r) row="$OPTARG" ;; s) seed="$OPTARG" ;; n) count="$OPTARG" ;;
      o) out="$OPTARG" ;; t) tag="$OPTARG" ;; T) TIMEOUT="$OPTARG" ;;
      b) BATCH="$OPTARG" ;; m) MEM_MB="$OPTARG" ;;
      *) die "run: bad option -$OPTARG" ;;
    esac
  done
  [ -n "$row" ] && [ -n "$seed" ] && [ -n "$count" ] && [ -n "$out" ] \
    || die "usage: run -r ROW -s SEED -n COUNT -o OUTDIR [-t TAG|none] [-T SECS] [-b BATCH] [-m MB|0]"
  [ "$MEM_MB" != 0 ] || MEM_MB=""
  local backend image
  eval "$(plan --row "$row" --seed "$seed" | grep -E '^(backend|image)=')"
  mkdir -p "$out/pins" "$out/heartbeat"
  out="$(cd "$out" && pwd -P)"
  [ -n "$tag" ] || tag="$(newest_release_tag)"
  [ -n "$tag" ] || tag=none
  echo "k8a-nightly: row=$row backend=$backend image=$image seed=$seed count=$count tag=$tag"
  local plan_batches_out nb
  plan_batches_out="$(plan_batches "$count" "$BATCH")" || die "run: bad count '$count' or batch size '$BATCH'"
  nb="$(echo "$plan_batches_out" | wc -l)"
  echo "k8a-nightly: $nb batch(es) of at most $BATCH, memory guard ${MEM_MB:-off} MB per build+run"
  : > "$out/differential.log"; : > "$out/findings.txt"; : > "$out/head.tsv"; : > "$out/tag.tsv"
  : > "$out/threeway-head.log"; : > "$out/threeway-tag.log"

  # The release engine, same programs: one checkout for every batch.
  local tagwt=""
  if [ "$tag" != none ]; then
    tagwt="$out/tagwt"
    git worktree remove --force "$tagwt" > /dev/null 2>&1 || true
    if git worktree add --detach "$tagwt" "$tag" > /dev/null 2>&1; then
      mkdir -p "$tagwt/scripts" "$tagwt/tests"
      cp tests/s0016_k8a_gen.nim tests/s0016_k8a_threeway.nim "$tagwt/tests/"
      cp scripts/dt-bounded.sh scripts/run-one.sh "$tagwt/scripts/"
      [ -f nim.cfg ] && cp nim.cfg "$tagwt/nim.cfg"
      rm -rf "$tagwt/_deps"; mkdir -p "$tagwt/_deps"
      for dep in _deps/*; do   # each entry is a link into the milpa cache; copy its target
        [ -e "$dep" ] && { mkdir -p "$tagwt/$dep"; cp -a "$dep/." "$tagwt/$dep/" 2>/dev/null; }
      done
    else
      tagwt=""
    fi
  fi

  # 1-3, once per batch. A batch is programs [first, first + n) of the seed's
  # stream (ids stay absolute), built and run on its own under the memory
  # guard: one compile holds every program at once, so a single 250-program
  # build outgrew the runner (see the header).
  local drc=0 failed="" bi=0 first n flags blog
  mkdir -p "$out/batches"
  while read -r first n; do
    bi=$(( bi + 1 ))
    flags="-d:k8aSeed=$seed -d:k8aFirst=$first -d:k8aCount=$n"
    blog="$out/batches/b$first"
    local brc=0
    echo "k8a-nightly: batch $bi/$nb programs [$first, $(( first + n )))"
    echo "=== batch $bi/$nb programs [$first, $(( first + n ))) ===" >> "$out/differential.log"

    # 1. head: the differential (orig and twins vs native).
    NELLI_PIN_DIR="$out/pins" test_run . "$image" "$backend" tests/tsymex_0016_k8a_gen.nim \
      "$blog.diff.log" "$flags" || brc=$?
    cat "$blog.diff.log" >> "$out/differential.log"
    awk '/^FINDING /{p=1} p && /^[[:space:]]*\[(OK|FAILED|SKIPPED)\]|^\[(Suite|Summary)\]|^k8a-gen /{p=0} p' \
      "$blog.diff.log" >> "$out/findings.txt"
    # rc != 0 with the smoke's summary line is a disagreement (the job
    # working); rc != 0 without it is a build or run that died.
    if [ "$brc" -ne 0 ] && ! grep -aq '^k8a-gen seed=' "$blog.diff.log"; then
      failed="batch $bi/$nb programs [$first, $(( first + n ))) differential rc=$brc"
      break
    fi
    [ "$brc" -eq 0 ] || drc=$brc
    echo "k8a-nightly: batch $bi differential rc=$brc"

    # 2. head: the three-way runner (head verdict + native).
    local hrc=0 rows
    test_run . "$image" "$backend" tests/s0016_k8a_threeway.nim "$blog.head.log" "$flags" || hrc=$?
    cat "$blog.head.log" >> "$out/threeway-head.log"
    grep -a '^K8A3W' "$blog.head.log" >> "$out/head.tsv" || true
    rows="$(grep -ac '^K8A3W' "$blog.head.log")"
    if [ "$rows" -ne "$n" ]; then
      failed="batch $bi/$nb programs [$first, $(( first + n ))) head three-way runner rc=$hrc ($rows of $n rows)"
      break
    fi

    # 3. the release engine on the same programs.
    if [ -n "$tagwt" ]; then
      test_run "$tagwt" "$image" "$backend" tests/s0016_k8a_threeway.nim "$blog.tag.log" "$flags" \
        || echo "k8a-nightly: batch $bi tag threeway runner rc=$?"
      cat "$blog.tag.log" >> "$out/threeway-tag.log"
      grep -a '^K8A3W' "$blog.tag.log" >> "$out/tag.tsv" || true
    fi
    rm -f "$blog".*.log
  done <<< "$plan_batches_out"
  [ -z "$tagwt" ] || { git worktree remove --force "$tagwt" > /dev/null 2>&1 || rm -rf "$tagwt"; }
  [ -n "$failed" ] || echo "k8a-nightly: differential rc=$drc, findings: $(grep -c '^FINDING ' "$out/findings.txt")"

  local label="" tagtsv=""
  if [ "$tag" = none ]; then label=skipped
  elif [ -z "$tagwt" ]; then label="not run (no checkout of $tag)"
  elif [ -s "$out/tag.tsv" ]; then tagtsv="$out/tag.tsv"
  else label=compile-stop; fi
  join_threeway "$out/head.tsv" "$tagtsv" "$label" > "$out/threeway.tsv"
  echo "k8a-nightly: three-way table:"; cat "$out/threeway.tsv"

  if [ -n "$failed" ]; then
    # Loud, named, and no heartbeat: the job did not get to its end.
    echo "k8a-nightly: BATCH FAILED: $failed (memory guard ${MEM_MB:-off} MB, timeout ${TIMEOUT}s per run); log tail:" >&2
    local lf
    for lf in "$blog".*.log; do
      echo "--- $lf ($(wc -l < "$lf") lines; an empty log with a small guard means the build was refused memory)" >&2
      tail -25 "$lf" >&2
    done
    return 3
  fi

  # 4. the heartbeat, last: it says the job got this far, whatever it found.
  {
    echo "k8a-heartbeat $(date -u +%Y-%m-%dT%H:%M:%SZ) row=$row backend=$backend seed=$seed count=$count batches=$nb batch=$BATCH tag=$tag differential_rc=$drc"
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
  # batch planning: [0, COUNT) covered exactly once, in order, whatever the size
  eq "250 by 25" "$(plan_batches 250 25 | tr '\n' ',')" "0 25,25 25,50 25,75 25,100 25,125 25,150 25,175 25,200 25,225 25,"
  eq "ragged tail" "$(plan_batches 7 3 | tr '\n' ',')" "0 3,3 3,6 1,"
  eq "one batch" "$(plan_batches 6 25 | tr '\n' ',')" "0 6,"
  local cs
  for cs in "250 25" "250 24" "250 1" "1 25" "97 10" "25 25" "26 25"; do
    got="$(plan_batches ${cs% *} ${cs#* } | awk -v total="${cs% *}" '{ for (i = 0; i < $2; i++) c[$1 + i]++; n += $2 }
      END { ok = (n == total); for (i = 0; i < total; i++) if (c[i] != 1) ok = 0; print ok }')"
    eq "plan_batches $cs covers every index once" "$got" 1
  done
  ( plan_batches 0 25 > /dev/null 2>&1 ) && { echo "self-test FAILED: count 0 accepted"; bad=1; }
  ( plan_batches 10 0 > /dev/null 2>&1 ) && { echo "self-test FAILED: batch size 0 accepted"; bad=1; }
  ( plan_batches 1x 5 > /dev/null 2>&1 ) && { echo "self-test FAILED: a bad count was accepted"; bad=1; }

  # the driver, end to end, with the test runs faked: each fake run prints what
  # the real one would for programs [first, first+count) of the stream.
  test_run() {
    local test="$4" log="$5" flags="$6" f n i
    f="$(echo "$flags" | sed -n 's/.*k8aFirst=\([0-9]*\).*/\1/p')"
    n="$(echo "$flags" | sed -n 's/.*k8aCount=\([0-9]*\).*/\1/p')"
    case "$test" in
      *tsymex_0016_k8a_gen.nim)
        if [ -n "${FAKE_DIE:-}" ] && [ "$FAKE_DIE" -ge "$f" ] && [ "$FAKE_DIE" -lt $(( f + n )) ]; then
          echo "Error: out of memory" > "$log"; return 137
        fi
        { echo "[Suite] K8a-gen"
          if [ -n "${FAKE_FINDING:-}" ] && [ "$FAKE_FINDING" -ge "$f" ] && [ "$FAKE_FINDING" -lt $(( f + n )) ]; then
            echo "FINDING seed=7 prog=$FAKE_FINDING variant=orig shape=DivLit"
            echo "native differential: boom"
          fi
          echo "  [FAILED] smoke"
          echo "k8a-gen seed=7 first=$f programs=$n runs=1 exact=1"; } > "$log"
        [ -n "${FAKE_FINDING:-}" ] && [ "$FAKE_FINDING" -ge "$f" ] && [ "$FAKE_FINDING" -lt $(( f + n )) ] && return 1
        return 0 ;;
      *) for (( i = f; i < f + n; i++ )); do
           printf 'K8A3W\t7\t%s\tDivLit\tint\tsxSat trusted\thit (0,0)\n' "$i"
         done > "$log"; return 0 ;;
    esac
  }
  local od rc
  od="$(mktemp -d)"
  ( run -r linux-c -s 7 -n 7 -o "$od/ok" -t none -b 3 -m 0 > "$od/ok.log" 2>&1 ); rc=$?
  eq "driver: clean run rc" "$rc" 0
  eq "driver: three batches announced" "$(grep -c '^=== batch' "$od/ok/differential.log")" 3
  eq "driver: merged table has every program once, absolute ids" \
    "$(tail -n +2 "$od/ok/threeway.tsv" | cut -f2 | sed 's/ .*//' | tr '\n' ',')" "prog0,prog1,prog2,prog3,prog4,prog5,prog6,"
  eq "driver: heartbeat names the batches" "$(grep -c 'batches=3 batch=3' "$od/ok/heartbeat/heartbeat.txt")" 1
  ( FAKE_FINDING=4 run -r linux-c -s 7 -n 7 -o "$od/fd" -t none -b 3 -m 0 > "$od/fd.log" 2>&1 ); rc=$?
  eq "driver: a finding is the differential's rc" "$rc" 1
  eq "driver: the finding keeps its absolute index" "$(grep -c '^FINDING seed=7 prog=4 ' "$od/fd/findings.txt")" 1
  eq "driver: only that finding" "$(grep -c '^FINDING ' "$od/fd/findings.txt")" 1
  eq "driver: the later batch still ran" "$(tail -n +2 "$od/fd/threeway.tsv" | wc -l)" 7
  ( FAKE_DIE=4 run -r linux-c -s 7 -n 7 -o "$od/die" -t none -b 3 -m 0 > "$od/die.log" 2>&1 ); rc=$?
  eq "driver: a dead batch fails the driver" "$rc" 3
  eq "driver: the dead batch is named" "$(grep -c 'BATCH FAILED: batch 2/3 programs \[3, 6) differential rc=137' "$od/die.log")" 1
  eq "driver: no heartbeat from a dead batch" "$([ -e "$od/die/heartbeat/heartbeat.txt" ] && echo yes || echo no)" no
  eq "driver: the dead batch's log is kept in the report" "$(grep -c 'out of memory' "$od/die/differential.log")" 1
  rm -rf "$od"
  [ "$bad" -eq 0 ] && echo "k8a-nightly self-test: ok"
  return "$bad"
}

case "${1:-}" in
  plan) shift; plan "$@" ;;
  run) shift; run "$@" ;;
  --self-test) self_test ;;
  *) die "usage: k8a-nightly.sh plan|run|--self-test (see the header)" ;;
esac
