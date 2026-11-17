#!/usr/bin/env bash
# RFC-0016 K8c (CRH-07): the walker under AddressSanitizer. Builds and runs a
# core set plus a rotating slice of the registered tsymex_ corpus with
# nelli AND libz3 built under ASan, and fails on any sanitizer report.
#
# Why libz3 has to be instrumented too. A reference-count error on a Z3 AST
# handle (the CRH-07 class) frees the node inside libz3 and the stale read is
# made by libz3 as well. ASan reports only accesses made by instrumented
# code, so with a stock libz3 the program prints the stale value and exits 0
# (--self-test proves it with tests/asan/plant_z3_overrelease.nim). The job
# therefore points LD_LIBRARY_PATH at an ASan-built libz3
# (scripts/build-z3-asan.sh, cached by version in CI) and the self-test
# refuses to start the slice unless that library catches the planted over-release.
#
# Flags (one definition, here): `--mm:orc -d:useMalloc` so ASan sees Nim's
# allocations (Nim's own arena is invisible to it), `-fsanitize=address` on
# compile and link, frame pointers and native debug info for readable traces.
#
# libstdc++ is a STARTUP dependency of the executable (`-Wl,--push-state,
# --no-as-needed,-l:libstdc++.so.6,--pop-state`). ASan resolves the real `__cxa_throw`
# when the process starts, and the C backend's executable links no C++ runtime
# (only libz3, loaded later, does), so the first C++ exception libz3 throws
# internally (ordinary control flow: a probe, an ill-sorted term the API turns
# into an error code) hit `CHECK failed: asan_interceptors.cpp real___cxa_throw
# != 0` and killed every test of the first nightly (run 44040495505). Plain
# `-lstdc++` is not enough: Ubuntu's gcc links with --as-needed and drops it,
# as nothing the executable itself references is in libstdc++, and it needs the
# -dev symlink, which a gcc-only image lacks (so the soname is named).
# The reason the first run on a developer machine passed: openSUSE's
# libasan.so.8 itself NEEDs libstdc++.so.6, so the container's executable always
# had it; Ubuntu's libasan does not, so only the CI job hit the abort. The self-test's
# third plant (tests/asan/plant_z3_throw.nim) fails the job if this link goes
# missing.
#
# Leaks: LeakSanitizer is ON (detect_leaks=1, S8ck-r). A leak report fails the
# test like any other sanitizer report. tests/asan/lsan.supp suppresses only
# frames outside nelli (nim-z3's open INF-04 items), one sourced reason and
# retirement condition per entry; a leak under src/nelli is fixed, never
# suppressed. The self-test's fourth plant (tests/asan/plant_nim_leak.nim)
# fails the job if leak detection is off or swallowed. Nim 2.2.10 itself
# leaks in three shapes nelli met, each worked around rather than
# suppressed: a first write that is a bitwise copy
# (tests/asan/nim_firstwrite_leak.nim; tsymex_0016_s8ckr_firstwrite_audit
# keeps the shape out of src/), a never-read string cursor
# (nim_cursor_strlit_leak.nim), and threadvars never destroyed at thread
# exit (nim_threadvar_exit_leak.nim; releaseSymexThreadState).
#
# The slice: the CORE set (the suites that exercise Z3 AST lifetime hardest:
# heap, strings, regex, closures, raise paths, cache replay) always runs, then
# every STRIDE-th registered tsymex_ test starting at OFFSET (day of year modulo
# the stride), as scripts/vm-alias-slice.sh does, so the whole corpus is
# covered in STRIDE nights.
#
# Usage: scripts/asan-slice.sh [-n COUNT] [-o OFFSET] [-t SECS] [-B BUDGET] <outlog>
#        scripts/asan-slice.sh --self-test
#   -n COUNT   about this many rotating tests besides the core (default 24; the nightly passes 12)
#   -o OFFSET  slice offset (default: day of year modulo the stride)
#   -t SECS    per-test timeout (default 1200)
#   -B BUDGET  stop starting new tests after this many seconds (default 5400);
#              the core always runs first, the unstarted tail is listed
# Env:   NELLI_NIM_FLAGS  host flags (--cc, --path, --cincludes), as the other
#        host scripts take them; the ASan flags are appended here.
#        NELLI_HOST=1 runs without podman (CI). ASAN_OPTIONS is set here.
# Output: <outlog> in sweep.sh's `<rc> <backend> <file> <warn>` shape,
# <outlog>.times, <outlog>.san (tests with a sanitizer report: `<file> <kind>`),
# <outlog>.summary. Exit 0 if the log was written; the gate reads .san and the log.
set -uo pipefail
cd "$(dirname "$0")/.."

# One definition of the sanitizer build.
asan_flags="--mm:orc -d:useMalloc --debugger:native --passC:-fsanitize=address --passC:-fno-omit-frame-pointer --passL:-fsanitize=address --passL:-Wl,--push-state,--no-as-needed,-l:libstdc++.so.6,--pop-state"
export ASAN_OPTIONS="detect_leaks=1:halt_on_error=1:abort_on_error=0:detect_odr_violation=0:symbolize=1:print_summary=1"
# The suppression file as the test process sees it: the repo is /work in the
# podman container, the checkout itself on a host run.
if [ -n "${NELLI_HOST:-}" ]; then supp="$PWD/tests/asan/lsan.supp"; else supp=/work/tests/asan/lsan.supp; fi
export LSAN_OPTIONS="suppressions=$supp:print_suppressions=1"
export NELLI_NIM_FLAGS="${NELLI_NIM_FLAGS:-} $asan_flags"

# Suites that exercise Z3 AST lifetime hardest. Every name must be registered.
core=(
  tsymex_h_stepC_heapidentity tsymex_r6_heap_raise_totality tsymex_phase15_r1b_callheap   # heap
  tsymex_rfc0005_s8ca_strings tsymex_r6_b1_stringbacked                                    # strings
  tsymex_phase15_S6a_regex_parser tsymex_phase15_S6b_regex tsymex_rfc0005_s8cf_classes     # regex
  tsymex_rfc0005_s8ca_closures_heap tsymex_phase15_CR1_CR5_closure_heap                    # closures
  tsymex_r6_n36_raise_class_audit tsymex_rfc0005_s8ce_raiseshapes tsymex_r6_n37_raise_residue  # raise paths
  tsymex_rfc0005_s2_replay tsymex_rfc0005_s8cb_replay tsymex_phase15_CR2_cachekey tsymex_0016_w1d1c_cachedprune  # cache replay
)

# $1 = test file, $2 = timeout; stdout+stderr to $3; echoes the rc
run_one() { scripts/dt-bounded.sh c "$1" "$2" > "$3" 2>&1; echo $?; }
# the sanitizer kind a report names, or empty
san_kind() { command grep -m1 -o -E '(AddressSanitizer|LeakSanitizer): [A-Za-z-]+' "$1" | sed 's/: /:/'; }

if [ "${1:-}" = "--self-test" ]; then
  d="$(mktemp -d)"; trap 'rm -rf "$d"' EXIT
  fail=0
  # 1. a use-after-free in plain Nim memory: the flags work and ASan is on
  rc="$(run_one tests/asan/plant_nim_uaf.nim 600 "$d/nim.out")"
  k="$(san_kind "$d/nim.out")"
  if [ "$rc" != 0 ] && [ "$k" = "AddressSanitizer:heap-use-after-free" ]; then
    echo "asan self-test: plant_nim_uaf failed as it must (rc=$rc, $k)"
  else echo "asan self-test FAILED: plant_nim_uaf rc=$rc kind='$k' (a real UAF must abort under the job's flags)"; tail -n 20 "$d/nim.out"; fail=1; fi
  # 2. an over-released Z3 AST: libz3 is instrumented
  rc="$(run_one tests/asan/plant_z3_overrelease.nim 600 "$d/z3.out")"
  k="$(san_kind "$d/z3.out")"
  if [ "$rc" != 0 ] && [ "$k" = "AddressSanitizer:heap-use-after-free" ] && command grep -q 'ast_manager::' "$d/z3.out"; then
    echo "asan self-test: plant_z3_overrelease failed as it must (rc=$rc, $k, ast_manager frames in libz3)"
  else echo "asan self-test FAILED: plant_z3_overrelease rc=$rc kind='$k' (libz3 is not ASan-built, or the over-release went unseen)"; tail -n 20 "$d/z3.out"; fail=1; fi
  # 3. libz3 throws a C++ exception internally and recovers: libstdc++ is linked
  # into the executable at startup (the CHECK abort of the first nightly)
  rc="$(run_one tests/asan/plant_z3_throw.nim 600 "$d/throw.out")"
  if [ "$rc" = 0 ] && command grep -q 'z3 threw and recovered' "$d/throw.out" && ! command grep -q 'Sanitizer' "$d/throw.out"; then
    echo "asan self-test: plant_z3_throw exited cleanly (an internal Z3 C++ exception passes the interceptor)"
  else echo "asan self-test FAILED: plant_z3_throw rc=$rc (an internal Z3 exception must not abort: is libstdc++ linked at startup?)"; tail -n 20 "$d/throw.out"; fail=1; fi
  # 4. a dropped heap block: LeakSanitizer is on, and the suppressions do not
  # swallow a leak in plain program code
  rc="$(run_one tests/asan/plant_nim_leak.nim 600 "$d/leak.out")"
  k="$(san_kind "$d/leak.out")"
  if [ "$rc" != 0 ] && [ "$k" = "LeakSanitizer:detected" ] && command grep -q 'leakOne' "$d/leak.out"; then
    echo "asan self-test: plant_nim_leak failed as it must (rc=$rc, $k, leakOne named)"
  else echo "asan self-test FAILED: plant_nim_leak rc=$rc kind='$k' (a dropped heap block must be reported: is detect_leaks on, useMalloc set, the suppression file narrow?)"; tail -n 20 "$d/leak.out"; fail=1; fi
  exit "$fail"
fi

count=24; offset=; tmo=1200; budget=5400
while getopts ":n:o:t:B:" o; do
  case "$o" in n) count="$OPTARG" ;; o) offset="$OPTARG" ;; t) tmo="$OPTARG" ;; B) budget="$OPTARG" ;;
    *) sed -n '/^# Usage:/,/^# Env:/p' "$0" >&2; exit 2 ;; esac
done
shift $((OPTIND - 1))
outlog="${1:?usage: asan-slice.sh [-n N] [-o OFF] [-t SECS] [-B SECS] <outlog>}"

mapfile -t all < <(sed -n '/for f in \[/,/\]:/p' nelli.nimble | sed 's/#.*$//' \
  | command grep -o '"[^"]*"' | tr -d '"' | command grep '^tsymex_' | LC_ALL=C sort -u)
n=${#all[@]}
[ "$n" -ge 100 ] || { echo "asan-slice.sh: only $n tsymex_ tests registered" >&2; exit 2; }
declare -A is_reg is_core
for t in "${all[@]}"; do is_reg[$t]=1; done
for c in "${core[@]}"; do is_core[$c]=1; done
for c in "${core[@]}"; do
  [ -n "${is_reg[$c]:-}" ] || { echo "asan-slice.sh: core test $c is not registered in nelli.nimble" >&2; exit 2; }
done
stride=$(( n / count )); [ "$stride" -ge 1 ] || stride=1
[ -n "$offset" ] || offset=$(( 10#$(date -u +%j) % stride ))
set_=("${core[@]}")
for (( i = offset; i < n; i += stride )); do
  [ -n "${is_core[${all[$i]}]:-}" ] || set_+=("${all[$i]}")
done

: > "$outlog"; : > "$outlog.times"; : > "$outlog.san"
echo "asan-slice: ${#set_[@]} tests (${#core[@]} core, stride $stride, offset $offset of $n registered)" >&2
notrun=()
for t in "${set_[@]}"; do
  if [ "$SECONDS" -gt "$budget" ]; then notrun+=("$t"); continue; fi
  f="tests/$t.nim"; t0=$EPOCHREALTIME
  rc="$(run_one "$f" "$tmo" "$outlog.$t.out")"
  echo "$rc c $f 0" >> "$outlog"
  awk -v a="$t0" -v b="$EPOCHREALTIME" -v f="$f" 'BEGIN { printf "%.1f c %s\n", b - a, f }' >> "$outlog.times"
  k="$(san_kind "$outlog.$t.out")"
  [ -z "$k" ] || { echo "$f $k" >> "$outlog.san"; echo "SANITIZER REPORT in $t: $k" >&2; command grep -n -A40 -m1 -E 'ERROR: (Address|Leak)Sanitizer' "$outlog.$t.out" >&2; }
  if [ "$rc" -eq 0 ]; then rm -f "$outlog.$t.out"; else echo "rc=$rc: $t" >&2; fi
done
{
  echo "asan slice: ${#set_[@]} tests (${#core[@]} core), stride $stride, offset $offset, registered $n"
  echo "pass=$(awk '$1 == "0"' "$outlog" | wc -l | tr -d ' ') fail=$(awk '$1 != "0"' "$outlog" | wc -l | tr -d ' ') sanitizer=$(wc -l < "$outlog.san" | tr -d ' ') notrun=${#notrun[@]}"
  awk '$1 != "0" {print "FAIL " $3}' "$outlog"
  awk '{print "SAN " $0}' "$outlog.san"
  for t in "${notrun[@]}"; do echo "NOTRUN $t"; done
} > "$outlog.summary"
cat "$outlog.summary" >&2
exit 0
