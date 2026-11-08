#!/usr/bin/env bash
# Windows+vcc FRONT-END check: runs Nim's semantic pass and macro expansion for
# `--os:windows --cc:vcc` and stops before the C compiler. Code that is only
# reached where a replay is re-executed (`replayReexecs`, Windows) is expanded
# here, so a macro-time error in it (RFC-0016 INT-47: "node has no type")
# reproduces on Linux without MSVC. It does not run the result.
#
# Usage: scripts/dt-vcc-frontend.sh <test.nim> [timeout_secs]
# Exit:  0 = the front end accepts the file; non-zero = a compile error.
set -uo pipefail
cd "$(dirname "$0")/.."
test_file="${1:?usage: dt-vcc-frontend.sh <test.nim> [timeout_secs]}"
timeout_secs="${2:-900}"
# `-r` of run-one.sh is moot under --compileOnly; its "cannot run the exe"
# error is the success tail, so the check is on the compiler's own errors.
out=$(NELLI_NIM_FLAGS="--os:windows --cpu:amd64 --cc:vcc --compileOnly --nimcache:/tmp/vccfe" \
  scripts/dt-bounded.sh c "$test_file" "$timeout_secs" 2>&1)
rc=$?
printf '%s\n' "$out" | command grep -v 'instantiation of\|Warning'
if [ "$rc" -eq 137 ]; then exit 137; fi
if printf '%s\n' "$out" | command grep -q ') Error: '; then exit 1; fi
exit 0
