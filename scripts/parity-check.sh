#!/usr/bin/env bash
# C/C++ backend parity gate (CR-8 Part A).
#
# PURPOSE: Run a single Phase-15 test file under BOTH the `c` and `cpp` Nim
# backends via dt-bounded.sh and fail (non-zero exit) if either backend fails
# or if their pass/fail status diverges. This is the canonical "both backends
# must agree" check that the RFC Phase-15 DoD requires. Before CR-8 this was a
# manual workflow step; running this script makes it an automated regression.
#
# Usage:  scripts/parity-check.sh <test.nim> [timeout_secs]
# Exit:   0 = both backends passed and AGREE
#         1 = one or both backends failed, or their status diverges
#        137 = at least one backend HUNG (killed at timeout — non-termination)
#
# Wraps dt-bounded.sh, which handles podman image lookup, container teardown,
# and the 137/124 HUNG exit codes. Mirrors the style of dt-bounded.sh.
set -uo pipefail
cd "$(dirname "$0")/.."

test_file="${1:?usage: parity-check.sh <test.nim> [timeout_secs]}"
timeout_secs="${2:-180}"

run_backend() {
  local backend="$1"
  echo "=== parity-check: running $backend backend ===" >&2
  scripts/dt-bounded.sh "$backend" "$test_file" "$timeout_secs"
}

rc_c=0
rc_cpp=0

run_backend c
rc_c=$?

run_backend cpp
rc_cpp=$?

echo "=== parity-check results ===" >&2
echo "  c   exit: $rc_c" >&2
echo "  cpp exit: $rc_cpp" >&2

# HUNG check: 137 from dt-bounded.sh means the run was killed at timeout.
if [ "$rc_c" -eq 137 ] || [ "$rc_cpp" -eq 137 ]; then
  echo "PARITY-CHECK FAIL: at least one backend HUNG (exit 137) — non-termination defect." >&2
  exit 137
fi

# Parity divergence check: both exits must agree (both 0 or both non-0).
if [ "$rc_c" -eq 0 ] && [ "$rc_cpp" -eq 0 ]; then
  echo "PARITY-CHECK PASS: both backends agree (both passed)." >&2
  exit 0
fi

if [ "$rc_c" -ne 0 ] && [ "$rc_cpp" -ne 0 ]; then
  echo "PARITY-CHECK FAIL: both backends failed (rc_c=$rc_c, rc_cpp=$rc_cpp)." >&2
  exit 1
fi

# Divergence: one passed, the other failed.
echo "PARITY-CHECK FAIL: backends DIVERGE (c=$rc_c, cpp=$rc_cpp) — backend-specific regression!" >&2
exit 1
