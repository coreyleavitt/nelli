#!/usr/bin/env bash
# The single definition of "compile and run one test": every runner executes
# this, inside the podman container (scripts/dt-bounded.sh) or directly on the
# host (NELLI_HOST=1 dt-bounded.sh, i.e. sweep.sh --host). Flags live here and
# nowhere else.
#
# Usage: scripts/run-one.sh <c|cpp> tests/foo.nim
# Env:   NELLI_NIM_FLAGS  extra nim flags, word-split. The container needs none;
#        a host run sets e.g. `--cc:gcc --colors:off --cincludes:<z3 include>`
#        because the Nim OCI artifact ships Nim alone.
set -uo pipefail
backend="${1:?usage: run-one.sh <c|cpp> <test.nim>}"
test_file="${2:?usage: run-one.sh <c|cpp> <test.nim>}"
# shellcheck disable=SC2086
exec nim "$backend" -r --threads:on --hints:off ${NELLI_NIM_FLAGS:-} "$test_file"
