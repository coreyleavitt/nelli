#!/usr/bin/env bash
# Windows cross-compile CHECK (Eci): compile+link a module or test for
# --os:windows via the container's mingw64 cross toolchain. This catches
# Windows API misuse, missing `when defined(posix)` gating, and linker
# errors at build time — it CANNOT run the result. Run-verification for
# Windows-only behavior goes through the CI Windows leg (push-and-wait;
# see docs/RFC-fuzzer-nextgen.windows-capability.md).
#
# Usage: scripts/dt-crosswin.sh <c|cpp> <file.nim> [timeout_secs]
# Exit:  0 = cross-compiles+links; 137 = compile HUNG (killed); other = failure.
set -uo pipefail
cd "$(dirname "$0")/.."
backend="${1:?usage: dt-crosswin.sh <c|cpp> <file.nim> [timeout_secs]}"; shift
nim_file="${1:?usage: dt-crosswin.sh <c|cpp> <file.nim> [timeout_secs]}"; shift
timeout_secs="${1:-300}"
img=localhost/nelli-dev:latest
podman image exists "$img" || scripts/build-dev-image.sh

cname="dtxwin_$(basename "$nim_file" .nim)_${backend}_$$"
cleanup() { podman rm -f "$cname" >/dev/null 2>&1 || true; }
trap cleanup EXIT
cleanup

# --compileOnly is NOT used: linking is the phase that catches a missing
# Windows symbol, so we go all the way to a .exe (discarded).
timeout --signal=KILL "$timeout_secs" podman run --rm --name "$cname" \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work \
  "$img" \
  bash -c 'nim "$1" --os:windows --cpu:amd64 -d:mingw --threads:on \
    --amd64.windows.gcc.exe:x86_64-w64-mingw32-gcc \
    --amd64.windows.gcc.linkerexe:x86_64-w64-mingw32-gcc \
    --amd64.windows.gcc.cpp.exe:x86_64-w64-mingw32-g++ \
    --amd64.windows.gcc.cpp.linkerexe:x86_64-w64-mingw32-g++ \
    --cincludes:/opt/z3-headers \
    --hints:off --nimcache:/tmp/xwin_cache \
    -o:/tmp/xwin_out.exe "$2"' _ "$backend" "$nim_file"
rc=$?
if [ "$rc" -eq 137 ] || [ "$rc" -eq 124 ]; then
  echo ">>> HUNG: cross-compile of $nim_file ($backend) killed after ${timeout_secs}s." >&2
  exit 137
fi
exit "$rc"
