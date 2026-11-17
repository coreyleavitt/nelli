#!/usr/bin/env bash
# RFC-0016 K8c: build libz3 from source with AddressSanitizer, into a prefix
# that has the same layout as the release zip (bin/libz3.so*, include/z3*.h),
# so setup-z3-linux's exports (LD_LIBRARY_PATH, NELLI_Z3_INCLUDE) work on it
# unchanged.
#
# Why this exists. A reference-count error on a Z3 AST handle (CRH-07's class)
# frees the node INSIDE libz3, and the stale read is in libz3 too. ASan only
# reports accesses made by instrumented code, so a nelli-only ASan build prints
# the stale string and exits 0 (tests/asan/plant_z3_overrelease.nim shows it).
#
# Usage: scripts/build-z3-asan.sh <version> <prefix> [workdir]
#   version  a Z3 release tag suffix, e.g. 5.1.0 (tag z3-<version>)
#   prefix   install prefix (bin/, include/, lib/)
# Env:   Z3_ASAN_JOBS  parallel jobs (default nproc)
#        Z3_SRC_TARBALL  use this tarball instead of downloading
#
# The build is Release (-O2, so the corpus stays inside the job budget) with
# `-fsanitize=address -fno-omit-frame-pointer -g1`, internal mpz (no GMP: the
# GMP build trips UPS-02's nlsat VERIFY, and drops a dependency), no Python
# bindings, no .NET/Java. The z3 executable is built too: it is the cheapest
# smoke test of the instrumented library.
set -euo pipefail
ver="${1:?usage: build-z3-asan.sh <version> <prefix> [workdir]}"
prefix="${2:?usage: build-z3-asan.sh <version> <prefix> [workdir]}"
work="${3:-$(mktemp -d)}"
jobs="${Z3_ASAN_JOBS:-$(nproc)}"
mkdir -p "$work" "$prefix"
tarball="${Z3_SRC_TARBALL:-$work/z3-$ver.tar.gz}"
if [ ! -s "$tarball" ]; then
  curl -fsSL --retry 5 -o "$tarball" "https://github.com/Z3Prover/z3/archive/refs/tags/z3-$ver.tar.gz"
fi
rm -rf "$work/src" "$work/build"
mkdir -p "$work/src" "$work/build"
tar -xzf "$tarball" -C "$work/src" --strip-components=1
# Z3 serves every AST node (< 8 KB) from small_object_allocator's pooled chunks,
# so a freed node never reaches free() and ASan cannot poison it: the planted
# over-release is silent even in an instrumented libz3. Z3 ships a bypass for
# valgrind, `defined(Z3DEBUG) && !defined(_WINDOWS)` in allocate/deallocate,
# but Z3DEBUG also turns on every SASSERT (far too slow for the corpus). Take
# the bypass alone; the header (the object layout) is untouched.
sed -i 's/defined(Z3DEBUG) && !defined(_WINDOWS)/1/' "$work/src/src/util/small_object_allocator.cpp"
[ "$(grep -c '^#if 1$' "$work/src/src/util/small_object_allocator.cpp")" = 2 ] \
  || { echo "build-z3-asan: the small_object_allocator bypass did not patch (source layout moved?)" >&2; exit 1; }
san="-fsanitize=address -fno-omit-frame-pointer -g1"
gen=()
command -v ninja >/dev/null 2>&1 && gen=(-G Ninja)
cmake -S "$work/src" -B "$work/build" "${gen[@]}" \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_FLAGS="$san" -DCMAKE_CXX_FLAGS="$san" \
  -DCMAKE_SHARED_LINKER_FLAGS="-fsanitize=address" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address" \
  -DCMAKE_INSTALL_PREFIX="$prefix" \
  -DCMAKE_INSTALL_LIBDIR=bin \
  -DZ3_USE_LIB_GMP=OFF -DZ3_BUILD_LIBZ3_SHARED=ON \
  -DZ3_BUILD_PYTHON_BINDINGS=OFF -DZ3_BUILD_JAVA_BINDINGS=OFF \
  -DZ3_BUILD_DOTNET_BINDINGS=OFF -DZ3_BUILD_TEST_EXECUTABLES=OFF \
  -DZ3_ENABLE_EXAMPLE_TARGETS=OFF
cmake --build "$work/build" -j "$jobs"
cmake --install "$work/build"
# the release zip's layout: bin/libz3.so, include/z3.h
ls -l "$prefix"/bin/libz3.so* "$prefix"/include/z3.h
# the library must carry ASan instrumentation
if command -v nm >/dev/null 2>&1 && nm -D "$prefix"/bin/libz3.so | grep -q __asan_report; then
  echo "build-z3-asan: libz3 is ASan-instrumented"
else
  echo "build-z3-asan: libz3 shows no __asan_report symbols" >&2; exit 1
fi
