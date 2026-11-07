# UPS-03 (draft, not filed): Z3, invalid read in `spacer::pob_queue::reset()`

Target: Z3Prover/z3. RFC-0016 section 5.6, decision D-0016-3. Drafted
2026-11-07 (W1-z). Nothing here has been filed. nelli does not reach the
fixedpoint API (`src/nelli` has no fixedpoint reference), so this is an
upstream courtesy report, not a nelli defect.

## Title

Valgrind: invalid read of size 1 in `spacer::pob_queue::reset()` of a block
freed earlier in `spacer::context::solve_core` (`Z3_fixedpoint_query`)

## Reproduction

There is no standalone reproduction yet. The read was found through three
nim-z3 test programs, each calling the C API `Z3_fixedpoint_query` from Nim:

- `tests/tfixedpoint.nim`
- `tests/tfixedpoint_newlemma.nim`
- `tests/tfixedpoint_typed_callbacks.nim`

in the nim-z3 repository, at `cc5ffc9` and equally at `ae509f0`. Run, per
file, as `run-tests.sh valgrind <file>`, which expands to:

```
nim c --threads:on --hints:off -d:debug -d:useMalloc --debugger:native --opt:none <f>
valgrind --leak-check=full --num-callers=40 --freelist-vol=400000000 \
  --keep-debuginfo=yes <bin>
```

Each prints one `Invalid read of size 1` and no invalid write or free. The
S8ck job (nelli RFC-0005) wrote a reduction as its item 10; no reduction
exists on disk, so the SMT-LIB / Horn input still has to be extracted
(see below).

## Versions

- Z3 4.13.4 (release build with symbols): the read is in
  `spacer::pob_queue::reset()`, in a block freed earlier in the same
  `spacer::context::solve_core`. Alloc and free stacks contain no wrapper
  code; the only non-Z3 frames are the `Z3_fixedpoint_query` call chain.
- Z3 5.1.0.0: libz3 has no symbols, so the site is inferred from the same read
  size (1), the same offset (78 bytes into a 152-byte block) and the same
  stack shape. Not confirmed by name.
- valgrind 3.27.1, Linux x86-64 (Debian-based container).
- Not tried: Z3 master, other platforms, AddressSanitizer.

## Expected and actual

Expected: no memory error; `pob_queue::reset()` must not read a block that
`solve_core` already freed.

Actual: valgrind reports `Invalid read of size 1`, 78 bytes inside a 152-byte
block that was freed earlier in the same `solve_core` call. Verdicts are
unaffected in the observed runs; the exit code is 0 (the gate runs with
`--error-exitcode=0`).

## How it was observed

nim-z3 leak gate, nelli RFC-0005 slice S8ck item 1 (2026-11): 16 curated test
files plus 11 more hook-family files, on Z3 5.1 and 4.13.4, at two nim-z3
shas. Definite leaks were 0 everywhere; the only invalid access in all 54
(file, Z3 version) pairs per sha is this single read in the three fixedpoint
programs. It is identical at both shas, which rules out the wrapper's
destructors (the shas differ in every hook).

## What a fileable report still needs

1. The Horn / Datalog input each test builds, dumped as SMT-LIB 2 with
   `Z3_fixedpoint_to_string`, reduced to the smallest query that still shows
   the read.
2. A run of that input through the `z3` binary (`z3 fp.engine=spacer in.smt2`)
   under valgrind or ASan, so the report does not need Nim.
3. The 4.13.4 valgrind stack pasted in full, and a check against current Z3
   master.
4. Confirmation on 5.1 with a symbolised build.

Fileable as-is: no (no standalone input or reduction exists; the report needs the Horn problem dumped and reduced, a z3-binary run under valgrind or ASan, and a check on Z3 master)
