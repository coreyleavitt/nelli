# UPS-03 (filed 2026-11-07 as Z3Prover/z3#11601): Z3, invalid read in `spacer::pob_queue::reset()` (`Z3_fixedpoint_query`)

Target: Z3Prover/z3. RFC-0016 section 5.6, decision D-0016-3. Reproduced
standalone 2026-11-07 (W1-z follow-up). Nothing here has been filed. nelli
does not reach the fixedpoint API, so this is an upstream courtesy report.

## Title

Valgrind: invalid read of size 1 in `spacer::pob_queue::reset()` on the second
`Z3_fixedpoint_query` against the same fixedpoint object (Spacer)

## Summary

Calling `Z3_fixedpoint_query` twice on the same `Z3_fixedpoint` with the Spacer
engine makes the second call read a `pob` that the second call's own
`solve_core` has just freed. Verdicts are correct (`sat`, `sat`); the exit
code is 0. The problem needs no rules beyond one fact. It reproduces on
4.13.4, 5.1.0.0 and the 5.4.0 nightly built from master (build hashcode
a8070934de032ae17bec3672e3b4a45aef703a90, published 2026-11-07).

## Reproduction

Input (`UPS-03-min.smt2`, 4 lines):

```
(declare-rel Q ())
(rule Q)
(query Q)
(query Q)
```

Driver (`UPS-03-fpdrv.c`): parses the file with `Z3_fixedpoint_from_file` on a
Spacer fixedpoint (`engine=spacer`), then calls `Z3_fixedpoint_query` once per
`(query ...)` returned, in order, on the one fixedpoint object. Full source:

```c
/* Standalone driver: parse an SMT-LIB 2 fixedpoint problem (declare-rel /
   declare-var / rule / query) and run Z3_fixedpoint_query on it.
   Build: gcc -g -o fpdrv fpdrv.c -lz3 */
#include <stdio.h>
#include <stdlib.h>
#include <z3.h>

static void on_err(Z3_context c, Z3_error_code e) {
  fprintf(stderr, "z3 error %d: %s\n", (int)e, Z3_get_error_msg(c, e));
  exit(2);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: fpdrv file.smt2 [engine]\n"); return 2; }
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);
  Z3_set_error_handler(ctx, on_err);
  Z3_fixedpoint fp = Z3_mk_fixedpoint(ctx);
  Z3_fixedpoint_inc_ref(ctx, fp);
  Z3_params p = Z3_mk_params(ctx);
  Z3_params_inc_ref(ctx, p);
  Z3_params_set_symbol(ctx, p, Z3_mk_string_symbol(ctx, "engine"),
                       Z3_mk_string_symbol(ctx, argc > 2 ? argv[2] : "spacer"));
  Z3_fixedpoint_set_params(ctx, fp, p);
  Z3_ast_vector qs = Z3_fixedpoint_from_file(ctx, fp, argv[1]);
  Z3_ast_vector_inc_ref(ctx, qs);
  unsigned n = Z3_ast_vector_size(ctx, qs);
  for (unsigned i = 0; i < n; i++) {
    Z3_lbool r = Z3_fixedpoint_query(ctx, fp, Z3_ast_vector_get(ctx, qs, i));
    printf("query %u: %s\n", i, r == Z3_L_TRUE ? "sat" : r == Z3_L_FALSE ? "unsat" : "unknown");
  }
  Z3_ast_vector_dec_ref(ctx, qs);
  Z3_params_dec_ref(ctx, p);
  Z3_fixedpoint_dec_ref(ctx, fp);
  Z3_del_context(ctx);
  return 0;
}
```

Commands (any Linux with libz3 and valgrind):

```
gcc -g -o fpdrv fpdrv.c -lz3
valgrind --num-callers=40 --freelist-vol=400000000 --keep-debuginfo=yes ./fpdrv min.smt2
```

Expected output: `query 0: sat`, `query 1: sat`, and no memory error.
Actual: both queries print `sat`, and valgrind reports one `Invalid read of
size 1` (counted as 2 errors in the summary) during the second query. A
single `(query Q)` is clean; three queries give a second report (4 errors).

Reduction notes (4.13.4, each tried under valgrind):

- One query, on any of the problems tried: clean. Two queries: reported for
  sat+sat (nullary and non-nullary query relation), for unsat+unsat on a
  counter-chain problem and for sat-then-unsat on the graph problem; clean
  for sat-then-unsat and unsat-then-sat on a 3-rule problem and for
  unsat+unsat on a trivial one. So two queries is necessary, not sufficient.
- The fact `(rule Q)` is enough; no recursion, no integers, no variables.

The original three nim-z3 tests were not needed for the reduction. The one run
here, `tests/tfixedpoint.nim` (nim-z3 ac6020a, `-d:useMalloc` build, valgrind
3.27.1, Z3 4.13.4), shows the identical report at the second query of its
"graph reachability" test (`path(1,4)` sat, then `path(4,1)` unsat). That
problem, translated by hand to SMT-LIB 2 (not dumped from the Nim program),
gives the same report through the C driver:

```
(declare-rel edge (Int Int))
(declare-rel path (Int Int))
(declare-rel Q1 ())
(declare-rel Q2 ())
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(rule (=> (edge x y) (path x y)))
(rule (=> (and (path x y) (edge y z)) (path x z)))
(rule (edge 1 2))
(rule (edge 2 3))
(rule (edge 3 4))
(rule (=> (path 1 4) Q1))
(rule (=> (path 4 1) Q2))
(query Q1)
(query Q2)
```

(The other two nim-z3 tests, `tfixedpoint_newlemma.nim` and
`tfixedpoint_typed_callbacks.nim`, were not re-run; both issue repeated
queries on one fixedpoint.)

## Versions

| Z3 | How obtained | Symbols | Result |
|---|---|---|---|
| 4.13.4.0 | openSUSE Tumbleweed `libz3.so.4.13` | yes | reproduces |
| 5.1.0.0 | openSUSE Tumbleweed `libz3.so.5.1.0.0` | no | reproduces (same address offset and block size) |
| 5.4.0 nightly, hash a8070934de03 | `Z3Prover/z3` release "Nightly", `z3-5.4.0-x64-glibc-2.39.zip`, 2026-11-07 | yes | reproduces |

Also: valgrind 3.27.1, Linux x86-64 (openSUSE Tumbleweed container, gcc). The
`z3` command-line binary (nightly) running `z3 fp.engine=spacer min.smt2`
under valgrind does NOT show the read (prints `sat sat`, 0 errors), so the
report must use the C API driver, not the binary.

## Valgrind output, Z3 4.13.4 (full error block, driver above)

```
==7== Invalid read of size 1
==7==    at 0x4C75670: spacer::pob_queue::reset() (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C7C156: spacer::context::solve_core(unsigned int) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C7C524: spacer::context::solve(unsigned int) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4CDB7B2: spacer::dl_interface::query(expr*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4EB7EF3: datalog::context::query(expr*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4AF9CCC: Z3_fixedpoint_query (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4014BD: main (fpdrv.c:30)
==7==  Address 0x7ffc57e is 78 bytes inside a block of size 152 free'd
==7==    at 0x48519BF: free (in /usr/libexec/valgrind/vgpreload_memcheck-amd64-linux.so)
==7==    by 0x60BC320: memory::deallocate(void*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C7C12B: spacer::context::solve_core(unsigned int) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C7C524: spacer::context::solve(unsigned int) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4CDB7B2: spacer::dl_interface::query(expr*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4EB7EF3: datalog::context::query(expr*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4AF9CCC: Z3_fixedpoint_query (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4014BD: main (fpdrv.c:30)
==7==  Block was alloc'd at
==7==    at 0x484E958: malloc (in /usr/libexec/valgrind/vgpreload_memcheck-amd64-linux.so)
==7==    by 0x60BC388: memory::allocate(unsigned long) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C63E41: spacer::pred_transformer::pob_manager::mk_pob(spacer::pob*, unsigned int, unsigned int, expr*, ref_vector<app, ast_manager> const&) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C7C105: spacer::context::solve_core(unsigned int) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4C7C524: spacer::context::solve(unsigned int) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4CDB7B2: spacer::dl_interface::query(expr*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4EB7EF3: datalog::context::query(expr*) (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4AF9CCC: Z3_fixedpoint_query (in /usr/lib64/libz3.so.4.13)
==7==    by 0x4014BD: main (fpdrv.c:30)
```

## Valgrind output, Z3 5.4.0 nightly (symbols)

```
==8== Invalid read of size 1
==8==    at 0x5A62C09: spacer::pob_queue::reset() (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A8238A: spacer::context::solve_core(unsigned int) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A82934: spacer::context::solve(unsigned int) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A88D36: spacer::dl_interface::query(expr*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x58F43ED: datalog::context::query(expr*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x4C66475: Z3_fixedpoint_query (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x4014BD: main (fpdrv.c:30)
==8==  Address 0x878d6ee is 78 bytes inside a block of size 152 free'd
==8==    at 0x48519BF: free (in /usr/libexec/valgrind/vgpreload_memcheck-amd64-linux.so)
==8==    by 0x66C4A90: memory::deallocate(void*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A82367: spacer::context::solve_core(unsigned int) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A82934: spacer::context::solve(unsigned int) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A88D36: spacer::dl_interface::query(expr*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x58F43ED: datalog::context::query(expr*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x4C66475: Z3_fixedpoint_query (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x4014BD: main (fpdrv.c:30)
==8==  Block was alloc'd at
==8==    at 0x484E958: malloc (in /usr/libexec/valgrind/vgpreload_memcheck-amd64-linux.so)
==8==    by 0x66C4B00: memory::allocate(unsigned long) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A6A551: spacer::pred_transformer::pob_manager::mk_pob(spacer::pob*, unsigned int, unsigned int, expr*, ref_vector<app, ast_manager> const&) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A82340: spacer::context::solve_core(unsigned int) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A82934: spacer::context::solve(unsigned int) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x5A88D36: spacer::dl_interface::query(expr*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x58F43ED: datalog::context::query(expr*) (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x4C66475: Z3_fixedpoint_query (in /w/nightly/x/z3-5.4.0-x64-glibc-2.39/bin/libz3.so)
==8==    by 0x4014BD: main (fpdrv.c:30)
```

## Valgrind output, Z3 5.1.0.0 (no symbols)

```
==7== Invalid read of size 1
==7==    at 0x580F21B: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x581CD35: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x56D9CF1: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x5941404: Z3_fixedpoint_query (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x4014BD: main (fpdrv.c:30)
==7==  Address 0x78bc02e is 78 bytes inside a block of size 152 free'd
==7==    at 0x48519BF: free (in /usr/libexec/valgrind/vgpreload_memcheck-amd64-linux.so)
==7==    by 0x4AF1840: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x580F1D6: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x581CD35: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x56D9CF1: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x5941404: Z3_fixedpoint_query (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x4014BD: main (fpdrv.c:30)
==7==  Block was alloc'd at
==7==    at 0x484E958: malloc (in /usr/libexec/valgrind/vgpreload_memcheck-amd64-linux.so)
==7==    by 0x4AF18B3: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x5800127: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x580F1B6: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x581CD35: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x56D9CF1: ??? (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x5941404: Z3_fixedpoint_query (in /usr/lib64/libz3.so.5.1.0.0)
==7==    by 0x4014BD: main (fpdrv.c:30)
```

## Likely cause (from reading master, not verified by a patch)

`spacer_context.cpp`, `pob_queue::set_root`:

```
void pob_queue::set_root(pob& root) {
    m_root = &root;          // pob_ref: drops the previous query's root
    ...
    reset();                 // walks m_data, calling p->set_in_queue(false)
}
```

`context::solve_core` calls `m_pob_queue.set_root(*root)` for each query. On the
second query `m_root = &root` releases the previous root `pob` (the free in the
report is in `solve_core`, i.e. `set_root` inlined). `m_data` still holds raw
`pob*` from the first query, and `reset()` then pops them and calls
`set_in_queue(false)` on a pointer into the freed block. Offset 78 of a
152-byte block is consistent with the `m_in_queue` flag. Untested suggestion:
call `reset()` before replacing `m_root`, or clear `m_data` first.

## How it was found

nim-z3 leak gate, nelli RFC-0005 slice S8ck: 16 curated test files plus 11
hook-family files, Z3 5.1 and 4.13.4, two nim-z3 shas, 54 (file, Z3 version)
pairs per sha. The only invalid access in all of them was this read in the
three fixedpoint programs; definite leaks were 0 everywhere.

Fileable as-is: yes (4-line input plus a ~35-line C driver reproduce the read under valgrind on Z3 4.13.4, 5.1.0.0 and a 2026-11-07 5.4.0 master nightly with symbols; caveat: the z3 command-line binary does not show it, so the report must use the C API driver)
