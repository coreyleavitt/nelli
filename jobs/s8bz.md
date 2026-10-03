# Job: S8bz -- new slice (S8bw's blocked bullets and remainder)

**HOLD:** do not start until the coordinator says that batch 6 (which will include S8bw) is pushed, and gives you its sha. Base will be **origin/rfc-0005-batch6 at that sha**.
- That base includes S8bs, S8bn, S8bl, S8bq and S8bw, plus everything up to batch 5: S8ar/S8at (Table values), S8bc (tree-seq backing) and S8be (element cells, `isRoutineGlobal`).
- Provisional walker: **232**.

**Before you start**, read WORKER-BRIEF.md, WORKER-LOCAL.md, and the "As landed (S8bw)" notes.

**First commit:** add this row before the S11 row, and flip it to `done` at the end.
```
[[slice]]
id = "S8bz"
title = "S8bw's remainder: pointer into a seq of aggregates, pointer into a Table of string/float/aggregate values (and aggregate Table values themselves), partial writes into unwritten parts, deref onto unwritten candidates, addr of an array element alias, inactive-branch deref, {.global.}/{.noinit.} locals"
state = "pending"
```
Also flip S8bw's row from `pending` to `done`: its blocked bullets now live here.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **A pointer into a seq of aggregates.** Use per-element cells on S8bc's tree-seq backing, reusing S8be's cells.
2. **Table values beyond int:**
   - `Table[K, V]` for aggregate `V` (tuple/object). This declines even on batch 5, so model the value storage first.
   - Pointers into tables of `string`, `float` and aggregate values.
3. **Partial writes into an unwritten part currently decline.** Cover:
   - a symbolic-index write into an array-of-aggregates element;
   - a variant global's partial write;
   - a `var`/`addr` actual whose part is unwritten.
   Model the written-ness per part.
4. **A pointer dereference whose candidate target is an unwritten part declines.** Model it.
5. **`let p = addr gArr[1]` stays heUnsafeCast**, because S8an's alias takes no index. Extend the alias with constant and symbolic indices.
6. **A dereference that may reach an inactive branch declines that sub-path.**
   - Nim 2.2.10 reads the overlapping bytes there. Model that byte-faithfully only where the layout is defined and native runs agree, for example same-size scalar overlap.
   - Otherwise keep a scoped decline, with native evidence for why.
7. **`{.global.}` and `{.noinit.}` locals.**
   - Remove S8bw's parse-time decline in favour of S8be's `isRoutineGlobal`, for `{.global.}`.
   - Model `{.noinit.}` as unwritten. Reads are tainted until written.

## Verification
- Suites:
  - yours;
  - s8bw, s8bn, s8bh, s8be, s8ax, s8bc*, s8ar, s8at, s8an, s8bs (4), s8bf_alias, s7_closure, letaudit, CR2;
  - every Table/ptr/case grep hit.
- Run them on Z3 5.1 and 4.13.4, plus one cpp run.
- Push, then report DONE to `worker-reports/s8bz.md`.
