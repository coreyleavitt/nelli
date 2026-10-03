# Job: S8bw -- new slice (S8bn's remainder)

**Setup.**
- Branch: create `rfc-0005-s8bw` from origin/rfc-0005-s8bn at 22361d7 (base a28c9c3, walker 215).
- Provisional walker: **227**.
- Read first: WORKER-BRIEF.md and the "As landed (S8bn)" notes.
- In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8bw"
title = "S8bn's remainder: walker fault reading an array-global element, aggregate global reads (tuple/object/array globals), pointers into case objects / seqs of aggregates / tables of non-int values, generic case objects"
state = "pending"
```
- Flip the row to `done` at the end.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **SOUNDNESS (crash class): reading `gArr[2]` from an array global faults in the walker.** The `recv.kind == svArray` assertion fires.
   - A walker fault is never an acceptable outcome. Pin the crash first.
   - Then make it decide, which is item 2. Until item 2 lands it must at least decline in-band.
   - Audit every `assert recv.kind ==` / `doAssert ... kind` on a receiver path that a global, a captured value or a heap read can reach. Each one becomes either a modelled case or a named in-band decline.
2. **Aggregate global reads** (`var g: tuple[...]`, object globals, array globals) currently give `feGlobalReadUnmodelled`. Model them with the same frame and heap machinery as scalar globals:
   - element and field reads and writes;
   - writes through a `var` parameter and through `addr`;
   - re-pin S8bn item 4's global path directly on globals, rather than through `var` params.
3. **Pointers into case objects, seqs of aggregates, and tables of non-`int` values decline, and so does every generic case object.** Model them:
   - a variant-arm check at dereference, raising FieldDefect;
   - per-element cells for seqs of aggregates, reusing S8be's;
   - `Table[K, V]` for an aggregate or non-int `V`;
   - generic case objects through monomorphization.

## Integration notes (do not act on them; the batch integrator handles these)
- S8bn's `placeLateAddrs` is superseded by S8bk's `placeLateAddr`.
- S8bn item 4 re-implements element identity; it needs reconciling with S8ax's `elemAddrNode`.

## Verification
- Suites: yours, s8bn, s8bh, s8bf, s8be, s8ax, s8bd, s7_closure, s8i, h_stepC, CR2, and every grep hit for globals or case objects (`command grep -l '^var g\|case kind\|of RootObj' tests/tsymex_*`).
- Run them on Z3 5.1 and 4.13.4, plus one cpp run.
- Push, and report DONE to `worker-reports/s8bw.md`.
