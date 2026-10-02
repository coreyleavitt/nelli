# Job: S8bl -- new slice (S8bc's remainder)

Work in your own worktree under /home/corey/tmp-usage/work/wt, with branch
`rfc-0005-s8bl` created from origin/rfc-0005-s8bc (22b67c7, walker 203).
Provisional walker **213**. Read WORKER-BRIEF.md first, then the
"As landed (S8bc)" notes on that branch.

Add this row before the S11 row in your first commit, and flip it to `done`
at the end:
```
[[slice]]
id = "S8bl"
title = "S8bc's remainder: var-param magics beyond inc/dec (swap etc.), non-terminating unrecognized pair loop, unbacked-element add fault, type aliases, inc borrow arity, borrow-view coverage, for-in array literal, mpairs/mvalues, table length change during iteration, ref-part seq element witnesses, long nested seqs in witnesses"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each wrong verdict or crash RED first)
1. **SOUNDNESS: bodiless `{.magic.}` routines with `var` params are no-ops
   beyond inc/dec.** `swap(a[0], a[2])` gives a false sxSat.
   - Enumerate every system magic with a `var` param that a target can call:
     swap, add on string/seq, setLen, del, insert, delete, shallowCopy,
     wasMoved, reset, `=sink`/`=copy` if reachable, `incl`/`excl`, `inc`/`dec`
     with a second argument, and any others you find in system.nim.
   - Model each one exactly. Where that is impossible, make it a scoped
     decline that names the magic.
   - Never let one be a silent no-op. Add a guard test that scans for
     unhandled var-param magics.
2. **A non-recognized pair loop does not terminate in 900 s**, even with no
   accumulator. B6-1-red and B6-6 take 200-285 s each, and `r6_b6_optionregion`
   needs 732 s alone, so it gets killed under parallel load.
   - Find out why the walk does not terminate. Then make it terminate within
     budget with a named decline, or model it.
   - Bring `r6_b6_optionregion` under the sweep's 900 s cap with margin, at
     -j 4 load.
3. **`add` to a local seq of an unbacked element** files `weInternalWalkerFault`.
   Make it a proper placeholder decline, or model it.
4. **Smaller gaps:**
   - plain type aliases (`Hash = int`);
   - Nim crashing on a fewer-formals `inc` borrow (find what the walker does and
     make it safe);
   - borrow views beyond `classifyType`/`valueTypeName`;
   - `for x in [a, b]` faults;
   - `mpairs`/`mvalues`;
   - a Table length change during iteration (model it where Nim's behaviour is
     defined; otherwise decline);
   - witnesses for seq elements with a ref part;
   - nested seqs longer than 1024 in a witness.
5. **Compile time.** `tests/tsymex_rfc0005_s8bc_remainder.nim` takes about
   220 s to compile. Split it so each file stays under the 60 s per-backend
   budget including compile on Windows, if compile time dominates there.

## Note for integration
S8bc added `iekSeqNewZero` for `newSeq`. S8bi, running separately, added
`iekSeqNew` for the same family. Do not reconcile them here; the batch-4
integrator will. Do state it in your report.

## Verification
- Run your suite(s), the s8bc suite, every r6_* suite, s8at, s8ar, M1_seq_fixedwidth,
  emit_roundtrip, letaudit, CR2, and the Table/seq suites.
- Run them on Z3 5.1 and 4.13.4, plus one cpp run.
- Push, and report DONE to `worker-reports/s8bl.md`.
