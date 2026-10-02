# Job: S8bo -- new slice (S8be's remainder)

- **Branch:** create `rfc-0005-s8bo` from origin/rfc-0005-s8be at ef08ada (walker 205; base S8ax).
- **Provisional walker:** 216.
- **Read first:** WORKER-BRIEF.md and the "As landed (S8be)" notes.

Add this RFC row before the S11 row in your first commit, and flip it to `done` at the end:
```
[[slice]]
id = "S8bo"
title = "S8be's remainder: isNil false UNSAT, plain-object address cells, same-length whole seq assign as resize, escaping arm-field addr, element cells over seqs of objects, abandoned replay threads, threadvar/stack fidelity of threaded replay"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **SOUNDNESS: `r.isNil` gives a false sxUnsat** on a `ref` parameter with `errors` empty, where `r == nil` gives sxSat.
   - Lower the `isNil` magic, for ref, ptr, pointer, cstring, proc and closure, to the nil comparison.
   - Audit the other bodiless system magics on pointer-like values the same way (`isNil` variants, `cast` to pointer, `pointer(x)` comparisons).
   - Add a guard test so an unlowered magic is never silently a constant.
2. **A plain (non-variant) object's address cell is not field-split.** A pointer to one stored in another object clashes, giving `seUnsupportedCompoundSortLeaf`. Field-split it the way S8be did case objects.
3. **A callee assigning a `var seq` whole with the same length term** is not seen as a resize, so its cells stay live. Treat any whole assignment as a resize: Nim reallocates, which is UB for old element pointers. Kill the cells, or decline on a reachable dead deref.
4. **`addr o.a` of an arm field used as an escaping value** still gives `heUnsafeCast`. Model it as the arm-field alias cell, with the arm-change decline.
5. **Element cells cover only seqs of scalars or strings.**
   - Extend them to seqs of objects and tuples. They are on S8bc's leaf-split heap in batch 4, which you do not have.
   - If the leaf split is needed, BLOCKER rather than reimplementing it. In that case, instead implement this on whatever representation the base has, and say what the batch-4 integrator must reconcile.
6. **An abandoned replay thread keeps running** until it ends or the process exits, and it may write a global while later replays run. That can corrupt later replay verdicts.
   - Make later replays sound against it: serialize, fence, or run replays in a subprocess or fresh state.
   - Or mark every replay after an abandoned one as unconfirmed (`roTimedOut`-tainted).
   - Pin a test where an abandoned replay's late global write would otherwise flip a later confirmation.
7. **A replay runs on another thread.** A `{.threadvar.}` starts at its default there, and the stack is 2 MiB. Make replay fidelity match the SUT's real execution context:
   - copy or seed threadvars from the walker's model;
   - size the thread stack to match the main thread, or run replay on the main thread with a watchdog;
   - pin a threadvar-reading SUT so that it confirms correctly.
8. **New suite compile time** is 83 s. Split it so each file stays under 60 s per backend including compile.

## Verification
- **Suites:** run all of these on Z3 5.1 and 4.13.4, plus one cpp run:
  - your suite;
  - s8be;
  - s8ax;
  - s2_replay;
  - s1_lattice;
  - every `symexOpaque|addr |closure|isNil|threadvar` grep hit;
  - CR2;
  - letaudit;
  - n27;
  - N2_kindgate_audit;
  - configdefaults;
  - 163rev_inert_exclusions;
  - s6b_ops.
- **Report:** push the branch and report DONE in `worker-reports/s8bo.md`.
