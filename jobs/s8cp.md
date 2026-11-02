# Job: S8cp -- new slice (S8cb's remainder; items 1-4 are soundness or crash)

## Setup
- Branch: create `rfc-0005-s8cp` from the current origin/rfc-0005-soundness-channels when you start, then merge origin/rfc-0005-s8cb at 28ab1a7. Port S8cb's trial-merge conflicts as you meet them.
- Walker number is assigned at integration; use the next free one above 247 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md and worker-reports/s8cb.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cp"
title = "S8cb's remainder: replay footprint gaps, the dropped uncheckedAssign pragma, replay reaching quit, the unexplained rc=139, n42 on cpp, stack size off Linux, declined shapes and magics"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **SOUNDNESS: three replay footprint gaps the scan cannot see.**
   - a compiler-inserted hook, `=destroy` naming a variable;
   - state shared behind two different C routines;
   - a runtime hook variable the program sets.
   Show each one producing a wrong verdict or an unsafe abandoned replay. The fix must fail closed: where the footprint cannot be proved, it is open, so a contended replay gives the unknown verdict rather than a refutation. Scan the types whose hooks are reached. Treat any two foreign routines as sharing state unless they are on a known-pure list. Treat a program-writable hook variable as open.
2. **SOUNDNESS: `{.cast(uncheckedAssign).}: o.k = v` gives a false sxRaised**, because the pragma is dropped. Keep the pragma's meaning through the parser and pin it natively, both for a discriminator change that keeps the same branch and for one that changes it. Model what the compiled program does in each case.
3. **SOUNDNESS: replay of an unmodelled path that calls the real `quit` ends the process.** Replay must survive it and report a declined verdict, or it must run where exit cannot kill the host. Cover `quit` directly, via a callee, via `addExitProc`, and a raw C `exit`. Say which of these cannot be intercepted, and make those decline before replay starts rather than kill the run.
4. **CRASH: the unexplained rc=139 from probe p7** (top-level `let ra = symexFind(...)` plus an unused proc with `=sink`, `=dup` and `quit`). A crash that does not reproduce is still a crash. Rerun at least 200 times, on c and cpp, on the probe's exact commit and on your head, and under valgrind or ASan. Report the cause if found. If it never reappears, report the exact count and tooling, and say that the cause stays unknown. Do not call it fixed.
5. **`tsymex_r6_n42_deref_taint` fails to compile on cpp** (`readCellField` `f = F(i)` on `std::atomic<NI8>`, deleted operator=). S8cl's job takes n43, with the same cause. Check whether S8cl has fixed it. If not, fix the shared cause and tell S8cl. A cpp compile failure counts as red for any file a user can hit it from, so test `readCellField` with an atomic field directly.
6. **Stack size off Linux was only checked with `--compileOnly`.** The C has never been compiled or run on macOS or the BSDs. Compile the generated C against real target headers: `zig cc -target` for macOS and FreeBSD, in podman, and NetBSD or DragonFly if a sysroot exists. Also check whether a toolchain artifact exists for macOS. If one does, run the 16 MiB pin on a GitHub macOS runner, as a job costing under 5 minutes. If not, state plainly in the RFC which platforms are compiled but never run, and make those platforms fall back to the conservative 2 MiB.
7. **Shapes that decline (precision).** Model each:
   - whole-tuple `==` (declines at eqBV);
   - a local `let b = addr o.y` alias on whole assignment;
   - a type section in a routine body;
   - a parameter pragma `x {.inject.}: int`, which is currently a compile error in collectStringBackedByteSeqParamsImpl, so fix that error first;
   - nested `addr t[1][0]`: pin it and claim it, or decline it precisely.
   `s[1].b = 7` and `s[1][0] = x` are S8bz's. Check them once S8bz is available, and take them only if it left them declined.
8. **Declined magics (precision).** Go through S8cb's declined list and model what can be modelled: `math.toInt`, a holey enum's invalid value, `=dup` of an object or tuple through its hook, `$float`, and the remaining `repr` shapes. Stop only where the behaviour cannot be expressed in the theory or the cost is measured as out of budget, and state which one applies, with the number. `<` on pointers, compile-time magics and `finished` keep their existing reasons.

## Verification
- Suites: yours, s8cb_* (all), s8bo_* (all), s10_replay_verdict, s2_replay, n42, n43, n27, s5_str, emit_roundtrip, CR2.
- Run on Z3 5.1, 4.13.4 and cpp. All three Windows legs green.
- Run the whole tree on Linux once before DONE. S8cb's first Windows run failed on four stale pins that its 94-suite list omitted.
- Report DONE to `worker-reports/s8cp.md`, with per-file Windows times.
