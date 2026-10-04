# Job: S8ce -- new slice, SOUNDNESS, cross-repo (S8bx's remainder)

**PRIORITY: runs next, ahead of S8bz/S8cb/S8cd.**

**MODEL: use opus for this job's agent.** It is one of the hardest slices in the RFC.

## Setup
- Branch: create `rfc-0005-s8ce` from origin/rfc-0005-s8bx at de6c67f (walker 228; base 1f38a13, which is in the landed batch 6).
- Provisional walker: **238**.
- Read these first: WORKER-BRIEF.md, WORKER-LOCAL.md, worker-reports/s8bx.md, and S8bx's "As landed" notes.
- In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8ce"
title = "Destructor-swallowed exceptions: nim-z3's lifecycle hooks catch an in-flight raise on the C backend; root fix in nim-z3, lock bump, every destroy site covered"
state = "pending"
```
- Flip the row to `done` at the end.

## The defect (from S8bx)
On Nim 2.2.10's C backend (goto exceptions), a call's result temporary is destroyed on the raise path while the error flag is still set. nim-z3's hooks wrap their bodies in `try/except CatchableError: discard`, and also `except Exception`. A `try` inside a destructor running during unwinding catches the IN-FLIGHT exception and clears it. The walk then continues as if nothing had raised, giving a false sxUnsat or sxSat. cpp is unaffected.

S8bx closed this for extraction raises only, with a hook. About 290 other destroy sites in the generated C can lose an exception the same way.

## Scope (do all of it; defer nothing; pin each item RED first)

### 1. Prove the mechanism
Write a minimal RED reproduction in nelli's tests, on the C backend:
- a nim-z3 value temporary is destroyed while an exception from the same expression propagates;
- assert that the exception reaches an outer `except`.

It must be RED at your base on c and green on cpp. Also look at the generated C so the report can cite exactly where the error flag gets cleared.

### 2. Root fix in nim-z3
Repo: `github.com/coreyleavitt/nim-z3`. Base is origin/main **ae509f0**, the commit nelli's milpa.lock pins. Create branch **`rfc-0005-s8ce`** there; pushing that branch is authorised. Never push nim-z3 main.

- Remove every `try`/`except` from destructor and copy/dup hook bodies:
  - `termDestroy` in `src/z3/lifecycle.nim` (lines 106-125);
  - `emitRefcountLifecycle` / `emitTermLifecycle`;
  - `context.nim` near 106-134;
  - `quantifier.nim` near 63;
  - `datatypes.nim` near 162/170/190;
  - and any other hook (`command grep -n 'except' src`).
- Make the bodies raise-free by construction:
  - call the raw C `dec_ref` / `inc_ref` directly, never through anything that can raise (no `checkErr`, no error-handler dispatch);
  - check `isNil` up front;
  - keep `{.raises: [].}` so the compiler proves it.
- If a hook genuinely needs an operation that can raise, restructure it so the operation cannot raise, or move it out of the hook. Do NOT swallow.
- Add a nim-z3 regression test for the raise-path temporary.
- Run nim-z3's own test suite, through podman.
- If the Nim compiler's codegen is itself at fault, also reduce it to a minimal pure-Nim reproduction (no Z3) and include it in the report. Still do the nim-z3 fix, since it removes the swallowing.

### 3. Lock bump in nelli
- Point milpa.lock's z3 entry at the `rfc-0005-s8ce` commit, using the same lock shape as S8at's bump.
- Do a fresh fetch, and verify `_deps/z3` resolves to the new identity in a fresh worktree.
- The coordinator fast-forwards nim-z3 main to your branch at integration. Note in the report the exact nim-z3 sha to fast-forward.

### 4. Nelli-side sites
- Audit nelli's own `=destroy` / `=copy` / `=sink` / `=dup` hooks, and any `try` inside them (`command grep -rn '=destroy\|=copy\|=dup\|=sink' src`), for the same pattern. Fix them all the same way.
- Decide whether S8bx's extraction hook is still needed once the root fix is in:
  - if it is now redundant, remove it (no dormant substrate) and keep its pins green;
  - if it still matters, say why.

### 5. Cover the ~290 sites by class, not one by one
- Write tests that hit each distinct shape of raise-during-temporary-destroy that the walker produces:
  - extraction;
  - solver calls;
  - model eval;
  - term construction inside a raising expression;
  - and any other shapes.
- Show each one RED at base, then green.

## Verification
- Run: your suites, s8bx's suites, CR2, configdefaults, and every suite touching `checkErr` / model eval.
- Then the full `tsymex_*` set on c, on Z3 5.1 and 4.13.4 (sliced as you like, but cover all of it), because this changes behaviour on every destroy path.
- cpp: run the new suites and s8bx's.
- Windows: all three legs must be green. symex-mingw is the C backend with mingw, so it is the important one.
- Report DONE to `worker-reports/s8ce.md`. Include the nim-z3 sha, the lock identity, and the generated-C citation.
