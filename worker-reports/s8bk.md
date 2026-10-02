# S8bk -- BLOCKER

Branch `rfc-0005-s8bk` (pushed), head 6197636 = base d42204d (origin/rfc-0005-batch3, walker 209) + the RFC row commit (state `pending`). No code changes, no walker bump. Probes (untracked in the worktree, copied for you): `reports-out/s8bk-probes/{native.nim,csrc.nim,tsym.nim}`.

## The wrong assumption
The job says Nim takes the address of a `var`/by-ref actual BEFORE a later argument's call runs, so the write lands in the OLD object, and asks for the fix "snapshot the address at the argument's evaluation point". Native Nim does the opposite. The address is taken AFTER every later argument's call, at the call itself, and the write lands in the NEW object. The only thing done at the argument's own position is an index's bound check. (The job's own probe output, `old.x=0 gP.x=5`, is consistent with this: the write landed in the object `gP` holds after the call.) Implementing the snapshot would make every case below wrong, including the by-reference symbol case that is right today. That is a design-changing spec error, so I stopped.

## Evidence
1. Native, c and cpp identical (`native.nim`; `gP = Box(x: 10)`, `moveP` sets `gP = Box(x: 100)`, `touch(v) = v = v + 5 + k`):
   - `touch(gP.x, moveP())`: `old.x=10 gP.x=105`
   - `touchP(addr gP.x, moveP())`: `old.x=10 gP.x=105`
   - `touch(gO.inner.x, moveInner())`: `old.x=10 gO.inner.x=105`
   - `touch(a[gi], incI())`, array or seq: `[10, 25, 30]`, so the new index is used for both the read and the write.
   - The callee's copy-in sees a write the later call made to the old object (`writeOld` sets `gP.x = 50` and then rebinds): `old.x=50 gP.x=105`.
   - With `gi = 2` and a later call that sets `gi = 3`: there is no IndexDefect. The check ran on the old `gi`, and the access used the new one (out of bounds, UB).
   - A `var` formal forwarded on (`fwd(gP.x)` -> `touch(v, moveP())`): `old.x=15 gP.x=100`. The address was fixed at the outer call, so this is correct both ways.
   - Through a proc variable (`let f = touch`): the same as the direct call, `old.x=10 gP.x=105`.
2. Generated C (`csrc.nim`, nimcache). Nim hoists the later call into a temporary and takes the address inline after it. This is deterministic codegen, not C evaluation order:
   ```
   T1_ = moveP__csrc_u5();
   touch__csrc_u51((&(*gP__csrc_u4).x), T1_);
   if ((NU)(gi__csrc_u55) > (NU)(2)){ raiseIndexError2(gi__csrc_u55, 2); ...
   T2_ = incI__csrc_u56();
   touch__csrc_u51((&a__csrc_u54[(gi__csrc_u55)- 0]), T2_);
   ```
   This is the S8ax rule (`dsl_parser.nim:1600-1623`: an lvalue is an inline C expression, read after every later operand's call, with its checks where it stands) applied to an address.
3. The walker at the base, Z3 5.1 (`tsym.nim`). "nim" is the label Nim reaches; "stale" and "old" are labels Nim cannot reach (old = the write went to the old cell/index):

   | shape | path | nim | stale | old |
   |---|---|---|---|---|
   | `touch(gP.x, moveP())` | heap copy-in/out | sxRaised (unreached) | **sxSat** | sxRaised |
   | `touchG(gP.x, moveP())` (callee reads gP) | S8ba by-ref, symbol base | sxSat | (label not discriminating) | sxRaised |
   | `touchP(addr gP.x, moveP())` | S8an addr cell | sxRaised (unreached) | **sxSat** | sxRaised |
   | `touchPG(addr gP.x, moveP())` | by-ref, ptr | sxSat | (not discriminating) | sxRaised |
   | `touch(a[gi], incI())` (local array) | copy-in/out | sxRaised (unreached) | **sxSat** | sxRaised |
   | `touchG(gA[gi].x, incI())` | S8bd by-ref, element base | sxRaised (unreached) | -- | **sxSat** |

So there is a real SOUNDNESS bug: false sxSat labels, and labels Nim reaches reported unreached. But it runs in the opposite direction from the job:
- Copy-in/out (`dsl_parser.nim:5003`, `var ir = parseExpr(n[i], ...)`) and the addr cell (`:4964`, `let lvIR = parseExpr(addrLv, ...)`) read the value at the argument's position. `orderOperands` leaves them there because they are `fixed` (`:4874`, `:1781`, `:1803`). The write-back (`:5053`, `:4970`) then re-reads the root after the call. The result is a stale copy-in from the old cell or index, written into the new one.
- The S8bd by-ref element base (`:4903`, `:5000`, `parseExpr(b.base, ...)` of `a[i]`) evaluates the index early, at the argument's position. Nim uses the late index.
- The by-ref symbol base (`gP`) is read at the call, late, and is right.

## Best read (the design I would implement if you confirm)
Model the address as taken late, at the call, after every later argument's statements. Keep the address's own checks where the argument stands:
- A fixed (`var`/`addr`) operand's lvalue reads (the copy-in, the addr cell's initial store, the by-ref element/call base) move after the last operand's statements, exactly like S8ax's lazy operands.
- Where a check (an index bound, a variant arm) runs at the argument's position on a value a later call may change, apply S8ax's checked-operand treatment: snapshot what the check reads, then decline `feEvalOrderUnmodelled` on a path where it differs. Nim there accesses out of bounds (UB) or accesses an index it never checked.
- Copy-out keeps writing through the same late address it read. It does so today by re-reading the root after the callee; that is only exact while the callee cannot rebind the root, and that is already guaranteed: a callee that reaches the root goes by reference (`outerReachesCell`).
- A by-ref call base (`getB().x`) is evaluated once. Nim evaluates the call to a temporary where it stands (it is eager), so that one stays at its position.

The pins would be the job's audit list with the corrected truth: the index variable, the field-of-field chain, the forwarded `var` formal (which is already correct), the `addr` actual, and the reference-semantics twins.

## The indirect-call bullet
S8bh (origin/rfc-0005-s8bh, 657f37a) is NOT reachable from the base d42204d. A call through a proc variable drops its `var` writes on this base (S8bf's reported item), so the proc-variable variants cannot be modelled here. Natively, they behave like the direct call (see above).

## Tree state
- `/home/corey/tmp-usage/work/wt/s8bk` at 6197636 (pushed, `-u`). It is clean apart from the untracked `probe_s8bk/`.
- No test file and no walker bump.
- No Windows runs were listed for the branch: the push was a doc-only commit.
