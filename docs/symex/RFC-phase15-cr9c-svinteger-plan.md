# CR-9(c) integer-representation unification — Option 2 (chosen)

Decision (Corey-confirmed): do NOT collapse to an erased `svInteger`. Keep the typed `svInt`/`svBV8/16/32/64` variants (they give nim-z3 compile-time `Z3BitVec[N]` width safety — the exact safety that caught the F5-hang and probeProto bugs). Instead: move `signed` into the BV variants (fixes CR-9(a) phantom field) and add boundary helpers so NO caller branches on int width or rep-family. Same ergonomic goal as "the svInteger split", without erasing typing.

Rules: build/test ONLY via `scripts/dt-bounded.sh <c|cpp> <test> [secs]` + `scripts/parity-check.sh`; both backends green per commit; commits on main; NO `symexWalkerVersion`/`renderAsChoicesVersion` bump on ANY stage (pure encapsulation → byte-identical Z3 terms; a verdict flip = bug to fix, not a bump). 137 = Z3-hang regression. Copy replaced branch bodies BYTE-FOR-BYTE into helpers (same op-pair order e.g. bvslt,bvult; same signed/unsigned selection) so emitted terms are identical.

DO NOT TOUCH (load-bearing F5 fixes, already construct typed svBV32/svBV64): `probeProto` (runtime.nim ~1544-1649), `iekConvFloatToInt` + `toBv64ForFp` (runtime_floats.nim ~40-233). Option 2 needs no change there — note this in commit messages so nobody "unifies" them later.

Canary set (run F5 pair under dt-bounded so a hang = 137, both backends): F5_probeproto, F5hang_derefwrite, CR3_CR4_CR6_float, rereview_drains, CR1_CR5_closure_heap, + a width-mix arith/cmp test.

## Stages
- **A — move `signed` into the 4 BV variant cases** (fixes CR-9(a)): delete outer `signed: bool` (runtime.nim ~209), add `signed` to `of svBV8/16/32/64`. Compiler-driven: `nim c` errors at every `.signed` read not under a BV-kind guard (all ~42 sites already BV-guarded; grep-confirmed no phantom non-BV `signed:` constructions). Touch runtime.nim + runtime_heap.nim + runtime_floats.nim. Gate: full canary set both backends. NO bump.
- **B — add `reconcileInt(a,b): (SymVal,SymVal)`** near reconcileFloat (~2078): if kinds differ and both in {svInt,svBV8/16/32/64} → both as svInt via toZ3Int; else identity. Additive, no call-site change. NO bump.
- **C — add `lowerArith(a,b,op): SymVal` and `lowerCmp(a,b,op): SymVal`**: lift the EXACT existing branch bodies. lowerArith: svInt→arithInt / float→arithFloat / else bAdd→binBV(+),bSub→binBV(-),bMul→binBV(*),bDiv→divBV,bMod→modBV. lowerCmp: svInt→cmpInt / bool→bool-eq / float→cmpFloat / string→cmpString / else bEq→eqBV,bNe→neBV,bLt→cmpBV(bvslt,bvult),... ; call reconcileInt at top. Additive. Visually diff bodies vs source before commit. NO bump.
- **D — migrate call sites, one arm-group per commit:**
  - D1 arithmetic arm (~2682-2697) → lowerArith. Gate: arith + rereview_drains.
  - D2 comparison probe-hit (~2587-2619) → reconcileInt+lowerCmp; keep closureEq/refEq short-circuits BEFORE the call. **HIGHEST DANGER (F5/probeProto epicenter)** — gate F5_probeproto + F5hang_derefwrite (BOUNDED) + width-mix cmp, both backends; verify int(f)-vs-literal ordering/equality/arith for int32 AND int64.
  - D3 comparison probe-miss (~2620-2645) → lowerCmp (reconcileInt is identity no-op when kinds match — safe). Gate F5_probeproto, rereview_drains.
  - D4 iekBorrowOp arm (~2698-2749) → lowerCmp + lowerArith, preserve ejectBase + reboxDistinct wrap. Gate G4/G5 + canaries.
  - D5 cross-rep return linkage (~5060-5067) + seq-index coercion (~4581) → reconcileInt where it applies (keep toZ3Int in the index proto path). Gate CR1_CR5, rereview_drains.
- **E (optional)** — grep residual `l.kind==svInt`/{svInt,svBV*} ladders; migrate or document. Gate full canary set. NO bump.

Outcome: phantom `signed` gone (a); zero walk arms branch on int width or rep-family (c); typed variants + compile-time width safety + the two load-bearing doAsserts RETAINED.
