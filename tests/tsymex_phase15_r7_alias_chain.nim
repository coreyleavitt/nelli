## Phase 15 — Cluster R (FINAL cluster), cycle R7: ref equality + alias chain.
##
## R7 is mostly CONFIRMATION that the env binding ALREADY shares the underlying
## `Ref_T` Z3 const for a ref-typed RHS. `let q = p` lowers to
## `mkLet("q", itRef(T), mkVar("p"))`; the walker's `of isLet:` arm does
## `newEnv["q"] = lower(env, mkVar("p")) = env["p"]` — and `SymVal` is a Nim
## VALUE type, so the copy SHARES the underlying `Z3AnyAst` (the `refAst`). So
## `q` and `p` are structurally the SAME svRef:
##   * `p == q` is a Z3 tautology (`refEq` over identical terms) — no `check-sat`,
##   * a write through `q` (`q[] = v` → store at the shared refAst) is observed
##     through `p` (same heap index), and
##   * alias CHAINS `p == q == r` (two sequential lets) need NO extra axioms —
##     transitivity is the IDENTITY of the same Z3 const (each let copies the
##     same SymVal forward).
##
## Reassignment BREAKS the alias. `q = r` is an `isAssign` (variable REBIND, NOT
## a heap write — distinct from `q[] = v` which IS a store), so the walker does
## `newEnv["q"] = lower(env, mkVar("r")) = env["r"]` — `q` now holds r's refAst,
## NOT p's. After `q = r` a write through `q` lands on r's address and is NOT
## forced to be observed through p (p and r are distinct params — independent
## `Ref_T` consts, free to differ).
##
## DoD (RFC §R7 + reconciliation §F-R):
##   1. Transitive alias: `let q = p; let r = q; r[] = 5; p[] == 5` → sxSat
##      (write through r visible through p — all three share the refAst).
##   2. Reassignment breaks alias: `var q = p; q = r; q[] = 9` — the write
##      through q (now aliasing r) does NOT force p[]==9; PROVED by showing
##      `p[] != 9` is still SATISFIABLE after the write (if the alias had NOT
##      broken, the write through a still-p-aliased q would force p[]==9, making
##      `p[] != 9` UNSAT).
##   3. Ref equality: `let q = p; if p == q` → sxSat (p==q is a tautology);
##      `let q = p; if p != q` → sxUnsat (p and q are the same const).
##
## See ADR-0010 (logical-heap model) and RFC §R7. R7 is ADDITIVE under walker
## version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

# --- DoD 1: transitive alias chain p == q == r --------------------------------
# `let q = p; let r = q` makes all three names hold the SAME Ref_T const. A write
# through r stores at that shared address; a read through p selects the same
# index → sees 5. (Per RFC §R7's literal SUT.)
proc transitive(p: ref int) =
  let q = p
  let r = q
  r[] = 5
  if p[] == 5:
    symexTarget("transitive")

# Reverse-order confirmation (DoD bullet 4 — heap-threading ordered correctly):
# write through r, then read r[] back — sees the overwrite.
proc transitiveReadBack(p: ref int) =
  let q = p
  let r = q
  r[] = 5
  if r[] == 5:
    symexTarget("readback")

# Transitive CONTRADICTION: the chain pins p[] to 5, so reading 6 through p is
# impossible — PROVES the write through r really reaches p (not a free heap).
proc transitiveContradiction(p: ref int) =
  let q = p
  let r = q
  r[] = 5
  if p[] == 6:
    symexTarget("nope")

# --- DoD 2: reassignment breaks the alias -------------------------------------
# `var q = p` aliases p; `q = r` REBINDS q to r (a variable rebind via isAssign,
# NOT a heap write). After the rebind a write `q[] = 9` lands on r's address.
# Because p and r are DISTINCT params (independent Ref_T consts, free to differ),
# the write does NOT force p[]==9 — so `p[] != 9` remains SATISFIABLE. Had the
# alias NOT broken (q still == p), the write through q would force p[]==9 and
# this `p[] != 9` target would be UNSAT. The sxSat verdict PROVES the rebind
# broke the alias.
proc reassignBreaksAlias(p: ref int, r: ref int) =
  var q = p
  q = r              # variable REBIND — q now aliases r, not p
  q[] = 9            # store lands on r's address
  if p[] != 9:       # still satisfiable iff p is NOT forced to alias r
    symexTarget("broke")

# Control: BEFORE the reassignment, q still aliases p. A write through q while it
# still aliases p forces p[]==9, so `p[] != 9` is UNSAT — confirming the alias
# was genuinely live before `q = r` (so the break in `reassignBreaksAlias` is
# real, not an artifact of q never having aliased p).
proc beforeReassignAliasLive(p: ref int, r: ref int) =
  var q = p
  q[] = 9            # q still aliases p → store lands on p's address
  if p[] != 9:       # forced false: p[] is pinned to 9
    symexTarget("impossible")

# After `q = r`, a read through q sees the write through q (q aliases r, write
# landed on r, read of q reads r) — read-back through the rebound name.
proc reassignReadBack(p: ref int, r: ref int) =
  var q = p
  q = r
  q[] = 9
  if q[] == 9:       # q aliases r; the store through q is read back through q
    symexTarget("qreadback")

# --- DoD 3: ref equality from a let-alias -------------------------------------
# `let q = p` makes q the SAME const as p, so `p == q` is a Z3 tautology → the
# gated target is reachable (sxSat); `p != q` is unsatisfiable (sxUnsat).
proc refEqTrue(p: ref int) =
  let q = p
  if p == q:
    symexTarget("eq")

proc refNeqFalse(p: ref int) =
  let q = p
  if p != q:
    symexTarget("neq")

# Two DISTINCT params are NOT axiomatically equal: `p == r` is sat (they MAY
# alias) and `p != r` is sat (they MAY differ) — both reachable.
proc distinctRefsMayDiffer(p: ref int, r: ref int) =
  if p != r:
    symexTarget("maydiffer")

suite "symex Phase 15 R7 — ref equality + alias chain (let-alias + reassignment)":

  test "R7: alias chain p == q == r consistent under sat":
    # RFC §R7 named test: write through r visible through p (all three share the
    # refAst via sequential let-aliasing).
    let res = symexFind(transitive, tLabel("transitive"))
    check res.status == sxSat

  test "R7 test 1b: read-back through r after r[]=5 sees the overwrite → sxSat":
    let res = symexFind(transitiveReadBack, tLabel("readback"))
    check res.status == sxSat

  test "R7 test 1c: chain pins p[]=5, so p[]==6 through p is sxUnsat (write reaches p)":
    let res = symexFind(transitiveContradiction, tLabel("nope"))
    check res.status == sxUnsat

  test "R7 test 2a: reassignment q=r breaks alias — p[]!=9 still sat after q[]=9 → sxSat":
    let res = symexFind(reassignBreaksAlias, tLabel("broke"))
    check res.status == sxSat

  test "R7 test 2b: control — before reassignment q aliases p, so p[]!=9 after q[]=9 is sxUnsat":
    let res = symexFind(beforeReassignAliasLive, tLabel("impossible"))
    check res.status == sxUnsat

  test "R7 test 2c: after q=r, read-back q[]==9 through the rebound name → sxSat":
    let res = symexFind(reassignReadBack, tLabel("qreadback"))
    check res.status == sxSat

  test "R7 test 3a: let-alias q=p makes p==q a tautology → sxSat":
    let res = symexFind(refEqTrue, tLabel("eq"))
    check res.status == sxSat

  test "R7 test 3b: let-alias q=p makes p!=q unsatisfiable → sxUnsat":
    let res = symexFind(refNeqFalse, tLabel("neq"))
    check res.status == sxUnsat

  test "R7 test 3c: two distinct params may differ — p!=r is sat → sxSat":
    let res = symexFind(distinctRefsMayDiffer, tLabel("maydiffer"))
    check res.status == sxSat
