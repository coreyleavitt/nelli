## Phase 15 — Cluster C, cycle C1: closure IR (`iekLambda`/`iekClosureCall`) +
## `svClosure` stub + `sortOfTuple` helper + raw `Z3_mk_app` PoC. PURELY
## STRUCTURAL — the parser recognises an `nnkLambda` / expression-position
## `nnkProcDef` and emits an `iekLambda` (with a free-variable capture list,
## post-monomorphization concrete params), and a call through a proc-valued
## variable as `iekClosureCall`. The walker STUBS both with a deterministic
## classified `ceNotImplemented` (sevError) → `sxUnknown` (Invariant 3 — never
## a silent UNSAT, never a crash). Closure SEMANTICS land C2a (construction) /
## C2b (application). See `docs/symex/ADR-0009-closure-encoding.md`.
##
## C1 is ADDITIVE under walker version "8" (no bump; Cluster C bumps at C6).
import std/[unittest, macros, strutils]
import nelli/smt/types
import nelli/smt/dsl_parser
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/symex

# --- SUTs ------------------------------------------------------------------

# A SUT that constructs and applies a lambda capturing an outer local. The
# walker must STUB this (ceNotImplemented) — no closure semantics in C1.
proc lambdaSut(x: int): int =
  let offset = x * 2
  let f = proc(y: int): int = y + offset
  result = f(3)
  symexTarget("after")

suite "symex Phase 15 C1 — closure IR (iekLambda/iekClosureCall) + svClosure stub":

  test "C1: iekLambda hand-constructed node round-trips through canonicalize (stable key)":
    # One capture ("offset"), one param ("y": int). lambdaBody returns y + offset.
    let body = mkReturnVal(mkBinop(bAdd, mkVar("y"), mkVar("offset")))
    let lam = mkLambda(siteHash = 12345'i64, declOrder = 0,
                       params = @[IRParam(name: "y", ty: tInt(64, true))],
                       body = body,
                       captures = @["offset"],
                       retTy = tInt(64, true))
    let k1 = canonicalize(lam)
    let k2 = canonicalize(lam)
    check k1 == k2                       # stable
    check k1.contains("Lam")             # tagged as a lambda
    check k1.contains("12345")           # site hash in the key
    check k1.contains("offset")          # capture name in the key

  test "C1: iekClosureCall key is DISTINCT from a plain isCall to the same target":
    let cc = mkClosureCall("f", @[mkIntLit(3)])
    let ccKey = canonicalize(cc)
    check ccKey.contains("CC")
    check ccKey.contains("f")
    # A plain user-proc call to the same name "f": A-normalised isCall.
    let plain = mkCall("f", "ret0", @[mkIntLit(3)], tInt(64, true))
    let plainKey = canonicalize(plain)
    check ccKey != plainKey              # closure-call vs named-call: distinct

  test "C1: same lambda site at T=int vs T=string ⇒ DISTINCT canonical keys (monomorphization, D8)":
    let body = mkReturnVal(mkVar("y"))
    let lamInt = mkLambda(siteHash = 999'i64, declOrder = 0,
                          params = @[IRParam(name: "y", ty: tInt(64, true))],
                          body = body, captures = @[], retTy = tInt(64, true))
    let lamStr = mkLambda(siteHash = 999'i64, declOrder = 0,
                          params = @[IRParam(name: "y", ty: tString())],
                          body = body, captures = @[], retTy = tString())
    check canonicalize(lamInt) != canonicalize(lamStr)

  test "C1: render of iekLambda / iekClosureCall is canonical (compiles through render dispatch)":
    let lam = mkLambda(1'i64, 0, @[IRParam(name: "y", ty: tInt(64, true))],
                       mkReturnVal(mkVar("y")), @["offset"], tInt(64, true))
    check render(lam).contains("lambda")
    let cc = mkClosureCall("f", @[mkIntLit(3)])
    check render(cc).contains("f")

  test "C2b: a constructed-and-applied lambda SUT now symexes (closure call modeled)":
    # C1 STUBBED this (`ceNotImplemented` → sxUnknown). C2b implements the
    # closure CALL (`f(3)` descends the lambda body with the ground per-call
    # axiom), so the unconditionally-reached `symexTarget("after")` is now SAT —
    # no longer a classified stub. (Behaviour superseded by C2b; the structural
    # IR/canonicalize/PoC assertions in this file are unchanged.)
    let res = symexFind(lambdaSut, tLabel("after"))
    check res.status == sxSat

  test "C1 PoC: Z3_mk_app with runtime-constructed sorts (Feas-H2; de-risks C2b)":
    # Declare an uninterpreted func decl over sorts derived from an svTuple env
    # via `sortOfTuple`, apply it via raw Z3_mk_app, and assert Z3 accepts the
    # application (round-trips) without a sort-mismatch crash.
    check c1ClosurePoCApply()

# --- Free-variable capture enumeration (parser) ----------------------------
# A lambda capturing an OUTER local (`outer`) but NOT an inner local (`inner`)
# declared inside the lambda body: only `outer` must appear in lambdaCaptures.
proc captureSut(a: int): int =
  let outer = a + 1
  let f = proc(y: int): int =
    let inner = y * 2
    inner + outer
  result = f(5)

macro lambdaCapturesOf(p: typed): untyped =
  let impl = p.getImpl
  let parsed = parseProc(impl)
  # Walk the parsed body for the iekLambda and surface its captures as a literal.
  var caps: seq[string]
  proc walk(s: IRStmt) =
    if s == nil: return
    case s.kind
    of isBlock:
      for c in s.stmts: walk(c)
    of isLet:
      if s.lvalue != nil and s.lvalue.kind == iekLambda:
        caps = s.lvalue.lambdaCaptures
    else: discard
  walk(parsed.body)
  var lit = newTree(nnkBracket)
  for c in caps: lit.add newLit(c)
  # Explicitly typed seq[string] so an empty capture list still infers.
  newCall(newTree(nnkBracketExpr, ident"seq", ident"string"), prefix(lit, "@"))

suite "symex Phase 15 C1 — free-variable capture enumeration":
  test "C1: lambda captures the OUTER local, NOT the body-local inner":
    let caps = lambdaCapturesOf(captureSut)
    check "outer" in caps
    check "inner" notin caps
    check "y" notin caps                 # a param is not a capture
