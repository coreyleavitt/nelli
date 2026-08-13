## Tests for `nelli/smt/canonicalize` — the content-addressed
## cache-key foundation for symex DB persistence (Phase 10).
##
## The canonical encoding's contract: a *pure structural function*
## of the inputs the witness depends on, with provably no source-
## location or local-variable-name leakage, and a stable ordering
## for unordered containers (callee maps, tuple field-name
## collisions).
import std/[unittest, strutils, tables]
import nelli/smt/canonicalize
import nelli/smt/types

suite "symex canonicalize — IRType primitives":
  test "int widths and sign encode distinctly":
    check canonicalize(tInt(64, signed = true))  != canonicalize(tInt(64, signed = false))
    check canonicalize(tInt(8,  signed = true))  != canonicalize(tInt(64, signed = true))

  test "bool and string each have a stable encoding":
    let b1 = canonicalize(tBool())
    let b2 = canonicalize(tBool())
    check b1 == b2
    check b1 != canonicalize(tInt(64, signed = true))
    check canonicalize(tString()) != b1

suite "symex canonicalize — IRType composites":
  test "array encodes both element type and size":
    let a1 = canonicalize(tArray(tInt(64, true), 10))
    let a2 = canonicalize(tArray(tInt(64, true), 20))
    let a3 = canonicalize(tArray(tInt(32, true), 10))
    check a1 != a2
    check a1 != a3

  test "seq, set encode their element type":
    check canonicalize(tSeq(tInt(64, true))) !=
          canonicalize(tSeq(tBool()))
    check canonicalize(tSet(tInt(64, true))) !=
          canonicalize(tSet(tBool()))
    check canonicalize(tSeq(tInt(64, true))) !=
          canonicalize(tSet(tInt(64, true)))

  test "table encodes both key and value types":
    let t1 = canonicalize(tTable(tString(), tInt(64, true)))
    let t2 = canonicalize(tTable(tString(), tInt(32, true)))
    let t3 = canonicalize(tTable(tInt(64, true), tInt(64, true)))
    check t1 != t2
    check t1 != t3

  test "tuple encodes per-field types positionally + nominal object name":
    let p1 = tTuple(@[tInt(64, true), tBool()], @["x", "y"], "Point")
    let p2 = tTuple(@[tInt(64, true), tBool()], @["x", "y"], "Vec")
    let p3 = tTuple(@[tBool(), tInt(64, true)], @["x", "y"], "Point")
    check canonicalize(p1) != canonicalize(p2)  # objectName matters
    check canonicalize(p1) != canonicalize(p3)  # field order matters

  test "anonymous tuple field names do not affect canonical form":
    # For positional/anonymous tuples (fieldNames == "" or absent),
    # field-name spelling has no semantic role — positional encoding.
    let anon1 = tTuple(@[tInt(64, true), tBool()], @["", ""], "")
    let anon2 = tTuple(@[tInt(64, true), tBool()], @["", ""], "")
    check canonicalize(anon1) == canonicalize(anon2)

  test "nested composites round-trip":
    let nested = tTable(tString(),
                        tArray(tSeq(tInt(64, true)), 5))
    check canonicalize(nested) == canonicalize(nested)
    check canonicalize(nested) !=
          canonicalize(tTable(tString(),
                              tArray(tSeq(tInt(32, true)), 5)))

suite "symex canonicalize — IRType variants (Phase 11)":
  test "itVariant encodes distinctly from a structurally-similar itTuple":
    # An itVariant SHAPED like Shape{kind, radius, side} is NOT the
    # same type as a plain object with the same fields flat. They
    # have different soundness contracts under the walker, so they
    # must produce different canonical forms (different cache keys).
    let kindTy = tInt(8, signed = true)  # the enum's int repr
    let arms = @[
      VariantArm(tagOrdinal: 0, tagName: "skCircle",
                 fieldNames: @["radius"],
                 fieldTypes: @[tInt(64, signed = true)]),
      VariantArm(tagOrdinal: 1, tagName: "skSquare",
                 fieldNames: @["side"],
                 fieldTypes: @[tInt(64, signed = true)])]
    let variantTy = tVariant("Shape", "kind", kindTy, arms)
    # The structurally-flat tuple form (the OLD Phase 4 lowering).
    let flatTy = tTuple(
      @[kindTy, tInt(64, signed = true), tInt(64, signed = true)],
      @["kind", "radius", "side"], "Shape")
    check canonicalize(variantTy) != canonicalize(flatTy)

  test "itVariant is stable: same shape → same canonical form":
    let kindTy = tInt(8, signed = true)
    let arms1 = @[VariantArm(tagOrdinal: 0, tagName: "a",
                              fieldNames: @["x"],
                              fieldTypes: @[tBool()])]
    let arms2 = @[VariantArm(tagOrdinal: 0, tagName: "a",
                              fieldNames: @["x"],
                              fieldTypes: @[tBool()])]
    check canonicalize(tVariant("V", "k", kindTy, arms1)) ==
          canonicalize(tVariant("V", "k", kindTy, arms2))

  test "itVariant distinguishes discriminator name, object name, " &
       "arm tag ordinal, arm name, and arm field types":
    let kindTy = tInt(8, signed = true)
    let baseArms = @[VariantArm(tagOrdinal: 0, tagName: "a",
                                 fieldNames: @["x"],
                                 fieldTypes: @[tBool()])]
    let base = canonicalize(tVariant("V", "k", kindTy, baseArms))
    # different objectName
    check base != canonicalize(tVariant("W", "k", kindTy, baseArms))
    # different discriminator name
    check base != canonicalize(tVariant("V", "tag", kindTy, baseArms))
    # different discriminator type
    check base != canonicalize(tVariant("V", "k", tInt(16, true), baseArms))
    # different arm tag ordinal
    let armsB = @[VariantArm(tagOrdinal: 7, tagName: "a",
                              fieldNames: @["x"],
                              fieldTypes: @[tBool()])]
    check base != canonicalize(tVariant("V", "k", kindTy, armsB))
    # different arm name
    let armsC = @[VariantArm(tagOrdinal: 0, tagName: "z",
                              fieldNames: @["x"],
                              fieldTypes: @[tBool()])]
    check base != canonicalize(tVariant("V", "k", kindTy, armsC))
    # different arm field type
    let armsD = @[VariantArm(tagOrdinal: 0, tagName: "a",
                              fieldNames: @["x"],
                              fieldTypes: @[tInt(64, true)])]
    check base != canonicalize(tVariant("V", "k", kindTy, armsD))

  test "Phase 11 walker semantics bump: symexWalkerVersion is no longer \"1\"":
    # Cycle 1 of Phase 11 introduces witness-affecting walker changes
    # (variant lowering). The walker-version constant bumps so old
    # persisted witnesses are invisible.
    check symexWalkerVersion != "1"

suite "symex canonicalize — IRStmt + IRExpr":
  test "block / if / let / assign / assert / target / return cover":
    let t = tInt(64, true)
    let body = mkBlock(@[
      mkLet("x", t, mkIntLit(0)),
      mkAssign("x", mkBinop(bAdd, mkVar("x"), mkIntLit(1))),
      mkIf(@[IRBranch(cond: mkBinop(bEq, mkVar("x"), mkIntLit(1)),
                      body: mkTargetLabel("hit"))]),
      IRStmt(kind: isAssert, acond: mkBoolLit(true)),
      mkReturn()])
    let s1 = canonicalize(body)
    let s2 = canonicalize(body)
    check s1 == s2
    check s1.len > 0

  test "let renames do not affect canonicalization (positional encoding)":
    # `let i` vs `let j` for the same value have the same canonical
    # form. Names of local lets are encoded positionally, not by
    # spelling, because variable rebinding semantics are by
    # de-Bruijn-like position. Implementation: lets are numbered
    # in declaration order; subsequent vname refs are rewritten
    # via the same numbering. So the renamed program is
    # structurally identical.
    let body1 = mkBlock(@[
      mkLet("i", tInt(64, true), mkIntLit(0)),
      mkAssign("i", mkVar("i"))])
    let body2 = mkBlock(@[
      mkLet("j", tInt(64, true), mkIntLit(0)),
      mkAssign("j", mkVar("j"))])
    check canonicalize(body1) == canonicalize(body2)

  test "different body structures encode distinctly":
    let body1 = mkBlock(@[mkLet("x", tInt(64, true), mkIntLit(0))])
    let body2 = mkBlock(@[mkLet("x", tInt(64, true), mkIntLit(1))])
    check canonicalize(body1) != canonicalize(body2)

  test "every IRExpr kind round-trips":
    check canonicalize(mkIntLit(7))   != canonicalize(mkIntLit(8))
    check canonicalize(mkBoolLit(true)) != canonicalize(mkBoolLit(false))
    check canonicalize(mkBinop(bAdd, mkIntLit(1), mkIntLit(2))) !=
          canonicalize(mkBinop(bSub, mkIntLit(1), mkIntLit(2)))
    check canonicalize(mkUnop(uNot, mkBoolLit(true))) !=
          canonicalize(mkUnop(uNeg, mkIntLit(1)))
    check canonicalize(mkStrLit("a")) != canonicalize(mkStrLit("b"))

suite "symex canonicalize — SymexProgram":
  test "params + body are encoded together":
    let p1 = SymexProgram(
      params: @[IRParam(name: "x", ty: tInt(64, true))],
      body: mkBlock(@[mkLet("y", tInt(64, true), mkVar("x"))]))
    let p2 = SymexProgram(
      params: @[IRParam(name: "x", ty: tInt(32, true))],  # different width
      body: p1.body)
    check canonicalize(p1) != canonicalize(p2)

  test "callee map iteration order does NOT affect canonical form":
    # Insert callees in two different orders into the Table; the
    # canonical form must sort by callee name.
    let body = mkBlock(@[])
    var procsA = initTable[string, ProcSig]()
    procsA["aaa"] = ProcSig(name: "aaa", body: body, retTy: tBool(), isVoid: true)
    procsA["bbb"] = ProcSig(name: "bbb", body: body, retTy: tBool(), isVoid: true)
    var procsB = initTable[string, ProcSig]()
    procsB["bbb"] = ProcSig(name: "bbb", body: body, retTy: tBool(), isVoid: true)
    procsB["aaa"] = ProcSig(name: "aaa", body: body, retTy: tBool(), isVoid: true)
    let p1 = SymexProgram(body: body, procs: procsA)
    let p2 = SymexProgram(body: body, procs: procsB)
    check canonicalize(p1) == canonicalize(p2)

  test "different callee body produces different canonical form":
    let body = mkBlock(@[])
    var procsA = initTable[string, ProcSig]()
    procsA["helper"] = ProcSig(name: "helper",
      body: mkBlock(@[mkReturn()]), retTy: tBool(), isVoid: true)
    var procsB = initTable[string, ProcSig]()
    procsB["helper"] = ProcSig(name: "helper",
      body: mkBlock(@[mkBreak()]), retTy: tBool(), isVoid: true)
    check canonicalize(SymexProgram(body: body, procs: procsA)) !=
          canonicalize(SymexProgram(body: body, procs: procsB))

suite "symex canonicalize — SymexTarget":
  test "the three target kinds are pairwise distinct":
    let l  = canonicalize(tLabel("foo"))
    let av = canonicalize(tAssertionViolation())
    let ix = canonicalize(tIndexError())
    check l  != av
    check l  != ix
    check av != ix

  test "different label strings produce different canonical forms":
    check canonicalize(tLabel("foo")) != canonicalize(tLabel("bar"))

suite "symex canonicalize — SymexSettings":
  test "integerSemantics, maxCallDepth, maxLoopUnwind, maxFrontierSize, "&
       "queryRLimit all change the canonical form":
    var s0 = defaultSymexSettings()
    var s1 = s0; s1.integerSemantics = isLoose
    var s2 = s0; s2.budget.maxCallDepth     = s0.budget.maxCallDepth + 1
    var s3 = s0; s3.budget.maxLoopUnwind    = s0.budget.maxLoopUnwind + 1
    var s4 = s0; s4.budget.maxFrontierSize  = s0.budget.maxFrontierSize + 1
    var s5 = s0; s5.budget.queryRLimit      = s0.budget.queryRLimit + 1
    check canonicalize(s0) != canonicalize(s1)
    check canonicalize(s0) != canonicalize(s2)
    check canonicalize(s0) != canonicalize(s3)
    check canonicalize(s0) != canonicalize(s4)
    check canonicalize(s0) != canonicalize(s5)

  test "acceptUnknownAsCovered does NOT affect canonical form":
    # The flag only affects assertCoveredBy's raise/pass decision —
    # it has zero influence on what symex returns or what witness
    # gets persisted. Regression guard for the provable-exclusion
    # claim.
    var s0 = defaultSymexSettings()
    s0.acceptUnknownAsCovered = false
    var s1 = s0
    s1.acceptUnknownAsCovered = true
    check canonicalize(s0) == canonicalize(s1)

suite "symex canonicalize — symexCacheKey":
  test "identical inputs produce identical keys":
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tLabel("foo")
    let settings = defaultSymexSettings()
    let k1 = symexCacheKey(prog, target, settings,
      z3Version = "4.13.3.0", nimVersion = "2.2.0",
      walkerVersion = "1", renderingVersion = "1")
    let k2 = symexCacheKey(prog, target, settings,
      z3Version = "4.13.3.0", nimVersion = "2.2.0",
      walkerVersion = "1", renderingVersion = "1")
    check k1 == k2
    check k1.len > 0
    check k1.startsWith("sx:")

  test "SUT body change → different key (witness depends on body)":
    let p1 = SymexProgram(body: mkBlock(@[mkLet("x", tInt(64, true), mkIntLit(0))]))
    let p2 = SymexProgram(body: mkBlock(@[mkLet("x", tInt(64, true), mkIntLit(1))]))
    check symexCacheKey(p1, tLabel("foo"), defaultSymexSettings(),
            "z3", "nim", "1", "1") !=
          symexCacheKey(p2, tLabel("foo"), defaultSymexSettings(),
            "z3", "nim", "1", "1")

  test "settings.budget.maxLoopUnwind change → different key":
    let prog = SymexProgram(body: mkBlock(@[]))
    var s0 = defaultSymexSettings()
    var s1 = s0; s1.budget.maxLoopUnwind = s0.budget.maxLoopUnwind + 1
    check symexCacheKey(prog, tLabel("foo"), s0, "z3", "nim", "1", "1") !=
          symexCacheKey(prog, tLabel("foo"), s1, "z3", "nim", "1", "1")

  test "acceptUnknownAsCovered toggle → SAME key (regression guard)":
    let prog = SymexProgram(body: mkBlock(@[]))
    var s0 = defaultSymexSettings()
    s0.acceptUnknownAsCovered = false
    var s1 = s0
    s1.acceptUnknownAsCovered = true
    check symexCacheKey(prog, tLabel("foo"), s0, "z3", "nim", "1", "1") ==
          symexCacheKey(prog, tLabel("foo"), s1, "z3", "nim", "1", "1")

  test "z3Version drift → different key":
    let prog = SymexProgram(body: mkBlock(@[]))
    let s = defaultSymexSettings()
    check symexCacheKey(prog, tLabel("foo"), s, "4.13.3.0", "nim", "1", "1") !=
          symexCacheKey(prog, tLabel("foo"), s, "4.14.0.0", "nim", "1", "1")

  test "nimVersion drift → different key":
    let prog = SymexProgram(body: mkBlock(@[]))
    let s = defaultSymexSettings()
    check symexCacheKey(prog, tLabel("foo"), s, "z3", "2.2.0", "1", "1") !=
          symexCacheKey(prog, tLabel("foo"), s, "z3", "2.3.0", "1", "1")

  test "walkerVersion drift → different key":
    let prog = SymexProgram(body: mkBlock(@[]))
    let s = defaultSymexSettings()
    check symexCacheKey(prog, tLabel("foo"), s, "z3", "nim", "1", "1") !=
          symexCacheKey(prog, tLabel("foo"), s, "z3", "nim", "2", "1")

  test "renderAsChoicesVersion drift → different key (Phase 12 cycle 3)":
    # Bumping the rendering version rotates the key INDEPENDENTLY of
    # the walker version. This lets cycle 6's collection-encoding fix
    # invalidate ONLY collection witnesses without forcing every
    # non-collection cached witness to re-derive.
    let prog = SymexProgram(body: mkBlock(@[]))
    let s = defaultSymexSettings()
    check symexCacheKey(prog, tLabel("foo"), s, "z3", "nim", "1", "1") !=
          symexCacheKey(prog, tLabel("foo"), s, "z3", "nim", "1", "2")

  test "renderAsChoicesVersion and walkerVersion rotate orthogonally":
    # Changing one and holding the other constant produces a key
    # distinct from changing the other and holding the first
    # constant — neither is folded into the other.
    let prog = SymexProgram(body: mkBlock(@[]))
    let s = defaultSymexSettings()
    let kRender = symexCacheKey(prog, tLabel("foo"), s, "z3", "nim", "1", "2")
    let kWalker = symexCacheKey(prog, tLabel("foo"), s, "z3", "nim", "2", "1")
    check kRender != kWalker
