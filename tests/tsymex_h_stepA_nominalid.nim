## Cluster H (ADR-0022) Step A — compile-time unit test of the
## `nominalId(NimNode)` helper introduced in `dsl_typebridge.nim`.
##
## This is a pure macro-time primitive: `nominalId` runs during macro
## expansion, not at runtime. The properties below are therefore proven as
## genuine COMPILE-TIME assertions — the `nominalId*` calls are folded into
## `const` string literals during semantic checking, and the `static:`
## block's `doAssert`s execute in the compile-time VM. A handful of ordinary
## `unittest` `check`s atop those same consts are added purely so the
## properties also show up in the test runner's pass/fail output.
##
## Step A is a pure no-op groundwork slice (ADR-0022): `nominalId` is
## populated onto `IRType.nominalId` at the named-object `tTuple(...)` call
## sites in `dsl_typebridge.nim`, but nothing downstream reads that field yet
## (Step B wires it into `refPointeeTypeId`). Verdicts, witnesses, and cache
## keys are unaffected — this file exercises ONLY the helper itself.
##
## RED (pre-helper) state: this file fails to COMPILE, because `nominalId`
## is undefined/unexported from `proptest/smt/dsl_typebridge`.
## GREEN: it compiles and every `static: doAssert` holds.
import std/[unittest, macros]
import proptest/smt/dsl_typebridge

type
  NodeObj = object
    n: int

  OtherObj = object
    m: int

  Box[T] = object
    val: T

# ---------------------------------------------------------------------------
# Helpers to reach `nominalId` from typed AST.
# ---------------------------------------------------------------------------

macro nominalIdOfType(T: typedesc): string =
  ## `T: typedesc` arrives wrapped as `typeDesc[X]`; peel one layer so
  ## `nominalId` sees the actual `nnkSym` (mirrors the `innerTypeSym` idiom
  ## in the sibling test `tsymex_typebridge_variants.nim`).
  var inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst = inst[1]
  newLit(nominalId(inst))

macro nominalIdOfExpr(x: typed): string =
  ## For a `var x: Box[T]`, `x.getTypeInst` yields the `nnkBracketExpr`
  ## instantiation node directly — `x` is a VALUE (not a typedesc), so there
  ## is no `typeDesc[...]` wrapper to peel.
  newLit(nominalId(x.getTypeInst))

# ---------------------------------------------------------------------------
# Property 1 — stability: nominalId of the SAME named-object symbol,
# computed at two independent call sites, is equal and non-empty.
# ---------------------------------------------------------------------------

const idNodeSiteA = nominalIdOfType(NodeObj)
const idNodeSiteB = nominalIdOfType(NodeObj)

# ---------------------------------------------------------------------------
# Property 2 — distinct named object types produce different ids.
# ---------------------------------------------------------------------------

const idOther = nominalIdOfType(OtherObj)

# ---------------------------------------------------------------------------
# Property 3 — generic discrimination: nominalId(Box[int]) != nominalId
# (Box[string]). The head symbol's `signatureHash` is identical for both
# instantiations; the type ARGS (threaded via the `nnkBracketExpr` recursion)
# are what disambiguate them.
# ---------------------------------------------------------------------------

var bi: Box[int]
var bs: Box[string]
const idBoxInt = nominalIdOfExpr(bi)
const idBoxString = nominalIdOfExpr(bs)

static:
  doAssert idNodeSiteA.len > 0
  doAssert idNodeSiteA == idNodeSiteB
  doAssert idNodeSiteA != idOther
  doAssert idBoxInt.len > 0
  doAssert idBoxString.len > 0
  doAssert idBoxInt != idBoxString

suite "symex Cluster H Step A — nominalId(NimNode) compile-time primitive":
  test "stability: same named-object symbol at two call sites yields an equal, non-empty id":
    check idNodeSiteA.len > 0
    check idNodeSiteA == idNodeSiteB

  test "distinct named object types produce different ids":
    check idNodeSiteA != idOther

  test "generic instantiations discriminate by type args: Box[int] != Box[string]":
    check idBoxInt.len > 0
    check idBoxString.len > 0
    check idBoxInt != idBoxString
