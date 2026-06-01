## IR interpreter — the symex back-end.
##
## Drives a path frontier over the IR built by `dsl_parser`, accumulating
## Z3 path conditions, and on hitting a target (label match or assertion
## violation) calls `Z3Solver.check` to find a witness.
##
## Phase 1 encoding choices (per ADR-0001 `isExact`):
##
##   * `IRTypeKind.itInt`  → `Z3BitVec[64]`  (signed; matches Nim `int`
##                            on 64-bit platforms, which is our only
##                            supported platform for v1)
##   * `IRTypeKind.itBool` → `Z3Bool`
##
## Phase 2 will introduce the abstraction layer and the choice between
## BV[W] and Z3Int. v1 ships with BV-only and the runtime is structured
## so the abstraction layer plugs in at the binding site without
## touching the walker.

import std/tables
import std/options
import z3

import ./types

type
  IntWidth* = static int

const Phase1IntWidth* = 64
  ## On the supported platform (64-bit Linux) Nim `int` is 64-bit.
  ## Phase 2 lifts this to per-type width tracking.

type
  SymVal = object
    ## A symbolic value bound to one of the supported families.
    ## Phase 1 has just int (as BV[64]) and bool; Phase 2+ grow this.
    case ty: IRTypeKind
    of itInt:
      bv: Z3BitVec[Phase1IntWidth]
    of itBool:
      bo: Z3Bool

  Env = OrderedTable[string, SymVal]
    ## Variable bindings on a path. Ordered so witness extraction can
    ## walk the original param order without a separate sidecar list.

  Path = ref object
    pc: seq[Z3Bool]    ## path condition (conjunction of accumulated guards)
    env: Env           ## variable bindings (params + locals)

  RawWitness = object
    ## Untyped witness shape — the runtime returns this; the public
    ## macro wraps it into a typed tuple.
    paramOrder: seq[string]   ## param names in declaration order
    intVals: Table[string, int64]
    boolVals: Table[string, bool]

  RawResult* = object
    case status*: SymexStatusKind
    of sxSat:
      witness*: RawWitness
    of sxUnsat, sxUnknown:
      discard

# ---- Path / env helpers -----------------------------------------------------

proc clonePath(p: Path): Path =
  ## Shallow copy — pc is reassigned per branch, env is overwritten
  ## per let/assign, both never mutated in place.
  Path(pc: p.pc, env: p.env)

# ---- IR-expr → Z3 -----------------------------------------------------------
#
# The two-family encoding means each expression has a "natural" target
# type. `lowerInt` / `lowerBool` are typed entry points; the runtime
# only calls the one matching the syntactic position. AST nodes whose
# operands have mismatched type kinds would be rejected at parse time —
# in Phase 1 the parser only emits well-typed IR, so the lowering
# procs can assume the types match.

proc lowerInt(env: Env, e: IRExpr): Z3BitVec[Phase1IntWidth]
proc lowerBool(env: Env, e: IRExpr): Z3Bool

proc lowerInt(env: Env, e: IRExpr): Z3BitVec[Phase1IntWidth] =
  case e.kind
  of iekIntLit:
    mkBitVec[Phase1IntWidth](e.ival)
  of iekVar:
    env[e.vname].bv
  of iekBinop:
    let l = lowerInt(env, e.lhs)
    let r = lowerInt(env, e.rhs)
    case e.bop
    of bAdd: l + r
    of bSub: l - r
    of bMul: l * r
    of bDiv: bvsdiv(l, r)
    of bMod: bvsmod(l, r)
    of bAnd: l and r        ## bitwise (Phase 1 isn't reached for ints via
                            ## `and`/`or`/`xor` since the parser rejects
                            ## bitwise — included for forward compat)
    of bOr:  l or r
    of bXor: l xor r
    else:
      raise newException(ValueError,
        "lowerInt: comparison " & $e.bop & " in integer position")
  of iekUnop:
    case e.uop
    of uNeg: -lowerInt(env, e.operand)
    of uNot:
      raise newException(ValueError, "lowerInt: `not` in integer position")
  else:
    raise newException(ValueError,
      "lowerInt: unsupported expr kind " & $e.kind)

proc lowerBool(env: Env, e: IRExpr): Z3Bool =
  case e.kind
  of iekBoolLit:
    mkBool(e.bval)
  of iekVar:
    env[e.vname].bo
  of iekBinop:
    case e.bop
    of bEq:
      # Polymorphic equality — peek the operand kind via either side.
      # In Phase 1 both sides are syntactically int or bool.
      if e.lhs.kind == iekBoolLit or e.rhs.kind == iekBoolLit:
        lowerBool(env, e.lhs) == lowerBool(env, e.rhs)
      else:
        # treat as int-eq; if the parser ever lets bools through here
        # the Z3 type system will catch it.
        lowerInt(env, e.lhs) == lowerInt(env, e.rhs)
    of bNe:
      if e.lhs.kind == iekBoolLit or e.rhs.kind == iekBoolLit:
        lowerBool(env, e.lhs) != lowerBool(env, e.rhs)
      else:
        lowerInt(env, e.lhs) != lowerInt(env, e.rhs)
    of bLt: bvslt(lowerInt(env, e.lhs), lowerInt(env, e.rhs))
    of bLe: bvsle(lowerInt(env, e.lhs), lowerInt(env, e.rhs))
    of bGt: bvsgt(lowerInt(env, e.lhs), lowerInt(env, e.rhs))
    of bGe: bvsge(lowerInt(env, e.lhs), lowerInt(env, e.rhs))
    of bAnd: lowerBool(env, e.lhs) and lowerBool(env, e.rhs)
    of bOr:  lowerBool(env, e.lhs) or  lowerBool(env, e.rhs)
    of bXor: lowerBool(env, e.lhs) xor lowerBool(env, e.rhs)
    else:
      raise newException(ValueError,
        "lowerBool: arithmetic op " & $e.bop & " in boolean position")
  of iekUnop:
    case e.uop
    of uNot: not lowerBool(env, e.operand)
    of uNeg:
      raise newException(ValueError, "lowerBool: `-` in boolean position")
  else:
    raise newException(ValueError,
      "lowerBool: unsupported expr kind " & $e.kind)

# ---- Driver -----------------------------------------------------------------
#
# A path-frontier walker. Each path is replayed independently; on hitting
# a target-matching node we check sat under that path's pc and, if SAT,
# extract a witness via the model. The Phase-1 search is exhaustive —
# every reachable path is explored — because the supported fragment has
# no loops or unbounded recursion.

proc extractWitness(m: Z3Model, env: Env, params: seq[IRParam]): RawWitness =
  result.paramOrder = newSeq[string](params.len)
  for i, p in params:
    result.paramOrder[i] = p.name
    let sv = env[p.name]
    case p.ty
    of itInt:
      result.intVals[p.name] = m.evalInt(sv.bv)
    of itBool:
      result.boolVals[p.name] = m.evalBool(sv.bo)

proc trySolve(ctx: Z3Context,
              path: Path,
              params: seq[IRParam]): tuple[status: SymexStatusKind,
                                            witness: RawWitness] =
  ## Check satisfiability of the path condition; if SAT extract witness.
  let s = newSolver(ctx)
  for c in path.pc:
    s.add(c)
  let r = s.check()
  case r
  of zsSat:
    let m = s.model()
    (status: sxSat, witness: extractWitness(m, path.env, params))
  of zsUnsat:
    (status: sxUnsat, witness: RawWitness())
  of zsUnknown:
    (status: sxUnknown, witness: RawWitness())

type
  WalkCtx = object
    z3:        Z3Context
    target:    SymexTarget
    params:    seq[IRParam]
    found:     Option[RawResult]
    sawUnknown: bool

proc shouldStop(w: WalkCtx): bool {.inline.} =
  w.found.isSome and w.found.get.status == sxSat

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path]
  ## Forward-symbolic-execution one statement. Consumes a frontier
  ## (the paths surviving up to this point) and returns the frontier
  ## surviving *after* the statement. Path-conditions, environment
  ## updates, and target-hit checks all happen inline.

proc walkBlock(stmts: seq[IRStmt], paths: seq[Path], w: var WalkCtx): seq[Path] =
  ## Sequencing: fold `walk` across the statement list. The frontier
  ## at step `k+1` is the union of all surviving paths produced by
  ## walking step `k`.
  result = paths
  for s in stmts:
    if w.shouldStop: return
    result = walk(s, result, w)
    if result.len == 0: return

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path] =
  if w.shouldStop or stmt == nil or paths.len == 0:
    return paths
  case stmt.kind
  of isBlock:
    walkBlock(stmt.stmts, paths, w)
  of isIf:
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      var accumNegated: seq[Z3Bool]
      for br in stmt.branches:
        let condBool = lowerBool(p.env, br.cond)
        let armPath = Path(pc: p.pc & accumNegated & @[condBool], env: p.env)
        survivors.add walk(br.body, @[armPath], w)
        accumNegated.add(not condBool)
        if w.shouldStop: return
      let elsePath = Path(pc: p.pc & accumNegated, env: p.env)
      if stmt.elseBody != nil:
        survivors.add walk(stmt.elseBody, @[elsePath], w)
      else:
        # Implicit else: the fall-through path survives unchanged,
        # carrying the negated prior guards.
        survivors.add elsePath
    survivors
  of isLet:
    var out2: seq[Path]
    for p in paths:
      var newEnv = p.env
      case stmt.lty
      of itInt:
        newEnv[stmt.lname] = SymVal(ty: itInt, bv: lowerInt(p.env, stmt.lvalue))
      of itBool:
        newEnv[stmt.lname] = SymVal(ty: itBool, bo: lowerBool(p.env, stmt.lvalue))
      out2.add Path(pc: p.pc, env: newEnv)
    out2
  of isReturn:
    @[]   ## paths die here; subsequent stmts in the block are not walked
  of isAssert:
    var out2: seq[Path]
    for p in paths:
      if w.shouldStop: return
      let cond = lowerBool(p.env, stmt.acond)
      if w.target.kind == stkAssertionViolation:
        # Fork: try to reach `not cond` as a witness on this path.
        let violPath = Path(pc: p.pc & @[not cond], env: p.env)
        let (st, wit) = trySolve(w.z3, violPath, w.params)
        case st
        of sxSat:    w.found = some(RawResult(status: sxSat, witness: wit))
        of sxUnknown: w.sawUnknown = true
        of sxUnsat:  discard
      # Continue along the assertion-holds path either way.
      out2.add Path(pc: p.pc & @[cond], env: p.env)
    out2
  of isTargetLabel:
    if w.target.kind == stkLabel and w.target.label == stmt.tname:
      for p in paths:
        if w.shouldStop: return
        let (st, wit) = trySolve(w.z3, p, w.params)
        case st
        of sxSat:    w.found = some(RawResult(status: sxSat, witness: wit))
        of sxUnknown: w.sawUnknown = true
        of sxUnsat:  discard
    paths   ## the label is a marker — the path continues
  of isUnsupported:
    # Model the unsupported stmt as identity-on-path-condition and
    # flag global uncertainty. A later sxUnsat verdict downgrades
    # to sxUnknown because of this flag.
    w.sawUnknown = true
    paths

# ---- Public driver ----------------------------------------------------------

proc runSymex*(prog: SymexProgram,
               target: SymexTarget,
               settings: SymexSettings = defaultSymexSettings()): RawResult =
  ## Top-level interpreter. Sets up a fresh Z3 context, encodes the
  ## params, walks the IR, and returns the raw (untyped) result.
  ## The public-API macro lifts this into a typed `SymexResult[T]`.
  let ctx = newContext()
  setCurrentContext(ctx)
  var env: Env
  for p in prog.params:
    case p.ty
    of itInt:
      env[p.name] = SymVal(ty: itInt, bv: mkBitVecVar[Phase1IntWidth](p.name))
    of itBool:
      env[p.name] = SymVal(ty: itBool, bo: mkBoolVar(p.name))
  let initial = Path(pc: @[], env: env)
  var w = WalkCtx(
    z3: ctx, target: target, params: prog.params,
    found: none(RawResult), sawUnknown: false,
  )
  discard walk(prog.body, @[initial], w)
  if w.found.isSome:
    w.found.get
  elif w.sawUnknown:
    RawResult(status: sxUnknown)
  else:
    RawResult(status: sxUnsat)

# ---- Raw → typed witness ----------------------------------------------------
#
# The macro emits a small adapter that reads from RawWitness into a tuple
# whose element types come from the proc's params. These two procs are
# the typed bridge.

proc readInt*(w: RawWitness, name: string): int =
  int(w.intVals[name])

proc readBool*(w: RawWitness, name: string): bool =
  w.boolVals[name]
