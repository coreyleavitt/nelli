## Mutation testing for PBT (#116).
##
## **The dual of writing tests.** A PBT property checks the SUT against
## inputs. *Mutation testing* checks the *property* against synthetic
## bugs in the SUT — generate program mutants (swap `<` for `<=`, flip
## boolean, replace integer literal with 0), run the property against
## each, count which mutants survive (still pass). A high kill rate
## means the property catches a wide range of bug classes; survivors
## are test gaps the user reviews.
##
## **v1 scope.** In-process mutation via macros: the user wraps a proc
## literal in `mutantsOf(...)`; the macro walks the AST, emits one
## mutant proc per (site, mutator) pair, and the runtime scoring loop
## runs each through a user-supplied property closure. The PIT-style
## compile-and-run sandbox (separate child processes per mutant,
## fresh binary per run) is the architecturally correct full
## implementation; deferred to v2 because it requires Nim compiler
## integration that's orthogonal to demonstrating the catalog +
## scoring machinery.

import std/[macros, options]
import ./engine/types

type
  Mutator* = enum
    ## The mutation catalog. Each enum value names a class of AST
    ## transformation. Adding new mutators is mechanical: extend the
    ## enum and the `applyMutator` switch.
    mtSwapLessLE       ## `<`  → `<=`
    mtSwapGreaterGE    ## `>`  → `>=`
    mtSwapEqNeq        ## `==` → `!=`
    mtSwapAndOr        ## `and` → `or`
    mtReplaceIntZero   ## integer literal → 0
    mtReplaceIntOne    ## integer literal → 1

  Mutant* = object
    ## A surviving / killed mutant after scoring. `description` names
    ## what was mutated; `body` is the variant proc to run.
    description*: string
    body*: proc(x: int): int {.closure.}

  MutationReport* = object
    ## Outcome of running a property against a mutant suite.
    killed*: int          ## mutants the property caught (otFalsified)
    survived*: int        ## mutants that passed (otPassed) — test gaps
    score*: float         ## killed / (killed + survived)
    survivors*: seq[Mutant]   ## the mutants the property didn't catch

proc applyMutator*(n: NimNode, m: Mutator): Option[NimNode] =
  ## Apply mutator `m` at the root of `n`. Returns `some(mutated)`
  ## when the mutator's pattern matches the AST node, `none` otherwise.
  ## Pure: doesn't mutate `n` in place.
  case m
  of mtSwapLessLE:
    if n.kind == nnkInfix and n.len >= 3 and n[0].kind == nnkIdent and
       $n[0] == "<":
      result = some(newTree(nnkInfix, ident"<=", n[1], n[2]))
  of mtSwapGreaterGE:
    if n.kind == nnkInfix and n.len >= 3 and n[0].kind == nnkIdent and
       $n[0] == ">":
      result = some(newTree(nnkInfix, ident">=", n[1], n[2]))
  of mtSwapEqNeq:
    if n.kind == nnkInfix and n.len >= 3 and n[0].kind == nnkIdent and
       $n[0] == "==":
      result = some(newTree(nnkInfix, ident"!=", n[1], n[2]))
  of mtSwapAndOr:
    if n.kind == nnkInfix and n.len >= 3 and n[0].kind == nnkIdent and
       $n[0] == "and":
      result = some(newTree(nnkInfix, ident"or", n[1], n[2]))
  of mtReplaceIntZero:
    if n.kind == nnkIntLit and n.intVal != 0:
      result = some(newLit(0))
  of mtReplaceIntOne:
    if n.kind == nnkIntLit and n.intVal != 1:
      result = some(newLit(1))

# --- collectMutations: walk the AST and emit (description, mutated) pairs ---

const allMutators* = [mtSwapLessLE, mtSwapGreaterGE, mtSwapEqNeq,
                      mtSwapAndOr, mtReplaceIntZero, mtReplaceIntOne]

proc replaceAt(root: NimNode, path: seq[int], newNode: NimNode): NimNode =
  ## Return a copy of `root` with the node at `path` replaced by
  ## `newNode`. Path is a sequence of child indices.
  if path.len == 0:
    return newNode
  result = root.copyNimNode
  for i in 0 ..< root.len:
    if i == path[0]:
      result.add replaceAt(root[i], path[1 ..^ 1], newNode)
    else:
      result.add root[i]

proc collectMutations*(body: NimNode):
    seq[tuple[description: string, mutated: NimNode]] =
  ## Walk `body` depth-first. For every node `n` and mutator `m`, if
  ## `applyMutator(n, m).isSome`, emit a variant of `body` where that
  ## specific node is replaced by the mutator's output. Description
  ## is `"<mutator-name> at <node-repr>"`.
  proc walk(n: NimNode, path: seq[int],
            out0: var seq[tuple[description: string, mutated: NimNode]]) =
    for m in allMutators:
      let mut = applyMutator(n, m)
      if mut.isSome:
        let replaced = replaceAt(body, path, mut.get)
        out0.add (description: $m & " @ " & n.repr,
                  mutated: replaced)
    for i in 0 ..< n.len:
      var subPath = path
      subPath.add i
      walk(n[i], subPath, out0)
  walk(body, @[], result)

macro mutantsOf*(originalLambda: untyped): untyped =
  ## Given a proc literal `proc(x: int): int = ...`, walk its body
  ## and emit `seq[Mutant]` of variants. Each entry pairs a
  ## description with a mutant proc that has the same signature as
  ## the original but with one AST mutation applied.
  ##
  ## v1 supports only `proc(x: int): int` literals. Generalising to
  ## arbitrary signatures is mechanical: read the params, emit
  ## variants with the same params.
  expectKind originalLambda, {nnkLambda, nnkProcDef, nnkDo}
  # Lambda AST layout: [name, ..., params, pragmas, reserved, body]; body is [^1].
  let body = originalLambda[^1]
  let muts = collectMutations(body)
  # Build `@[Mutant(...), Mutant(...), ...]` via quote do.
  var stmts = newStmtList()
  let resSym = genSym(nskVar, "mutResult")
  stmts.add quote do:
    var `resSym` = newSeq[Mutant]()
  for m in muts:
    let mutBody = m.mutated
    let descLit = newLit(m.description)
    # Clone the original lambda, swap in the mutated body so we keep
    # the original formal params verbatim. `originalLambda` is the
    # outer untyped AST; copying it preserves param annotations,
    # pragmas, generic constraints, everything.
    var mutLambda = originalLambda.copy
    mutLambda[^1] = mutBody
    stmts.add quote do:
      `resSym`.add Mutant(description: `descLit`, body: `mutLambda`)
  stmts.add resSym
  result = newBlockStmt(stmts)

# --- runtime scoring loop ---------------------------------------------------

proc mutationScore*(original: proc(x: int): int,
                    mutants: openArray[Mutant],
                    runProperty: proc(fn: proc(x: int): int): Outcome
                   ): MutationReport =
  ## For each mutant, run the property closure (typically a
  ## `forAll(...).outcome` for some property of `fn`) and bucket it:
  ## `otFalsified` → killed, `otPassed` → survived. The original is
  ## sanity-checked: if the property *doesn't* pass on the original,
  ## the score is meaningless (test setup error). That guard is on
  ## the user; we just compute the buckets.
  ##
  ## Score = killed / (killed + survived). Other outcomes (otFlaky,
  ## otExhausted) are treated as survivors — neither side cleanly
  ## proves the mutant was caught.
  result.score = 0.0
  for mut in mutants:
    let o = runProperty(mut.body)
    if o == otFalsified:
      inc result.killed
    else:
      inc result.survived
      result.survivors.add mut
  let total = result.killed + result.survived
  if total > 0:
    result.score = result.killed.float / total.float
