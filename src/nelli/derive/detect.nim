## Recursive-type detection — the testable seam under `arbitrary(T)` (#104).
##
## The `arbitrary(T)` macro in `derive.nim` synthesizes a `Strategy[T]` by
## walking `T`'s `getTypeImpl`. The hard case is **self-reference**:
## variant trees, linked lists, ASTs whose fields recurse on `T` itself
## (directly, or under one of the supported wrappers: `seq`, `Option`,
## `HashSet`, `Table`). The detector here decides "is this field type
## recursive in `selfName`, and if so, how?" — emitting a structured
## verdict the macro dispatches on.
##
## Public so domain-specific derive layers (and unit tests) can call
## the same primitives the macro does. Previously these were private to
## the macro module; bugs surfaced only as obscure "this type doesn't
## derive" compile errors. The seam gives them a localized signal.

import std/[macros, sets, options]

type
  RecursionKind* = enum
    ## How a field type relates to the enclosing-type name.
    drNone        ## doesn't reference the self-type
    drDirect      ## bare self reference (a field of type `Foo` inside `Foo`)
    drViaSeq      ## seq[Self]
    drViaOption   ## Option[Self]
    drViaHashSet  ## HashSet[Self]
    drViaTable    ## Table[_, Self]
    drMutual      ## references another type that transitively reaches Self

type RangeBounds* = tuple[lo, hi: BiggestInt]

proc tryRangeBounds*(t: NimNode): Option[RangeBounds] =
  ## If `t` is a Nim `range[lo..hi]` type — either directly written as
  ## `range[10..50]` (in which case `t.kind == nnkBracketExpr`) or named
  ## (`Natural`, `Positive`, or a user `type MyR = range[lo..hi]`, in
  ## which case `t.kind == nnkSym` and we drill via `getTypeImpl`) —
  ## return `some((lo, hi))`. Otherwise `none`.
  ##
  ## #111: this is the seam `arbitrary(T)` uses to recognise refinement
  ## types and emit `integers(lo, hi)` instead of falling back to the
  ## "cannot derive" error.
  var node = t
  if node.kind == nnkSym:
    let impl = node.getTypeImpl
    if impl.kind == nnkBracketExpr and impl.len >= 2 and $impl[0] == "range":
      node = impl
  if node.kind == nnkBracketExpr and node.len >= 2 and $node[0] == "range":
    let infix = node[1]
    if infix.kind == nnkInfix and infix.len == 3 and
       $infix[0] == ".." and
       infix[1].kind == nnkIntLit and infix[2].kind == nnkIntLit:
      return some((lo: infix[1].intVal, hi: infix[2].intVal))
  none(RangeBounds)

proc isSelfType*(t: NimNode, selfName: string): bool =
  ## True iff `t` is an ident or symbol whose textual name equals
  ## `selfName`. Cheap exact-match — the bedrock case the wrapper
  ## detectors short-circuit on.
  case t.kind
  of nnkSym, nnkIdent: $t == selfName
  else: false

proc reachesTypeViaFields*(t: NimNode, target: string,
                           visited: var HashSet[string],
                           maxDepth: int): bool =
  ## True iff any transitive field of `t` references the type named
  ## `target`. Used by `classifyRecursion` to detect mutual recursion
  ## (`MutA → seq[MutB] → MutA`). `visited` prevents revisiting types
  ## within the same walk; `maxDepth` bounds traversal in the presence
  ## of unsupported wrapper shapes.
  if maxDepth <= 0: return false
  var ty = t
  while ty.kind == nnkBracketExpr:
    case $ty[0]
    of "seq", "HashSet", "Option":
      if ty.len < 2: return false
      ty = ty[1]
    of "Table":
      if ty.len < 3: return false
      ty = ty[2]
    else: return false
  if ty.kind notin {nnkSym, nnkIdent}: return false
  let name = $ty
  if name == target: return true
  if name in visited: return false
  visited.incl name
  var impl: NimNode
  try:
    impl = ty.getTypeImpl
  except: return false
  if impl.kind == nnkRefTy:
    var inner = impl[0]
    if inner.kind == nnkSym:
      try: inner = inner.getTypeImpl
      except: return false
    impl = inner
  if impl.kind != nnkObjectTy: return false
  let recList = impl[2]
  if recList.kind != nnkRecList: return false
  for fd in recList:
    case fd.kind
    of nnkIdentDefs:
      let ft = fd[fd.len - 2]
      if reachesTypeViaFields(ft, target, visited, maxDepth - 1):
        return true
    of nnkRecCase:
      # AST shapes inside object-variants: single-field branches are bare
      # IdentDefs; multi/empty branches are RecList.
      for branch in fd[1 ..^ 1]:
        if branch.kind != nnkOfBranch: continue
        let body = branch[^1]
        case body.kind
        of nnkIdentDefs:
          if reachesTypeViaFields(body[body.len - 2], target,
                                  visited, maxDepth - 1):
            return true
        of nnkRecList:
          for ffd in body:
            if ffd.kind != nnkIdentDefs: continue
            let ft = ffd[ffd.len - 2]
            if reachesTypeViaFields(ft, target, visited, maxDepth - 1):
              return true
        else: discard
    else: discard
  false

proc classifyRecursion*(t: NimNode, selfName: string): RecursionKind =
  ## Classify how field type `t` relates to a type named `selfName`.
  ## Returns one of seven verdicts (`drDirect`, `drViaSeq`, ...,
  ## `drMutual`, `drNone`) so the macro can dispatch on the structured
  ## answer rather than re-implementing the string-comparison chain.
  if isSelfType(t, selfName): return drDirect
  if t.kind == nnkBracketExpr:
    case $t[0]
    of "seq":
      if t.len >= 2 and isSelfType(t[1], selfName): return drViaSeq
    of "Option":
      if t.len >= 2 and isSelfType(t[1], selfName): return drViaOption
    of "HashSet":
      if t.len >= 2 and isSelfType(t[1], selfName): return drViaHashSet
    of "Table":
      if t.len >= 3 and isSelfType(t[2], selfName): return drViaTable
    else: discard
  # No direct or single-wrapper match — check for mutual recursion: does
  # the field type (or its element, for wrappers) lead to a named type
  # that transitively references `selfName`?
  var visited = initHashSet[string]()
  if reachesTypeViaFields(t, selfName, visited, maxDepth = 8):
    return drMutual
  drNone
