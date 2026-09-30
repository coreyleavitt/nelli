## RFC-0005 (soundness channels) slice S8x -- S8t2's remainder: the
## compile-time VM's `let` aliasing.
##
## While writing `boundEmittedDepth` (`dsl_parser.nim`), S8t2 hit a quirk of
## Nim's compile-time VM: `let top = stack[^1]` binds `top` to the seq
## slot's own node, not a copy, so a later in-place write to that slot
## (`stack[^1].i = ...`) shows through `top`. Native code copies. S8t2 read
## the frame's fields into plain locals. The whole symex front end (the
## parser, the type bridge, the name scopes, the macros' own helpers) runs
## in that VM, so S8x audited it for the same hazard.
##
## What the VM does, probed on Nim 2.2.10 (patched), and pinned below:
##   * A `let` of any non-scalar location aliases it: a seq or array
##     element, an object or tuple field, a Table value, a whole local seq,
##     string, object or `set`, and a tuple unpacked from one. An in-place
##     write to that location or anything inside it (a field write, `add`,
##     `setLen`, `incl`, `[]=` on a nested seq, a `var`-parameter callee)
##     shows through the `let`. So does a non-`var` parameter, while the
##     callee changes the caller's location through a ref.
##   * `var`, `result =`, a proc's return value, `pop`, a slice and a tuple
##     constructor copy. Replacing the whole location (`s[i] = v`,
##     `obj.f = v`) detaches the `let`, which keeps the old value.
##   * Scalars (ints, bools, enums, chars) and refs (`NimNode`, `IRExpr`,
##     `IRStmt`, `IRType`) are unaffected: a scalar is copied into a
##     register, and a ref is meant to be shared.
##
## The audit found no live instance (a `let` copy read after an in-place
## write to its location). It found two latent ones in `dsl_parser.nim`,
## now bound without a `let` of the location:
##   (a) `resolveBreak` bound `let t = ctx.procScoped.jumpTargets[i]` and
##       then called `breakVia(ctx, i)`, which mints `brkLabel` in place in
##       that same element. `t` was not read after the call.
##   (b) `ensureProcRegistered` saved `let savedProcScoped =
##       ctx.procScoped` around a callee's parse, which fills the collectors
##       in place. It was safe only because the next statement replaced the
##       whole record (`ctx.procScoped = ProcScopedCollectors()`), which
##       detaches the `let`. Resetting only some fields would have made the
##       restore a no-op.
## The table is in the RFC's S8x note (§2.5).
##
## Each VM pin evaluates a proc in the VM (`const`) and natively and checks
## both: a toolchain that changes the VM's behaviour fails here first.
import std/[unittest, strutils, os, tables, sets]
import std/macros except strVal
import nelli/smt/scoped_names   ## S8x: enterNameScope / leaveNameScope
import audit_scan_utils

# ---- the VM's behaviour -----------------------------------------------------

type
  Frame = tuple[n: int, i, h: int]
    ## `boundEmittedDepth`'s frame shape (S8t2).
  Target = object
    ## `JumpTarget`'s shape: a flag and a label minted in place.
    isLoop: bool
    label: string
  Collectors = object
    ## `ProcScopedCollectors`' shape: value fields filled in place.
    xs: seq[int]
    tags: seq[string]
  Holder = ref object
    ## `ParseCtx`'s shape: a ref holding the collectors by value.
    c: Collectors

proc letFrameThenFieldWrite(): int =
  ## S8t2's hazard: `let top = stack[^1]`, then the frame is updated.
  var stack: seq[Frame] = @[(1, 0, 0)]
  let top = stack[^1]
  stack[^1].i = 7
  top.i

proc plainLocalsThenFieldWrite(): int =
  ## S8t2's fix: the fields read into plain locals.
  var stack: seq[Frame] = @[(1, 0, 0)]
  let i = stack[^1].i
  stack[^1].i = 7
  i

proc mintLabel(s: var seq[Target]; i: int) = s[i].label = "brk1"

proc letElemThenVarParamWrite(): string =
  ## Latent (a)'s shape: an element bound, then a `var`-parameter callee
  ## writes a field of that element (`breakVia` minting `brkLabel`).
  var s = @[Target(isLoop: false)]
  let t = s[0]
  mintLabel(s, 0)
  t.label

proc indexReadThenVarParamWrite(): string =
  ## Latent (a)'s fix: the fields read through the index before the write.
  var s = @[Target(isLoop: false)]
  let label = s[0].label
  mintLabel(s, 0)
  label

proc letFieldThenInPlaceAdd(): seq[int] =
  ## Latent (b)'s hazard without the reset: a ref's value field bound, then
  ## filled in place.
  let h = Holder(c: Collectors(xs: @[1]))
  let saved = h.c
  h.c.xs.add 2
  h.c.tags.add "t"
  saved.xs

proc letFieldResetThenInPlaceAdd(): seq[int] =
  ## Latent (b) as it was: the whole field replaced first, which detaches
  ## the `let`.
  let h = Holder(c: Collectors(xs: @[1]))
  let saved = h.c
  h.c = Collectors()
  h.c.xs.add 2
  saved.xs

proc varFieldThenInPlaceAdd(): seq[int] =
  ## Latent (b)'s fix: a `var` copy survives in-place writes, reset or not.
  let h = Holder(c: Collectors(xs: @[1]))
  var saved = h.c
  h.c.xs.add 2
  h.c.tags.add "t"
  saved.xs

proc resultOfFieldThenAdd(parts: seq[Collectors]): seq[int] =
  ## `lowerShortCircuitParts.nest`'s shape: `result = parts[k].pre`, then
  ## `result.add`.
  result = parts[0].xs
  result.add 99

proc resultCopiesLocation(): seq[int] =
  let parts = @[Collectors(xs: @[1])]
  discard resultOfFieldThenAdd(parts)
  parts[0].xs

proc popThenPush(): string =
  ## `popJumpTarget`'s shape: a popped element, then a push and a write.
  var s = @[Target(label: "a")]
  let t = s.pop()
  s.add Target()
  s[0].label = "b"
  t.label

proc letLocalStringThenAdd(): string =
  ## The hazard is not specific to seq elements: a whole local string.
  var str = "ab"
  let x = str
  str.add "c"
  x

proc letLocalSetThenIncl(): set[char] =
  var s = {'a'}
  let x = s
  s.incl 'b'
  x

proc paramThenCallerWriteThroughRef(h: Holder; xs: seq[int]): int =
  ## A non-`var` parameter, while the callee changes the caller's location
  ## through a ref.
  h.c.xs.add 3
  xs.len

proc paramAliasesCallerLocation(): int =
  let h = Holder(c: Collectors(xs: @[1]))
  paramThenCallerWriteThroughRef(h, h.c.xs)

suite "S8x: the compile-time VM aliases a let of a location":

  test "S8t2's frame: a let of stack[^1] sees a later field write":
    const vm = letFrameThenFieldWrite()
    check vm == 7                            # aliased in the VM
    check letFrameThenFieldWrite() == 0      # copied natively
    const vmFix = plainLocalsThenFieldWrite()
    check vmFix == 0
    check plainLocalsThenFieldWrite() == 0

  test "an element bound before a var-parameter callee writes it":
    const vm = letElemThenVarParamWrite()
    check vm == "brk1"
    check letElemThenVarParamWrite() == ""
    const vmFix = indexReadThenVarParamWrite()
    check vmFix == ""
    check indexReadThenVarParamWrite() == ""

  test "a ref's value field: let aliases, a whole reset detaches, var copies":
    const vm = letFieldThenInPlaceAdd()
    check vm == @[1, 2]
    check letFieldThenInPlaceAdd() == @[1]
    const vmReset = letFieldResetThenInPlaceAdd()
    check vmReset == @[1]
    check letFieldResetThenInPlaceAdd() == @[1]
    const vmVar = varFieldThenInPlaceAdd()
    check vmVar == @[1]
    check varFieldThenInPlaceAdd() == @[1]

  test "result =, pop and a proc's return value copy":
    const vmResult = resultCopiesLocation()
    check vmResult == @[1]
    check resultCopiesLocation() == @[1]
    const vmPop = popThenPush()
    check vmPop == "a"
    check popThenPush() == "a"

  test "the hazard covers whole locals and parameters too":
    const vmStr = letLocalStringThenAdd()
    check vmStr == "abc"
    check letLocalStringThenAdd() == "ab"
    const vmSet = letLocalSetThenIncl()
    check vmSet == {'a', 'b'}
    check letLocalSetThenIncl() == {'a'}
    const vmParam = paramAliasesCallerLocation()
    check vmParam == 2
    check paramAliasesCallerLocation() == 1

# ---- the name scopes' save / restore, in the VM -------------------------------
#
# `enterNameScope` returns `result = nameScope` and then resets two of its
# fields; a callee's claims then fill the global in place. Were that `result`
# an alias, `leaveNameScope` would restore the callee's renames (and lose
# the caller's claims). `result =` copies, so it does not: pinned on the real
# module, the way `ensureProcRegistered` and `parseProcAsValue` use it.

proc s8xCaller() =
  block:
    let y = 1
    discard y
  block:
    let y = 2
    discard y

proc s8xCallee() =
  block:
    let x = 1
    discard x
  block:
    let x = 2
    discard x

proc letSymsNamed(n: NimNode; name: string; into: var seq[NimNode]) =
  if n.kind == nnkSym and symKind(n) == nskLet and
     macros.strVal(n) == name and n notin into:
    into.add n
  for c in n: letSymsNamed(c, name, into)

macro nameScopeRoundTrip(caller, callee: typed): untyped =
  ## (the caller's second `y` inside its scope, the callee's second `x`
  ## inside the callee's scope, then both after the callee's scope is left)
  let callerImpl = caller.getImpl
  let calleeImpl = callee.getImpl
  var ys, xs: seq[NimNode]
  letSymsNamed(callerImpl, "y", ys)
  letSymsNamed(calleeImpl, "x", xs)
  doAssert ys.len == 2 and xs.len == 2
  resetNameScopes()
  claimRoutine(callerImpl)
  let callerY = scoped_names.strVal(ys[1])
  let savedNames = enterNameScope()
  claimRoutine(calleeImpl)
  let calleeX = scoped_names.strVal(xs[1])
  leaveNameScope(savedNames)
  let callerYAfter = scoped_names.strVal(ys[1])
  let calleeXAfter = scoped_names.strVal(xs[1])
  resetNameScopes()
  newLit((callerY, calleeX, callerYAfter, calleeXAfter))

suite "S8x: enterNameScope / leaveNameScope in the VM":

  test "leaving a callee's scope drops its renames and keeps the caller's":
    const r = nameScopeRoundTrip(s8xCaller, s8xCallee)
    check r[0].startsWith("y__sc")     # the caller's second `y` renamed
    check r[1].startsWith("x__sc")     # the callee's second `x` renamed
    check r[2] == r[0]                 # the caller's rename survives
    check r[3] == "x"                  # the callee's rename is dropped

# ---- the two latent sites stay fixed ------------------------------------------

const dslParserPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                      "smt" / "dsl_parser.nim"

suite "S8x: no let binds a value location of ctx.procScoped":

  test "dsl_parser.nim binds ctx.procScoped's record or elements by index or var":
    # `ProcScopedCollectors` and `JumpTarget` are value types filled in place
    # during the parse, so a `let` of one aliases it in the VM. Reading a
    # scalar or ref field (`.len`, `.high`, a `NimNode`) is fine, as is a
    # `template` alias that re-reads the location.
    var hits: seq[string]
    var lineNo = 0
    for raw in readFile(dslParserPath).splitLines():
      inc lineNo
      let t = raw.strip()
      if isCommentLine(t) or not t.startsWith("let "): continue
      let eq = t.find('=')
      if eq < 0: continue
      let rhs = t[eq + 1 .. ^1].strip().split('#')[0].strip()
      if not rhs.startsWith("ctx.procScoped"): continue
      if rhs.endsWith(".len") or rhs.endsWith(".high"): continue
      hits.add $lineNo & ": " & t
    check hits.len == 0
    if hits.len > 0: echo hits.join("\n")
