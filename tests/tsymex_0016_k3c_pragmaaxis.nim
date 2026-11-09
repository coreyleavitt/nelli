## RFC-0016 K3c (section 8.1) -- the pragma axis: three lists (local,
## routine/param, type) in `smt/pragmaaxes.nim`, read by the walker's pragma
## decision points.
##
## `{.union.}` overlays its fields, `{.packed.}` removes padding and alignment,
## `{.byref.}` / `{.bycopy.}` fix how a value is passed. The walk models an
## object as independent fields, passed by copy, so a verdict over one of
## these types would not be native's: each declines until modelled. The
## routine list admits the pragmas the walker reads or can ignore and declines
## a name with no row (absent is a decline).
import std/[unittest, strutils, os, compilesettings, sets, options]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/canonicalize
import nelli/smt/pragmaaxes
import nelli/smt/errorkind
import ./s8cu_helpers

type
  UnionObj {.union.} = object
    lo: int32
    all: int64
  PackedObj {.packed.} = object
    a: int8
    b: int32
  ByRefObj {.byref.} = object
    a: int
  ByCopyObj {.bycopy.} = object
    a: int
  PureObj {.pure.} = object
    a: int
  HoldsUnion = object
    u: UnionObj


const
  nimLib = querySetting(libPath)
  statementPragmas = ["push", "pop", "emit", "compile", "passc", "passl",
                      "passL", "line", "line_dir", "hint", "warning", "fatal",
                      "experimental", "pragma", "intdefine", "strdefine",
                      "booldefine", "rangeChecks", "cast", "debugger",
                      "rtlThreadVar", "noinit"]
    ## Pragmas lib/ writes that are not on a declaration (they act on a
    ## region, a statement or a definition), or that a row already covers.

proc libPragmaNames(): HashSet[string] =
  ## Every pragma name `{. .}` spells under lib/: the head of each
  ## top-level comma-separated entry.
  for f in walkDirRec(nimLib):
    if not f.endsWith(".nim"): continue
    var text = ""
    for ln in readFile(f).splitLines:
      if not ln.strip.startsWith("#"): text.add ln & "\n"
    var at = 0
    while true:
      let i = text.find("{.", at)
      if i < 0: break
      let e = text.find(".}", i + 2)
      if e < 0 or e - i > 300:
        at = i + 2
        continue
      var depth = 0
      var quoted = false
      var cur = ""
      var parts: seq[string]
      for ch in text[i + 2 ..< e]:
        if ch == '"': quoted = not quoted
        if not quoted:
          if ch in {'[', '(', '{'}: inc depth
          elif ch in {']', ')', '}'}: dec depth
          elif ch == ',' and depth == 0:
            parts.add cur
            cur = ""
            continue
        cur.add ch
      parts.add cur
      for p in parts:
        var name = ""
        for ch in p.strip:
          if ch in IdentChars: name.add ch else: break
        if name.len > 0 and name[0] in IdentStartChars: result.incl name
      at = e + 2

var
  gBR: ByRefObj
  gBC: ByCopyObj
  gHold: HoldsUnion
  gUnion: UnionObj
  gPacked: PackedObj
  gViaCallee: UnionObj

proc unionLocal(k: int) =
  var u: UnionObj
  u.all = 0
  u.lo = int32(k)
  if u.all == 5: symexTarget("hit")

proc packedLocal(k: int) =
  var p: PackedObj
  p.b = int32(k)
  if p.b == 5: symexTarget("hit")

proc byRefLocal(k: int) =
  var o = ByRefObj(a: k)
  if o.a == 5: symexTarget("hit")

proc byCopyLocal(k: int) =
  let o = ByCopyObj(a: k)
  if o.a == 5: symexTarget("hit")

proc unionGlobal(k: int) =
  gUnion.all = 0
  gUnion.lo = int32(k)
  if gUnion.all == 5: symexTarget("hit")

proc packedGlobal(k: int) =
  gPacked.b = int32(k)
  if gPacked.b == 5: symexTarget("hit")

proc touchViaCallee(k: int) =
  gViaCallee.lo = int32(k)
proc unionGlobalViaCallee(k: int) =
  touchViaCallee(k)
  if k == 5: symexTarget("hit")

proc nestedUnion(k: int) =
  var h: HoldsUnion
  h.u.lo = int32(k)
  if h.u.lo == 5: symexTarget("hit")

proc packedParam(p: PackedObj) =
  if p.b == 5: symexTarget("hit")

proc byRefCallee(o: ByRefObj): int = o.a + 1
proc viaByRefCallee(k: int) =
  gBR = ByRefObj(a: k)
  if byRefCallee(gBR) == 5: symexTarget("hit")

proc byCopyCallee(o: ByCopyObj): int = o.a + 1
proc viaByCopyCallee(k: int) =
  if byCopyCallee(gBC) == 5 and k == 1: symexTarget("hit")

proc pureLocal(k: int) =
  var o = PureObj(a: k)
  if o.a == 5: symexTarget("hit")

proc inl(x: int): int {.inline, noSideEffect.} = x + 1
proc routineInline(k: int) =
  if inl(k) == 5: symexTarget("hit")

proc tagged(x: int): int {.exportnims.} = x + 1
proc routineMarker(k: int) =
  if tagged(k) == 5: symexTarget("hit")

proc localInject(k: int) =
  var x {.used.} = k
  if x == 5: symexTarget("hit")

suite "RFC-0016 K3c: the pragma axis":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 294

  test "the table: three lists, keyed place/name on the pragma scope":
    check render(pragmaAxis.cellOf("local/cursor")) == "pragma:local/cursor"
    check admitPragma(ppType, "union", psTypeDecl).cell ==
      cellKey(axPragma, "type/union")
    var places: set[PragmaPlace]
    for c in pragmaAxis.cells:
      for p in PragmaPlace:
        if render(c.cell).startsWith("pragma:" & placeKey(p) & "/"):
          places.incl p
    check places == {ppLocal, ppRoutine, ppParam, ppType}

  test "every pragma lib/ declares has a row in some place (the lib-wide guard)":
    let found = libPragmaNames()
    checkpoint "pragma names found: " & $found.len
    # Not vacuous: the scan sees the common ones.
    check found.len >= 80
    for n in ["inline", "noSideEffect", "raises", "importc", "final", "pure"]:
      check n in found
    var missing: seq[string]
    for n in found:
      if n in statementPragmas: continue
      var has = false
      for k in pragmaAxis.keys:
        if nimIdentNormalize(k.split('/', 1)[1]) == nimIdentNormalize(n):
          has = true
      if not has: missing.add n
    checkpoint "pragmas with no row: " & $missing
    check missing.len == 0

  test "the four layout and passing pragmas decline at the type place":
    for n in ["union", "packed", "byref", "bycopy"]:
      let a = admitPragma(ppType, n, psTypeDecl)
      check not a.admitted
      check a.decline[0] == some(feUnsupportedOp)
      check n in a.decline[1]

  test "the local list keeps W1-b's verdicts":
    check admitPragma(ppLocal, "noinit", psLocalDecl).admitted
    check admitPragma(ppLocal, "global", psLocalDecl).admitted
    check admitPragma(ppLocal, "cursor", psLocalDecl).decline[0] ==
      some(feLocalPragma)
    check admitPragma(ppLocal, "neverHeardOfIt", psLocalDecl).decline[0] ==
      some(feLocalPragma)

  test "native: the pure type and the inline routine are exact":
    discard pinExact(pureLocal, cellKey(axPragma, "type/pure"))
    discard pinExact(routineInline, cellKey(axPragma, "routine/inline"))

  test "a used local is exact":
    discard pinExact(localInject, cellKey(axPragma, "local/used"))

  test "a union local declines":
    pinDecline(unionLocal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")

  test "a packed local declines":
    pinDecline(packedLocal, cellKey(axPragma, "type/packed"), feUnsupportedOp,
               needle = "pragma:type/packed")

  test "a byref local declines":
    pinDecline(byRefLocal, cellKey(axPragma, "type/byref"), feUnsupportedOp,
               needle = "pragma:type/byref")

  test "a bycopy local declines":
    pinDecline(byCopyLocal, cellKey(axPragma, "type/bycopy"), feUnsupportedOp,
               needle = "pragma:type/bycopy")

  test "a union module-level variable declines":
    pinDecline(unionGlobal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")

  test "a packed module-level variable declines":
    pinDecline(packedGlobal, cellKey(axPragma, "type/packed"), feUnsupportedOp,
               needle = "pragma:type/packed")

  test "a union global reached only through a callee declines":
    pinDecline(unionGlobalViaCallee, cellKey(axPragma, "type/union"),
               feUnsupportedOp, needle = "pragma:type/union")

  test "a union nested in a field declines":
    pinDecline(nestedUnion, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")

  test "a packed formal of the target declines":
    pinDecline(packedParam, cellKey(axPragma, "type/packed"), feUnsupportedOp,
               needle = "pragma:type/packed")

  test "a byref formal of a callee declines":
    pinDecline(viaByRefCallee, cellKey(axPragma, "type/byref"),
               feUnsupportedOp, needle = "pragma:type/byref")

  test "a bycopy formal of a callee declines":
    pinDecline(viaByCopyCallee, cellKey(axPragma, "type/bycopy"),
               feUnsupportedOp, needle = "pragma:type/bycopy")

  test "a routine pragma with no row declines (absent is a decline)":
    pinDecline(routineMarker, cellKey(axPragma, "routine/exportnims"),
               feUnadmitted, needle = "pragma:routine/exportnims")
