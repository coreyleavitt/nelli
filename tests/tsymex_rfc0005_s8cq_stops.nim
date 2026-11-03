## RFC-0005 slice S8cq -- two shapes that stopped the compile before the rule
## could be asked. Each is alone here because a stop takes the file with it.
##
## A user alias of an object (`type A = O`): `classifyType`'s S8bl alias arm and
## `O`'s symbol sent each other back until the VM's depth limit, on this stack
## and not on main. A pragma on a formal (`a {.byref.}: int`): the formal is a
## `nnkPragmaExpr`, whose `strVal` the walker read, on main too. A `{.byref.}`
## formal is the same memory whatever its type, so it declines.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize

type
  O1 = object
    x: int
  AliasO = O1

var gAl: AliasO
var gI: int

proc pAl(x: int) =
  gAl.x = x
  if gAl.x == 3: symexTarget("al")

proc w(a {.byref.}: int): int =
  gI = 50
  a

proc pBr(x: int) =
  if x == 50: return
  gI = x
  let r = w(gI)
  if r == 50: symexTarget("br_r50")
  if r == x: symexTarget("br_rx")

suite "S8cq compile stops":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 252

  test "an alias of an object declines":
    check symexFind(pAl, tLabel("al")).status == sxUnknown

  test "a by-reference formal declines":
    symexCaptureBegin()
    pBr(1)
    let hits = symexCaptureEnd()
    check "br_r50" in hits
    check "br_rx" notin hits
    check symexFind(pBr, tLabel("br_r50")).status == sxUnknown
    check symexFind(pBr, tLabel("br_rx")).status == sxUnknown
