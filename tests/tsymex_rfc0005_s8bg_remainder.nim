## RFC-0005 (soundness channels) slice S8bg -- S8bd's remainder.
##
## PROBE DRAFT v2 (not yet the final pins): exercising byRefSub's refusal of
## a pointer-dereference, a type-conversion and a cast lvalue, to observe
## today's decline before designing the fix. See the RFC's "As landed
## (S8bd)" note, "different mechanisms" list, last item.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

type Box = ref object
  x: int

# ---- probe A: pointer dereference through a PLAIN `ptr T` FORMAL -------------

var gBoxA: Box

proc setXG(v: var int, k: int) =
  v = k
  gBoxA.x = 5

proc innerPtr(pb: ptr int, k: int) =
  ## `pb[]`, a plain (non-`var`) `ptr` formal's dereference: passed by
  ## reference to `setXG` since `setXG` also reaches `gBoxA` directly.
  setXG(pb[], k)

proc sutPtrFormalDeref(k: int) =
  let b = Box(x: 0)
  gBoxA = b
  innerPtr(addr b.x, k)     ## S8an's modelled `addr lv` call-argument form.
  if b.x == 5 and gBoxA.x == 5 and k == 1: symexTarget("pfA")
  if b.x == k and k != 5: symexTarget("pfA_dead")

# ---- probe A2: a `var ptr T` FORMAL's dereference ----------------------------

proc innerVarPtr(pb: var ptr int, k: int) =
  setXG(pb[], k)

proc sutVarPtrFormalDeref(k: int) =
  let b = Box(x: 0)
  gBoxA = b
  var pbLocal = addr b.x
  innerVarPtr(pbLocal, k)
  if b.x == 5 and gBoxA.x == 5 and k == 2: symexTarget("pfA2")
  if b.x == k and k != 5: symexTarget("pfA2_dead")

# ---- probe B: an inheritance upcast conversion lvalue ------------------------

type Animal = ref object of RootObj
  x: int
type Dog = ref object of Animal
  y: int

var gAnimal: Animal

proc setXG2(v: var int, k: int) =
  v = k
  gAnimal.x = 5

proc sutConvInherit(k: int) =
  let d = Dog(x: 0, y: 0)
  gAnimal = d
  setXG2(Animal(d).x, k)
  if Animal(d).x == 5 and gAnimal.x == 5 and k == 1: symexTarget("cvB")
  if Animal(d).x == k and k != 5: symexTarget("cvB_dead")

# ---- probe C: a cast lvalue, inline (no intermediate var/let) ----------------

var gBoxC: Box

proc setXC(v: var int, k: int) =
  v = k
  gBoxC.x = 5

proc sutCastLvalue(k: int) =
  let p = Box(x: 0)
  gBoxC = p
  setXC(cast[ptr int](addr p.x)[], k)
  if p.x == 5 and gBoxC.x == 5 and k == 1: symexTarget("ccC")
  if p.x == k and k != 5: symexTarget("ccC_dead")

suite "S8bg probe v2: today's decline":
  test "nim sanity":
    block:
      let b = Box(x: 0)
      gBoxA = b
      innerPtr(addr b.x, 1)
      check b.x == 5
    block:
      let b = Box(x: 0)
      gBoxA = b
      var pbLocal = addr b.x
      innerVarPtr(pbLocal, 2)
      check b.x == 5
    block:
      let d = Dog(x: 0, y: 0)
      gAnimal = d
      setXG2(Animal(d).x, 1)
      check Animal(d).x == 5
    block:
      let p = Box(x: 0)
      gBoxC = p
      setXC(cast[ptr int](addr p.x)[], 1)
      check p.x == 5

  test "probe A: plain ptr-formal dereference":
    let r = symexFind(sutPtrFormalDeref, tLabel("pfA"))
    echo "A: " & $r.status & " " & show(r.errors)
    let rd = symexFind(sutPtrFormalDeref, tLabel("pfA_dead"))
    echo "A dead: " & $rd.status & " " & show(rd.errors)
    check false

  test "probe A2: var ptr-formal dereference":
    let r = symexFind(sutVarPtrFormalDeref, tLabel("pfA2"))
    echo "A2: " & $r.status & " " & show(r.errors)
    let rd = symexFind(sutVarPtrFormalDeref, tLabel("pfA2_dead"))
    echo "A2 dead: " & $rd.status & " " & show(rd.errors)
    check false

  test "probe B: inheritance upcast conversion":
    let r = symexFind(sutConvInherit, tLabel("cvB"))
    echo "B: " & $r.status & " " & show(r.errors)
    let rd = symexFind(sutConvInherit, tLabel("cvB_dead"))
    echo "B dead: " & $rd.status & " " & show(rd.errors)
    check false

  test "probe C: cast lvalue inline":
    let r = symexFind(sutCastLvalue, tLabel("ccC"))
    echo "C: " & $r.status & " " & show(r.errors)
    let rd = symexFind(sutCastLvalue, tLabel("ccC_dead"))
    echo "C dead: " & $rd.status & " " & show(rd.errors)
    check false
