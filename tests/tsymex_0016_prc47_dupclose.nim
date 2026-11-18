## RFC-0016 PRC-47 -- the `=dup` sink positions PRC-46 left declining: a
## `seq` of the hooked type whose length the walk does not know, a hook that
## writes a global, a `sink` parameter of a tuple or an array type, a hook
## or a field declared in another module, `except E as e`, and
## a `for` over an unlisted iterator, one whose header names a local, and a
## nested iterator or template naming one.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./prc47_dupmod

type DObj = object
  v: int
proc `=dup`(x: DObj): DObj = DObj(v: x.v + 1)
proc dTake(x: sink DObj): int = x.v

# 1. A `seq` of a length the walk does not know. Natively (Nim 2.2.10, c and
# cpp) its generated `=dup` is a loop running the element's `=dup` on each
# element in index order, never for an empty seq; a type holding a hooked
# field runs it per element through its own generated `=dup`.
proc dTakeFirst(x: sink seq[DObj]): int =
  if x.len > 0: x[0].v else: -1
proc mkSeq(k: int): seq[DObj] =
  if k > 0: @[DObj(v: k)] else: @[]
proc sl(k: int): int =
  let t = mkSeq(k)
  dTakeFirst(t) * 1000 + t.len
type DBox = object
  o: DObj
proc dTakeBS(x: sink seq[DBox]): int =
  for e in x: result = result * 10 + e.o.v
proc mkBoxSeq(k: int): seq[DBox] =
  if k > 0: @[DBox(o: DObj(v: k)), DBox(o: DObj(v: k))] else: @[]
proc bl(k: int): int =
  let t = mkBoxSeq(k)
  dTakeBS(t) + t.len * 0

# 2. A hook that writes a global: natively it runs once per element, in
# index order, so the global's final value is a fold over the elements.
var gc = 0
type DGl = object
  v: int
proc `=dup`(x: DGl): DGl =
  gc = gc * 10 + x.v
  DGl(v: x.v + 1)
proc dTakeGl(x: sink seq[DGl]): int =
  for e in x: result += e.v
proc go(k: int): int =
  gc = 0
  let t = @[DGl(v: k), DGl(v: k + 1)]
  discard dTakeGl(t) + t.len
  gc
proc mkGl(k: int): seq[DGl] =
  if k > 0: @[DGl(v: k)] else: @[]
proc gl(k: int): int =
  gc = 0
  let t = mkGl(k)
  discard dTakeGl(t) + t.len
  gc

# 3. A `sink` parameter of a tuple or an array type read after the site.
# Such a type takes `tfHasAsgn` from its components where it is made, and
# the compiler shares one type among the structurally equal ones (native,
# Nim 2.2.10, c and cpp). An alias is made at its declaration: one written
# before the component's hook moves, one after runs it, in a generic
# routine's instance (whose T is the first instantiation's: `gTL`'s
# anonymous `(DLate, int)` takes `gTE`'s `TEarly`, read on the instance) and
# a non-generic `sink` tuple alike. A `sink` array outside a generic
# routine is an object's case: moved. An anonymous one may be the first
# equal type written anywhere before it, which the walk does not read
# (`n6t(a: sink (D, int))` after D's hook moves when a `(D, int)` formal was
# written before the hook; a generic instance over `array[1, D]` likewise;
# over `(D, int)` the compiler fails its own assertion,
# `injectdestructors.nim(429, 5)`): one holding a hooked component declines.
proc tk(x: sink (DObj, int)): int = x[0].v
proc vv(x: (DObj, int)): int = x[0].v
proc tk(x: sink array[1, DObj]): int = x[0].v
proc vv(x: array[1, DObj]): int = x[0].v
type
  TEarly = (DLate, int)
  AEarly = array[1, DLate]
  DLate = object
    v: int
proc `=dup`(x: DLate): DLate = DLate(v: x.v + 1)
type DAft = object
  v: int
proc `=dup`(x: DAft): DAft = DAft(v: x.v + 1)
type
  TAft = (DAft, int)
  AAft = array[1, DAft]
proc tk(x: sink TEarly): int = x[0].v
proc vv(x: TEarly): int = x[0].v
proc tk(x: sink AEarly): int = x[0].v
proc vv(x: AEarly): int = x[0].v
proc tk(x: sink TAft): int = x[0].v
proc vv(x: TAft): int = x[0].v
proc tk(x: sink AAft): int = x[0].v
proc vv(x: AAft): int = x[0].v
proc nAft(a: sink TAft): int = tk(a) * 1000 + vv(a)
proc nEarly(a: sink TEarly): int = tk(a) * 1000 + vv(a)
proc nAnon(a: sink (DObj, int)): int = tk(a) * 1000 + vv(a)
proc nArr(a: sink array[1, DObj]): int = tk(a) * 1000 + vv(a)
proc nTA(k: int): int = nAft(TAft((DAft(v: k), 5)))
proc nTE(k: int): int = nEarly(TEarly((DLate(v: k), 5)))
proc nTU(k: int): int = nAnon((DObj(v: k), 5))
proc nAU(k: int): int = nArr([DObj(v: k)])

# 4. A hook or a field declared in another module: that module is read
# before this one's code, so its hooks are bound before anything here.
proc tk(x: sink MObj): int = x.v
proc vv(x: MObj): int = x.v
proc tk(x: sink MBox): int = x.o.v
proc vv(x: MBox): int = x.o.v
proc tk(x: sink MEarly): int = x.o.v
proc vv(x: MEarly): int = x.o.v
type LBox = object
  o: MObj
proc tk(x: sink LBox): int = x.o.v
proc vv(x: LBox): int = x.o.v
proc gq[T](a: sink T): int = tk(a) * 1000 + vv(a)
proc gTup(k: int): int = gq((DObj(v: k), 5))
proc gArr(k: int): int = gq([DObj(v: k)])
proc gTE(k: int): int = gq(TEarly((DLate(v: k), 5)))
proc gTL(k: int): int = gq((DLate(v: k), 5))
proc gAE(k: int): int = gq(AEarly([DLate(v: k)]))
proc gTA(k: int): int = gq(TAft((DAft(v: k), 5)))
proc gAA(k: int): int = gq(AAft([DAft(v: k)]))
proc gM(k: int): int = gq(MObj(v: k))
proc gMB(k: int): int = gq(MBox(o: MObj(v: k)))
proc gLB(k: int): int = gq(LBox(o: MObj(v: k)))
proc gME(k: int): int = gq(MEarly(o: MLate(v: k)))
proc mq(k: int): int =
  let a = MObj(v: k)
  let b = a
  tk(b) * 100 + a.v

# 5. `except E as e`: the binding is a `let` of the branch, read as one.
# (The walk does not bind `e` itself, so the branches do not read it.)
proc mayRaise(k: int) =
  if k == 99: raise newException(ValueError, "x")
proc x1(k: int): int =       # a read in the branch after the site: a cursor
  let a = DObj(v: k)
  let b = a
  try:
    result = dTake(b) * 100
    mayRaise(k)
  except ValueError as e:
    result = a.v + 1
proc x2(k: int): int =       # a read before the site only: owned
  let a = DObj(v: k)
  let b = a
  try:
    result = a.v
    result += dTake(b) * 100
  except ValueError as e:
    result = 7 + 1
proc x3(k: int): int =       # both in the branch, a read before: owned
  try:
    raise newException(ValueError, "x")
  except ValueError as e:
    let a = DObj(v: k)
    let b = a
    result = 1 + a.v
    result += dTake(b) * 100
proc x4(k: int): int =       # both in the branch, a read after: a cursor
  try:
    raise newException(ValueError, "x")
  except ValueError as e:
    let a = DObj(v: k)
    let b = a
    result = dTake(b) * 100 + 1
    result += a.v

# 6. Iterators and templates. A `for` over an iterator is inlined, its
# body at each `yield`; a nested template is expanded where it is used and
# its declaration is not followed; a nested iterator naming a local captures
# it as a nested routine does (`a` captured: `b` owns; `b` captured: copied).
iterator two(): int =
  yield 0
  yield 1
iterator upto(n: int): int =
  var i = 0
  while i < n:
    yield i
    inc i
proc i1(k: int): int =       # b in a two-`yield` body: each copy its own
  let a = DObj(v: k)
  for i in two():
    let b = a
    result += dTake(b)
proc i2(k: int): int =       # b in a looping body
  let a = DObj(v: k)
  for i in upto(2):
    let b = a
    result += dTake(b)
iterator twoOf(x: DObj): int =
  yield x.v
  yield x.v + 1
proc h1(k: int): int =       # a in an unlisted header, b in its body
  let a = DObj(v: k)
  for i in twoOf(a):
    let b = a
    result += dTake(b) * 100 + i
proc i5(k: int): int =       # a in a listed header after the site
  let a = DObj(v: k)
  let b = a
  result = dTake(b) * 100
  for i in 0 ..< a.v:
    result += 1
proc i6(k: int): int =       # a in an unlisted header after the site
  let a = DObj(v: k)
  let b = a
  result = dTake(b) * 100
  for i in upto(a.v):
    result += 1
proc i7(k: int): int =       # a in an unlisted header before the site
  let a = DObj(v: k)
  let b = a
  for i in upto(a.v):
    result += 1
  result += dTake(b) * 100
proc i8(k: int): int =       # a nested iterator naming a, used after
  let a = DObj(v: k)
  let b = a
  iterator inner(): int =
    yield a.v
  result = dTake(b) * 100
  for x in inner(): result += x
proc i9(k: int): int =       # a nested template naming a, used after
  let a = DObj(v: k)
  let b = a
  template tv(): int = a.v
  result = dTake(b) * 100 + tv()
proc i10(k: int): int =      # a nested template naming a, used before
  let a = DObj(v: k)
  let b = a
  template tv(): int = a.v
  result = tv()
  result += dTake(b) * 100
proc i11(k: int): int =      # a nested template naming b, unused
  let a = DObj(v: k)
  let b = a
  template tv(): int = b.v
  result = a.v
  result += dTake(b) * 100
proc i12(k: int): int =      # a nested iterator naming a, used before
  let a = DObj(v: k)
  let b = a
  iterator inner(): int =
    yield a.v
  for x in inner(): result += x
  result += dTake(b) * 100
proc i13(k: int): int =      # a closure iterator naming a
  let a = DObj(v: k)
  let b = a
  iterator inner(): int {.closure.} =
    yield a.v
  for x in inner(): result += x
  result += dTake(b) * 100
proc i14(k: int): int =      # a nested iterator naming b, used after
  let a = DObj(v: k)
  let b = a
  iterator inner(): int =
    yield b.v
  result = dTake(b) * 100 + a.v
  for x in inner(): result += x * 10
proc i15(k: int): int =      # a nested template naming b, used after
  let a = DObj(v: k)
  let b = a
  template tv(): int = b.v
  result = dTake(b) * 100 + tv() * 10
proc i16(k: int): int =      # an unlisted iterator naming neither, a after
  let a = DObj(v: k)
  let b = a
  result = dTake(b) * 100
  for i in two(): result += a.v
proc i17(k: int): int =      # an unlisted iterator naming neither, a before
  let a = DObj(v: k)
  let b = a
  for i in two(): result += a.v
  result += dTake(b) * 100

# Each entry: `hit` holds only with the native count of hooks.
proc eSeqLen(k: int) =
  if k > 50 or k < -50: return
  if sl(k) == (k + 1) * 1000 + 1 and k > 0: symexTarget("hit")
proc eSeqLenNever(k: int) =
  if k > 50 or k < -50: return
  if sl(k) == k * 1000 + 1 and k > 0: symexTarget("hit")
proc eBoxLen(k: int) =
  if k > 50 or k < -50: return
  if bl(k) == 11 * k + 11 and k > 0: symexTarget("hit")
proc eBoxLenNever(k: int) =
  if k > 50 or k < -50: return
  if bl(k) == 11 * k and k > 0: symexTarget("hit")
proc eGlobOrd(k: int) =
  if k > 50 or k < -50: return
  if go(k) == 10 * k + k + 1: symexTarget("hit")
proc eGlobOrdNever(k: int) =
  if k > 50 or k < -50: return
  if go(k) == 10 * k + 10 + k: symexTarget("hit")
proc eGlobLen(k: int) =
  if k > 50 or k < -50: return
  if gl(k) == k and k > 0: symexTarget("hit")
proc eGlobLenNever(k: int) =
  if k > 50 or k < -50: return
  if gl(k) == 0 and k > 0: symexTarget("hit")
proc eGM(k: int) =
  if k > 1000 or k < -1000: return
  if gM(k) == 2001: symexTarget("hit")
proc eGMNever(k: int) =
  if k > 1000 or k < -1000: return
  if gM(k) == 1001: symexTarget("hit")
proc eGMB(k: int) =
  if k > 1000 or k < -1000: return
  if gMB(k) == 2001: symexTarget("hit")
proc eGMBNever(k: int) =
  if k > 1000 or k < -1000: return
  if gMB(k) == 1001: symexTarget("hit")
proc eGLB(k: int) =
  if k > 1000 or k < -1000: return
  if gLB(k) == 2001: symexTarget("hit")
proc eGLBNever(k: int) =
  if k > 1000 or k < -1000: return
  if gLB(k) == 1001: symexTarget("hit")
proc eGME(k: int) =
  if k > 1000 or k < -1000: return
  if gME(k) == 1001: symexTarget("hit")
proc eGMENever(k: int) =
  if k > 1000 or k < -1000: return
  if gME(k) == 2001: symexTarget("hit")
proc eMQ(k: int) =
  if k > 50 or k < -50: return
  if mq(k) == 101 * k + 100: symexTarget("hit")
proc eMQNever(k: int) =
  if k > 50 or k < -50: return
  if mq(k) == 101 * k: symexTarget("hit")
proc eX1(k: int) =
  if k > 50 or k < -50: return
  if x1(k) == 100 * k + 100: symexTarget("hit")
proc eX1Never(k: int) =
  if k > 50 or k < -50: return
  if x1(k) == 100 * k: symexTarget("hit")
proc eX2(k: int) =
  if k > 50 or k < -50: return
  if x2(k) == 101 * k: symexTarget("hit")
proc eX2Never(k: int) =
  if k > 50 or k < -50: return
  if x2(k) == 101 * k + 100: symexTarget("hit")
proc eX3(k: int) =
  if k > 50 or k < -50: return
  if x3(k) == 101 * k + 1: symexTarget("hit")
proc eX3Never(k: int) =
  if k > 50 or k < -50: return
  if x3(k) == 101 * k + 101: symexTarget("hit")
proc eX4(k: int) =
  if k > 50 or k < -50: return
  if x4(k) == 101 * k + 101: symexTarget("hit")
proc eX4Never(k: int) =
  if k > 50 or k < -50: return
  if x4(k) == 101 * k + 1: symexTarget("hit")
proc eI5(k: int) =
  if k > 4 or k < 0: return
  if i5(k) == 101 * k + 100: symexTarget("hit")
proc eI5Never(k: int) =
  if k > 4 or k < 0: return
  if i5(k) == 101 * k: symexTarget("hit")
proc eI6(k: int) =
  if k > 4 or k < 0: return
  if i6(k) == 101 * k + 100: symexTarget("hit")
proc eI6Never(k: int) =
  if k > 4 or k < 0: return
  if i6(k) == 101 * k: symexTarget("hit")
proc eI7(k: int) =
  if k > 4 or k < 0: return
  if i7(k) == 101 * k: symexTarget("hit")
proc eI7Never(k: int) =
  if k > 4 or k < 0: return
  if i7(k) == 101 * k + 100: symexTarget("hit")
proc eI8(k: int) =
  if k > 50 or k < -50: return
  if i8(k) == 101 * k: symexTarget("hit")
proc eI8Never(k: int) =
  if k > 50 or k < -50: return
  if i8(k) == 101 * k + 100: symexTarget("hit")
proc eI9(k: int) =
  if k > 50 or k < -50: return
  if i9(k) == 101 * k + 100: symexTarget("hit")
proc eI9Never(k: int) =
  if k > 50 or k < -50: return
  if i9(k) == 101 * k: symexTarget("hit")
proc eI10(k: int) =
  if k > 50 or k < -50: return
  if i10(k) == 101 * k: symexTarget("hit")
proc eI10Never(k: int) =
  if k > 50 or k < -50: return
  if i10(k) == 101 * k + 100: symexTarget("hit")
proc eI11(k: int) =
  if k > 50 or k < -50: return
  if i11(k) == 101 * k: symexTarget("hit")
proc eI11Never(k: int) =
  if k > 50 or k < -50: return
  if i11(k) == 101 * k + 100: symexTarget("hit")
proc eI12(k: int) =
  if k > 50 or k < -50: return
  if i12(k) == 101 * k: symexTarget("hit")
proc eI12Never(k: int) =
  if k > 50 or k < -50: return
  if i12(k) == 101 * k + 100: symexTarget("hit")
proc eI13(k: int) =
  if k > 50 or k < -50: return
  if i13(k) == 101 * k: symexTarget("hit")
proc eI13Never(k: int) =
  if k > 50 or k < -50: return
  if i13(k) == 101 * k + 100: symexTarget("hit")
proc eI14(k: int) =
  if k > 50 or k < -50: return
  if i14(k) == 111 * k + 100: symexTarget("hit")
proc eI14Never(k: int) =
  if k > 50 or k < -50: return
  if i14(k) == 111 * k: symexTarget("hit")
proc eI15(k: int) =
  if k > 50 or k < -50: return
  if i15(k) == 110 * k + 100: symexTarget("hit")
proc eI15Never(k: int) =
  if k > 50 or k < -50: return
  if i15(k) == 110 * k: symexTarget("hit")
proc eI16(k: int) =
  if k > 50 or k < -50: return
  if i16(k) == 102 * k + 100: symexTarget("hit")
proc eI16Never(k: int) =
  if k > 50 or k < -50: return
  if i16(k) == 102 * k: symexTarget("hit")
proc eI17(k: int) =
  if k > 50 or k < -50: return
  if i17(k) == 102 * k: symexTarget("hit")
proc eI17Never(k: int) =
  if k > 50 or k < -50: return
  if i17(k) == 102 * k + 100: symexTarget("hit")
proc eI1(k: int) =
  if k > 50 or k < -50: return
  if i1(k) == 2 * k + 1: symexTarget("hit")
proc eI1Never(k: int) =
  if k > 50 or k < -50: return
  if i1(k) == 2 * k: symexTarget("hit")
proc eH1(k: int) =
  if k > 50 or k < -50: return
  if h1(k) == 202 * k + 101: symexTarget("hit")
proc eH1Never(k: int) =
  if k > 50 or k < -50: return
  if h1(k) == 202 * k + 1: symexTarget("hit")
proc eI2(k: int) =
  if k > 50 or k < -50: return
  if i2(k) == 2 * k: symexTarget("hit")
proc eI2Never(k: int) =
  if k > 50 or k < -50: return
  if i2(k) == 2 * k + 1: symexTarget("hit")
proc eTup(k: int) =
  if k > 1000 or k < -1000: return
  if gTup(k) == 2001: symexTarget("hit")
proc eTupNever(k: int) =
  if k > 1000 or k < -1000: return
  if gTup(k) == 1001: symexTarget("hit")
proc eArr(k: int) =
  if k > 1000 or k < -1000: return
  if gArr(k) == 2001: symexTarget("hit")
proc eArrNever(k: int) =
  if k > 1000 or k < -1000: return
  if gArr(k) == 1001: symexTarget("hit")
proc eTE(k: int) =
  if k > 1000 or k < -1000: return
  if gTE(k) == 1001: symexTarget("hit")
proc eTENever(k: int) =
  if k > 1000 or k < -1000: return
  if gTE(k) == 2001: symexTarget("hit")
proc eTL(k: int) =
  if k > 1000 or k < -1000: return
  if gTL(k) == 1001: symexTarget("hit")
proc eTLNever(k: int) =
  if k > 1000 or k < -1000: return
  if gTL(k) == 2001: symexTarget("hit")
proc eAE(k: int) =
  if k > 1000 or k < -1000: return
  if gAE(k) == 1001: symexTarget("hit")
proc eAENever(k: int) =
  if k > 1000 or k < -1000: return
  if gAE(k) == 2001: symexTarget("hit")
proc eTA(k: int) =
  if k > 1000 or k < -1000: return
  if gTA(k) == 2001: symexTarget("hit")
proc eTANever(k: int) =
  if k > 1000 or k < -1000: return
  if gTA(k) == 1001: symexTarget("hit")
proc eAA(k: int) =
  if k > 1000 or k < -1000: return
  if gAA(k) == 2001: symexTarget("hit")
proc eAANever(k: int) =
  if k > 1000 or k < -1000: return
  if gAA(k) == 1001: symexTarget("hit")
proc eNTA(k: int) =
  if k > 1000 or k < -1000: return
  if nTA(k) == 2001: symexTarget("hit")
proc eNTANever(k: int) =
  if k > 1000 or k < -1000: return
  if nTA(k) == 1001: symexTarget("hit")
proc eNTE(k: int) =
  if k > 1000 or k < -1000: return
  if nTE(k) == 1001: symexTarget("hit")
proc eNTENever(k: int) =
  if k > 1000 or k < -1000: return
  if nTE(k) == 2001: symexTarget("hit")
proc eNTU(k: int) =
  if k > 1000 or k < -1000: return
  if nTU(k) == 2001: symexTarget("hit")
proc eNTUNever(k: int) =
  if k > 1000 or k < -1000: return
  if nTU(k) == 1001: symexTarget("hit")
proc eNAU(k: int) =
  if k > 1000 or k < -1000: return
  if nAU(k) == 1001: symexTarget("hit")
proc eNAUNever(k: int) =
  if k > 1000 or k < -1000: return
  if nAU(k) == 2001: symexTarget("hit")

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")

template exact(hitP, neverP: untyped) =
  check pinExact(hitP, dCell, domain = idom).status == sxSat
  check pinExact(neverP, dCell, domain = idom).status == sxUnsat

template declined(p: untyped) =
  pinDecline(p, dCell, feGlobalRouteUnproved, needle = "=dup")

suite "PRC-47":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 427

  test "a seq of a length the walk does not know":
    check native(eSeqLen(1)) == "hit"
    check native(eBoxLen(1)) == "hit"
    exact(eSeqLen, eSeqLenNever)
    exact(eBoxLen, eBoxLenNever)

  test "a hook that writes a global: a fold over the elements":
    check native(eGlobOrd(1)) == "hit"
    check native(eGlobLen(1)) == "hit"
    exact(eGlobOrd, eGlobOrdNever)
    exact(eGlobLen, eGlobLenNever)

  test "a sink tuple or array: an alias by where it is declared":
    for e in [eTE, eTL, eAE, eTA, eAA, eNTA, eNTE, eNAU]:
      check native(e(1)) == "hit"
    exact(eTE, eTENever)
    exact(eTL, eTLNever)
    exact(eAE, eAENever)
    exact(eTA, eTANever)
    exact(eAA, eAANever)
    exact(eNTA, eNTANever)
    exact(eNTE, eNTENever)
    exact(eNAU, eNAUNever)
  test "a sink tuple or array of an anonymous hooked type declines":
    check native(eTup(1)) == "hit"
    check native(eArr(1)) == "hit"
    check native(eNTU(1)) == "hit"
    declined(eTup)
    declined(eArr)
    declined(eNTU)

  test "a hook or a field declared in another module":
    check native(eGM(1)) == "hit"
    check native(eGMB(1)) == "hit"
    check native(eGLB(1)) == "hit"
    check native(eGME(1)) == "hit"
    check native(eMQ(1)) == "hit"
    exact(eGM, eGMNever)
    exact(eGMB, eGMBNever)
    exact(eGLB, eGLBNever)
    exact(eGME, eGMENever)
    exact(eMQ, eMQNever)

  test "except E as e":
    check native(eX1(1)) == "hit"
    check native(eX2(1)) == "hit"
    check native(eX3(1)) == "hit"
    check native(eX4(1)) == "hit"
    exact(eX1, eX1Never)
    exact(eX2, eX2Never)
    exact(eX3, eX3Never)
    exact(eX4, eX4Never)

  test "a for over an iterator, a nested iterator or template":
    for e in [eI5, eI6, eI7, eI8, eI9, eI10, eI11, eI12, eI13, eI14, eI15,
              eI16, eI17, eI1, eI2]:
      check native(e(1)) == "hit"
    exact(eI5, eI5Never)
    exact(eI6, eI6Never)
    exact(eI7, eI7Never)
    exact(eI8, eI8Never)
    exact(eI9, eI9Never)
    exact(eI10, eI10Never)
    exact(eI11, eI11Never)
    exact(eI12, eI12Never)
    exact(eI13, eI13Never)
    exact(eI14, eI14Never)
    exact(eI15, eI15Never)
    exact(eI16, eI16Never)
    exact(eI17, eI17Never)

  test "b in an unlisted iterator's body declines":
    # Natively each inlined copy of the body is classified on its own: two
    # `yield`s give `b`'s first copy a cursor (copied) and its second an
    # owner (moved), one written site with two classifications; the same
    # with the header naming `a` (`h1`). The walk inlines the body at each
    # `yield`, but a site's classification is keyed by where it is written.
    check native(eH1(1)) == "hit"
    declined(eI1)
    declined(eI2)
    declined(eH1)
