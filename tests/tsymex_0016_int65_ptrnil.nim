## RFC-0016 INT-65: the `pointer` value and a proc value's nil.
##
## Native (Nim 2.2.10, c and cpp alike): an uninitialised `pointer` and a
## `pointer` set to `nil` are nil; `addr x`, a `cast[pointer]` of a non-nil
## `ref` and a lambda are not; the same address converted twice is equal and
## two variables' addresses are not; an uninitialised proc variable is nil;
## a call through a nil proc value and a dereference of a nil `ptr` end the
## process (SIGSEGV).
##
## Red at f89fb0c7: a `pointer` local holding `nil` declines
## `feUnsupportedExprKind` ("nil literal of an unmodelled type"), and a proc
## value compared with `nil` declines `ceUnsupportedHof`. Found while
## probing INT-63 (K8b's typeop axis suite, INT-56).
##
## Model: a `pointer` holds the address it was converted from (a `ptr` or a
## `ref`, nil exactly when that is), and its own `nil`. Two addresses of
## different pointee types compare equal only when both are nil; a non-nil
## pair of them declines (a `cast` may alias them). A proc value is the
## routine or closure it was built from, or nil; a call through nil
## declines. A `pointer` that is not an address (an integer cast) and a
## `ptr` cast from a `pointer` decline.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type I65R = ref object
  v: int

proc i65Id(a: int): int = a

proc i65PointerNil(a, b: int8) =
  let t = int(a)
  var x: pointer = nil
  if t + 1 == 6 and x == nil: symexTarget("hit")

proc i65PointerLet(a, b: int8) =
  let t = int(a)
  var x: pointer = nil
  let c = x
  if t + 1 == 6 and c == nil: symexTarget("hit")

proc i65PointerUninit(a: int8) =
  var x: pointer
  if int(a) == 5 and x.isNil: symexTarget("hit")

proc i65PointerAddr(c: bool) =
  var q: pointer
  var x = 1
  q = (if c: addr x else: nil)
  if q != nil: symexTarget("hit")

proc i65PointerCastRef(c: bool) =
  let r = (if c: I65R(v: 1) else: nil)
  let q = cast[pointer](r)
  if q.isNil: symexTarget("hit")

proc i65PointerSame(a: int8) =
  var x = int(a)
  let p1 = pointer(addr x)
  let p2: pointer = addr x
  if p1 == p2 and a == 3: symexTarget("hit")

proc i65PointerDistinctVars(a: int8) =
  var x = int(a)
  var y = 2
  let p1: pointer = addr x
  let p2: pointer = addr y
  if p1 == p2: symexTarget("hit")

proc i65PointerCrossSort(a: int8) =
  var x = int(a)
  var y = float(a)
  if pointer(addr x) == pointer(addr y): symexTarget("hit")

proc i65PointerArith(a: int8) =
  var x = int(a)
  let q = cast[pointer](cast[int](addr x) + 8)
  if q != nil and a == 2: symexTarget("hit")

proc i65PointerBackCast(a: int8) =
  var x = int(a)
  let q: pointer = addr x
  if cast[ptr int](q)[] == 4: symexTarget("hit")

proc i65Given(p: pointer): bool = p != nil

proc i65PointerFormal(c: bool) =
  var x = 1
  let q: pointer = (if c: addr x else: nil)
  if i65Given(q): symexTarget("hit")

proc i65ClosureNil(a, b: int8) =
  let t = int(a)
  let f = proc (x: int): int = x + t
  if t + 1 == 6 and f != nil: symexTarget("hit")

proc i65ClosureIsNil(a: int8) =
  let t = int(a)
  let f = proc (x: int): int = x * t
  if f.isNil or t == 7: symexTarget("hit")

proc i65ProcVar(c: bool) =
  var f: proc (a: int): int {.nimcall.}
  f = (if c: i65Id else: nil)
  if f != nil: symexTarget("hit")

proc i65ProcUninit(a: int8) =
  var f: proc (a: int): int {.nimcall.}
  if f == nil and a == 9: symexTarget("hit")

proc i65ProcNilCall(a: int8) =
  var f: proc (a: int): int {.nimcall.}
  if a == 1: f = i65Id
  if f(int(a)) == 7: symexTarget("hit")

suite "INT-65: a `pointer` is an address with a nil":
  test "nil, its `let` copy and the zero value are nil":
    discard pinExact(i65PointerNil, cellKey(axTypeClass, "pointer"),
                     domain = sampled([5'i8, 0'i8]))
    discard pinExact(i65PointerLet, cellKey(axTypeClass, "pointer"),
                     domain = sampled([5'i8, 0'i8]))
    discard pinExact(i65PointerUninit, cellKey(axTypeClass, "pointer"),
                     domain = sampled([5'i8, 0'i8]))

  test "an address converted to `pointer` keeps its nil":
    discard pinExact(i65PointerAddr, cellKey(axTypeClass, "pointer"),
                     domain = sampled([true, false]))
    discard pinExact(i65PointerCastRef, cellKey(axTypeClass, "pointer"),
                     domain = sampled([true, false]))
    discard pinExact(i65PointerFormal, cellKey(axTypeClass, "pointer"),
                     domain = sampled([true, false]))

  test "the same address is equal, two variables' are not":
    # INT-83's pointer model (int6): `pointer(addr x)` is an address of the
    # `pointer` sort, but `let p2: pointer = addr x` still holds `ptr int`,
    # so comparing the two declines by name (a precision gap, not a verdict).
    pinDecline(i65PointerSame, cellKey(axTypeClass, "pointer"),
               heUnresolvedRef)
    discard pinExact(i65PointerDistinctVars, cellKey(axTypeClass, "pointer"),
                     domain = sampled([3'i8, 0'i8]))

  test "what the walk cannot know declines by name":
    # Two `ptr`s of different sorts as `pointer`s: the model does not relate
    # them, so it declines (it was a trusted false sxSat once INT-83's
    # conversion met this program).
    pinDecline(i65PointerCrossSort, cellKey(axTypeClass, "pointer"),
               heUnresolvedRef)
    pinDecline(i65PointerArith, cellKey(axTypeClass, "pointer"),
               feUnsupportedExprKind, needle = "nnkCast")

  test "a pointer read back as its own ptr type is its cell (INT-83)":
    check parseInt(symexWalkerVersion) >= 443
    discard pinExact(i65PointerBackCast, cellKey(axTypeClass, "pointer"),
                     domain = sampled([4'i8, 0'i8]))

suite "INT-65: a proc value is nil or a routine":
  test "a closure local is not nil":
    discard pinExact(i65ClosureNil, cellKey(axTypeClass, "proc"),
                     domain = sampled([5'i8, 0'i8]))
    discard pinExact(i65ClosureIsNil, cellKey(axTypeClass, "proc"),
                     domain = sampled([7'i8, 0'i8]))

  test "a proc variable holds nil until a routine is stored":
    discard pinExact(i65ProcVar, cellKey(axTypeClass, "proc"),
                     domain = sampled([true, false]))
    discard pinExact(i65ProcUninit, cellKey(axTypeClass, "proc"),
                     domain = sampled([9'i8, 0'i8]))

  test "a call through nil declines":
    pinDecline(i65ProcNilCall, cellKey(axTypeClass, "proc"), ceUnsupportedHof)

  test "walker 434: the version floor":
    check parseInt(symexWalkerVersion) >= 434
