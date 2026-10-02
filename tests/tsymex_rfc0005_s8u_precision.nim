## RFC-0005 (soundness channels) slice S8u -- S8s's precision remainder.
##
## Six places the walker gave up on (or faulted over) code whose behaviour is
## fully determined. S8s reported them. Every expected value was probed
## against the real compiler (Nim 2.2.10, debug build) by the oracle test of
## each suite, which runs the SUT itself.
##   (1) a variant constructor naming an `else`-covered tag
##       (was `feUnsupportedExprKind`);
##   (2) a callee building a local `Table` / `HashSet`
##       (was `weInternalWalkerFault`, `lower`'s `doAssert recv.kind`);
##   (3) a callee allocating its `ref` result with `new(result)`
##       (was `weInternalWalkerFault`, "retBindEq: kind mismatch");
##   (4) a multi-variant with a `bool` discriminator
##       (was `weInternalWalkerFault`, "must be a BV kind (got svBool)");
##   (5) the zero value of a `distinct` result and of a type holding a
##       `HashSet` / `Table` (was `feUnsupportedOpHavoc`);
##   (6) `op=` on an array element (was `feUnsupportedStmtKind`);
##   (7) the walker version floor.
import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template expectSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat

template expectUnsat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxUnsat

# ---- (1) a constructor naming an else-covered tag ---------------------------------

type
  S8uK = enum u3A, u3B, u3C
  S8uVE = object
    case vk: S8uK
    of u3C: vc: int
    else: ve: int

proc elseCtor(x: int) =
  let v = S8uVE(vk: u3B, ve: x)
  if v.ve == 4 and v.vk == u3B: symexTarget("s8u_ec")
  if v.vk != u3B: symexTarget("s8u_ec_dead")

suite "S8u (1) a constructor naming an else-covered tag":
  test "oracle":
    symexCaptureBegin()
    elseCtor(4)
    let hits = symexCaptureEnd()
    check "s8u_ec" in hits

  test "an else-covered tag's constructor (was feUnsupportedExprKind)":
    let r = symexFind(elseCtor, tLabel("s8u_ec"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 4
    expectUnsat(symexFind(elseCtor, tLabel("s8u_ec_dead")))

# ---- (2) a callee building a local Table / HashSet --------------------------------

proc mkTable(n: int): Table[string, int] =
  var t: Table[string, int]
  t["a"] = n
  result = t

proc callTable(n: int) =
  let t = mkTable(n)
  if t["a"] == 5: symexTarget("s8u_tbl")
  if t["a"] != n: symexTarget("s8u_tbl_dead")

proc mkSet(n: int): HashSet[int] =
  var s: HashSet[int]
  s.incl n
  result = s

proc callSet(n: int) =
  let s = mkSet(n)
  if 3 in s: symexTarget("s8u_set")
  if s.len != 1: symexTarget("s8u_set_dead")

proc mkIntTable(n: int): Table[(int, int), int] =
  ## A shape the table theory does not back: still declined, now in-band --
  ## the RFC-0005 S8u scoped decline. RFC-0005 S8ar backs an integer key
  ## (this was `Table[int, int]`) and S8at a float one (then
  ## `Table[float, int]`); a tuple key is still unbacked.
  var t: Table[(int, int), int]
  t[(1, 1)] = n
  result = t

proc callIntTable(n: int) =
  let t = mkIntTable(n)
  if t[(1, 1)] == 5: symexTarget("s8u_itbl")

suite "S8u (2) a callee building a local Table / HashSet":
  test "oracle":
    symexCaptureBegin()
    callTable(5); callSet(3); callIntTable(5)
    let hits = symexCaptureEnd()
    check "s8u_tbl" in hits
    check "s8u_set" in hits
    check "s8u_itbl" in hits

  test "a local Table (was weInternalWalkerFault)":
    let r = symexFind(callTable, tLabel("s8u_tbl"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 5
    expectUnsat(symexFind(callTable, tLabel("s8u_tbl_dead")))

  test "a local HashSet (was weInternalWalkerFault)":
    let r = symexFind(callSet, tLabel("s8u_set"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 3
    expectUnsat(symexFind(callSet, tLabel("s8u_set_dead")))

  test "an unbacked Table[(int, int), int] declines in-band, never a walker fault":
    let r = symexFind(callIntTable, tLabel("s8u_itbl"))
    checkpoint($r.status & " " & show(r.errors))
    for e in r.errors: check e.kind != weInternalWalkerFault
    check r.status != sxUnsat
    check r.errors.len > 0

# ---- (3) a callee allocating its ref result with new(result) ----------------------

type S8uNode = ref object
  v: int
  w: int

proc mkNode(x: int): S8uNode =
  new(result)
  result.v = x

proc callNode(x: int) =
  let n = mkNode(x)
  if n.v == 9 and n.w == 0: symexTarget("s8u_nr")
  if n.w != 0: symexTarget("s8u_nr_dead")

suite "S8u (3) new(result) in a callee":
  test "oracle":
    symexCaptureBegin()
    callNode(9)
    let hits = symexCaptureEnd()
    check "s8u_nr" in hits

  test "a new(result) ref result (was weInternalWalkerFault)":
    let r = symexFind(callNode, tLabel("s8u_nr"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 9
    expectUnsat(symexFind(callNode, tLabel("s8u_nr_dead")))

# ---- (4) a multi-variant with a bool discriminator --------------------------------

type
  S8uMB = object
    case b: bool
    of true: t: int
    of false: f: int
    case k: S8uK
    of u3A: a: int
    else: e: int

proc mbParam(m: S8uMB) =
  if m.b and m.t == 3 and m.k == u3C: symexTarget("s8u_mb")
  if not m.b and m.f == 2: symexTarget("s8u_mbf")

suite "S8u (4) a multi-variant with a bool discriminator":
  test "oracle":
    symexCaptureBegin()
    mbParam(S8uMB(b: true, t: 3, k: u3C, e: 0))
    mbParam(S8uMB(b: false, f: 2, k: u3A, a: 0))
    let hits = symexCaptureEnd()
    check "s8u_mb" in hits
    check "s8u_mbf" in hits

  test "a bool axis (was weInternalWalkerFault)":
    let r = symexFind(mbParam, tLabel("s8u_mb"))
    expectSat(r)
    if r.status == sxSat:
      check reproduces(mbParam(r.witness[0]), "s8u_mb")
    let f = symexFind(mbParam, tLabel("s8u_mbf"))
    expectSat(f)
    if f.status == sxSat:
      check reproduces(mbParam(f.witness[0]), "s8u_mbf")

# ---- (5) zero values: distinct, and types holding a HashSet / Table ---------------

type S8uMeters = distinct int

proc mMaybe(x: int): S8uMeters =
  if x > 0: result = S8uMeters(x)

proc callMeters(x: int) =
  let m = mMaybe(x)
  if x <= 0 and int(m) == 0: symexTarget("s8u_dz")
  if x <= 0 and int(m) != 0: symexTarget("s8u_dz_dead")
  if x > 0 and int(m) == 6: symexTarget("s8u_dz6")

type S8uBag = object
  n: int
  s: HashSet[int]
  t: Table[string, int]

proc bagMaybe(x: int): S8uBag =
  if x > 0: result.n = x

proc callBag(x: int) =
  let b = bagMaybe(x)
  if x <= 0 and b.n == 0 and b.s.len == 0 and b.t.len == 0:
    symexTarget("s8u_bz")
  if x <= 0 and b.n != 0: symexTarget("s8u_bz_dead")

suite "S8u (5) zero values of distinct and HashSet/Table-holding results":
  test "oracle":
    check int(mMaybe(0)) == 0
    symexCaptureBegin()
    callMeters(0); callMeters(6); callBag(0)
    let hits = symexCaptureEnd()
    check "s8u_dz" in hits
    check "s8u_dz6" in hits
    check "s8u_bz" in hits

  test "an untouched distinct result is its base type's zero":
    let r = symexFind(callMeters, tLabel("s8u_dz"))
    expectSat(r)
    expectUnsat(symexFind(callMeters, tLabel("s8u_dz_dead")))
    let s = symexFind(callMeters, tLabel("s8u_dz6"))
    expectSat(s)
    if s.status == sxSat: check s.witness[0] == 6

  test "an untouched result holding a HashSet and a Table":
    let r = symexFind(callBag, tLabel("s8u_bz"))
    expectSat(r)
    expectUnsat(symexFind(callBag, tLabel("s8u_bz_dead")))

# ---- (6) op= on an array element --------------------------------------------------

proc arrSet(b: int) =
  var a = [1, 2, 3]
  a[1] = b
  if a[1] == 7 and a[0] == 1 and a[2] == 3: symexTarget("s8u_as")
  if a[0] != 1: symexTarget("s8u_as_dead")

proc arrAug(b: int) =
  var a = [1, 2, 3]
  if b > -1000 and b < 1000:
    a[0] += b
  if a[0] == 10 and a[1] == 2: symexTarget("s8u_aa")
  if a[2] != 3: symexTarget("s8u_aa_dead")

suite "S8u (6) op= on an array element":
  test "oracle":
    symexCaptureBegin()
    arrAug(9); arrSet(7)
    let hits = symexCaptureEnd()
    check "s8u_aa" in hits
    check "s8u_as" in hits

  test "an array element's = at a constant index":
    let r = symexFind(arrSet, tLabel("s8u_as"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 7
    expectUnsat(symexFind(arrSet, tLabel("s8u_as_dead")))

  test "an array element's += (was feUnsupportedStmtKind)":
    let r = symexFind(arrAug, tLabel("s8u_aa"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 9
    expectUnsat(symexFind(arrAug, tLabel("s8u_aa_dead")))

# ---- (7) walker version floor -----------------------------------------------------

suite "S8u (7) walker version":
  test "walker version is at least 169":
    check parseInt(symexWalkerVersion) >= 169
