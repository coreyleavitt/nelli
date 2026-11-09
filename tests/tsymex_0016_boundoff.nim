## RFC-0016 PRC-07 (bound half). This file builds with `--boundChecks:off`
## (its `.nim.cfg`). Nim then emits no check on `s[i]` / `a[i]` of a seq,
## string, openArray or array: a plain C subscript, so an index outside the
## container reads or writes memory the object does not own, which is
## undefined. The walker answers it on the definedness axis (row
## `index/unchecked`, `ubArrayOutOfBounds`): the in-bounds side is exact and
## trusted, the out-of-bounds side halts at the access and is an
## `UndefinedFinding` with its site. It is not an `IndexDefect` (a checked
## build's answer, pinned in `tsymex_0016_rangeoff` and the index suites) and
## not a `feCheckOption` decline of every routine (what a bound-checks-off
## build used to do).
##
## Native, read from the generated C of the pinned toolchain (c backend,
## `--boundChecks:off`): a seq element is `s.p->data[i]`, an openArray's
## `s[i]`, a string's `s.p->data[i]`, an array's `a[(i) - 0]`; no comparison
## against a length is emitted for any of them. gcc's `-fsanitize=bounds`
## bounds an array OBJECT (a global or local, never a parameter, which decays
## to a pointer); a seq's, an openArray's and a string's elements are heap
## memory behind a pointer and only AddressSanitizer over `malloc`
## (`-d:useMalloc`) sees them. The probe (`ubsan_support.indexProbeSrc`) is
## built both ways and the table's row is held against each.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/definedness
import nelli/smt/errorkind
import ./s8cu_helpers
import ./ubsan_support

const bk = cellKey(axBuild, "boundChecks=off")
const ik = cellKey(axDefinedness, "index/unchecked")

proc sutSeqRead(v: int) =
  let s = @[10, 20, 30]
  if s[v] == 30: symexTarget("hit")

proc sutSeqWrite(v: int) =
  var s = @[1, 2, 3]
  s[v] = 9
  if s[2] == 9 and v == 2: symexTarget("hit")

proc sutArrRead(v: int) =
  var a: array[5, int]
  a[3] = 7
  if a[v] == 7: symexTarget("hit")

proc sutArrWrite(v: int) =
  var a: array[5, int]
  a[v] = 7
  if a[4] == 7: symexTarget("hit")

proc sutStrRead(v: int) =
  let s = "abc"
  if s[v] == 'c': symexTarget("hit")

proc pick(a: openArray[int]; i: int): int = a[i]

proc sutOpenArray(v: int) =
  let s = @[10, 20, 30]
  if pick(s, v) == 20: symexTarget("hit")

proc sutPop(v: int) =
  var s: seq[int]
  if v > 0: s.add v
  discard s.pop()
  if v > 0: symexTarget("hit")

# The label is past the access and reachable only by an index outside the
# container: that side is undefined, so the access halts.
proc sutSeqOob(v: int) =
  var s = @[1, 2, 3]
  s[v] = 1
  if v < 0 or v > 2: symexTarget("hit")

proc sutSeqReadOob(v: int) =
  let s = @[1, 2, 3]
  let x = s[v]
  if x > 0 and (v < 0 or v > 2): symexTarget("hit")

proc sutArrOob(v: int) =
  var a: array[5, int]
  a[v] = 1
  if v < 0 or v > 4: symexTarget("hit")

proc sutStrOob(v: int) =
  let s = "abc"
  let c = s[v]
  if c == 'z' and (v < 0 or v > 2): symexTarget("hit")

proc sutOaOob(v: int) =
  let s = @[10, 20, 30]
  let x = pick(s, v)
  if x > 0 and (v < 0 or v > 2): symexTarget("hit")

proc sutPopEmpty(v: int) =
  var s: seq[int]
  discard s.pop()
  if v == 1: symexTarget("hit")

proc sutGuarded(v: int) =
  let s = @[10, 20, 30]
  if v >= 0 and v < 3:
    if s[v] == 30: symexTarget("hit")

suite "PRC-07: --boundChecks:off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 306

  test "the build has the bound check off and the others on":
    check coBound notin buildSemantics.checks
    check coRange in buildSemantics.checks
    check coOverflow in buildSemantics.checks

  test "in-bounds witnesses are exact and trusted (seq, array, string)":
    for (name, r) in [("seq read", pinExact(sutSeqRead, bk,
                         domain = sampled([2, 0, 1]))),
                      ("seq write", pinExact(sutSeqWrite, bk,
                         domain = sampled([2, 0, 1]))),
                      ("array read", pinExact(sutArrRead, bk,
                         domain = sampled([3, 0, 4]))),
                      ("string read", pinExact(sutStrRead, bk,
                         domain = sampled([2, 0, 1])))]:
      checkpoint name
      check r.status == sxSat
      check r.trusted

  test "an array write is exact when it reaches the label":
    let r = pinExact(sutArrWrite, bk, domain = sampled([4, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "openArray and pop are exact in bounds":
    let r = pinExact(sutOpenArray, bk, domain = sampled([1, 0, 2]))
    check r.status == sxSat
    check r.trusted
    let q = pinExact(sutPop, bk, domain = sampled([1, 5]))
    check q.status == sxSat
    check q.trusted

  test "a guard leaves no halt":
    let r = pinExact(sutGuarded, bk, domain = sampled([-1, 0, 2, 3, 99]))
    check r.status == sxSat
    check r.trusted
    check symexFind(sutGuarded, tLabel("hit")).undefined.len == 0

  test "a seq write outside the seq halts as undefined":
    pinDecline(sutSeqOob, ik, ubArrayOutOfBounds, excluding = {feCheckOption})

  test "a seq read outside the seq halts as undefined":
    pinDecline(sutSeqReadOob, ik, ubArrayOutOfBounds,
               excluding = {feCheckOption})

  test "an array access outside the array halts as undefined":
    pinDecline(sutArrOob, ik, ubArrayOutOfBounds, excluding = {feCheckOption})

  test "a string read outside the string halts as undefined":
    pinDecline(sutStrOob, ik, ubArrayOutOfBounds, excluding = {feCheckOption})

  test "an openArray read outside it halts as undefined":
    pinDecline(sutOaOob, ik, ubArrayOutOfBounds, excluding = {feCheckOption})

  test "pop of an empty seq halts as undefined":
    pinDecline(sutPopEmpty, ik, ubArrayOutOfBounds,
               excluding = {feCheckOption})

  test "no IndexDefect is reachable: an exact unsat":
    let r = symexFind(sutSeqRead, tRaisedExn("IndexDefect"))
    checkpoint show(r.errors)
    check r.status != sxRaised
    check not r.errors.named(feCheckOption)

  test "the out-of-bounds side is a finding with its site, the run stays trusted":
    let r = symexFind(sutSeqRead, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 2
    check r.trusted
    check not r.errors.named(feCheckOption)
    check r.undefined.len == 1
    check r.undefined[0].kind == UbKind(ubArrayOutOfBounds)
    check "no bound check emitted" in r.undefined[0].site
    check "tsymex_0016_boundoff" in r.undefined[0].site
    check r.undefined[0].witness[0] notin 0 .. 2

  test "tUndefined asks for the out-of-bounds input (seq write, array)":
    for r in [symexFind(sutSeqOob, tUndefined({UbKind(ubArrayOutOfBounds)})),
              symexFind(sutArrOob, tUndefined({UbKind(ubArrayOutOfBounds)}))]:
      check r.status == sxSat
      check not r.trusted
      check r.soundness.undefinedKinds == {UbKind(ubArrayOutOfBounds)}
    let w = symexFind(sutSeqOob, tUndefined({UbKind(ubArrayOutOfBounds)}))
    check w.witness[0] notin 0 .. 2
    let a = symexFind(sutArrOob, tUndefined({UbKind(ubArrayOutOfBounds)}))
    check a.witness[0] notin 0 .. 4

suite "PRC-07: index/unchecked against C (boundChecks:off)":
  when defined(windows):
    test "no UBSan or ASan on this toolchain: the cell is declared, not run":
      skipCell(ik, "UBSan and AddressSanitizer do not exist for mingw gcc " &
        "or MSVC; the cell is pinned by the walker half and by the Linux " &
        "legs' -fsanitize=bounds and -fsanitize=address runs")
  else:
    func expectOf(outside: bool): UbExpect =
      if outside and admitDefined(aoIndex, ocUncheckedAccess,
                                  dsIndex).payload[dpChecked].kind ==
                     dkUndefined: ueTrip
      else: ueClean

    test "arrays against -fsanitize=bounds (an array object, by int index)":
      let p = buildIndexProbe("boundoff-ubsan",
                              indexBoundsFlags(["--boundChecks:off"]))
      defer: dispose(p)
      var cases: seq[UbCase]
      for k in [-1, 0, 5, 10, 11, 300]:
        let outside = k < 0 or k > 10
        for op in ["rd", "wr"]:
          cases.add UbCase(ty: "arrI", op: op, a: cast[uint64](int64(k)),
                           b: 0, expect: expectOf(outside), cond: outside)
      pinUbsanCell(ik, p, cases)

    test "seq, openArray and string against -fsanitize=address (-d:useMalloc)":
      let p = buildIndexProbe("boundoff-asan",
                              indexAsanFlags(["--boundChecks:off"]))
      defer: dispose(p)
      var cases: seq[UbCase]
      # Positive indexes just past the end: a negative one reads the block's
      # own header (inside the allocation) and a far one may land in another
      # live chunk, neither of which the sanitizer can call out of bounds.
      for k in [0, 1, 2, 3, 4]:
        let outside = k > 2
        for (ty, op) in [("seq", "rd"), ("seq", "wr"), ("oa", "rd")]:
          cases.add UbCase(ty: ty, op: op, a: cast[uint64](int64(k)), b: 0,
                           expect: expectOf(outside), cond: outside)
      # A string keeps a terminator after its last byte, so `s[len]` reads a
      # defined NUL natively where the walker (conservatively) halts: the
      # native cases skip it and use 4 and up.
      for k in [0, 1, 2, 5, 6]:
        let outside = k > 2
        for op in ["rd", "wr"]:
          cases.add UbCase(ty: "str", op: op, a: cast[uint64](int64(k)),
                           b: 0, expect: expectOf(outside), cond: outside)
      pinUbsanCell(ik, p, cases)
