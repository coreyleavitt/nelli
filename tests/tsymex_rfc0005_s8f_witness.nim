## RFC-0005 (soundness channels) slice S8f -- a clean `sxSat` whose witness
## reproduces the target. Walker 153 -> 154.
##
## S8e found `proc f(t: Table[string, int])` with target `t.len == 2`
## returning a CLEAN `sxSat` whose witness rendered `{:}`. A clean `sxSat` is
## the engine's strongest claim, and it was false twice over:
##   (a) the MODEL. `Table`'s and `HashSet`'s `len` was a free integer in
##       `[0, 1024]`, never tied to the present/member array. A model could
##       say `len == 0` and `hasKey("a")` at once -- no real table does that,
##       so `t.len == 0 and t.hasKey("a")` was a false `sxSat`. Now every
##       check asserts, for each allocated table/set, `len >=` the number of
##       DISTINCT present keys among every key term the run selected at. That
##       is a fact about every real table, so it prunes no real input (never
##       a false `sxUnsat`), and it makes every model realizable: the present
##       term keys plus `len - count` keys no term names.
##   (b) the EXTRACTOR. A table's keys came from a static scan of string
##       LITERALS applied to a top-level param only, and `len` was ignored:
##       `{:}` for `len == 2`, for a symbolic key (`t.hasKey(k)`), and for a
##       table inside an object field. A set's `len` was ignored the same
##       way, and a seq was cut at 64 elements. Now a table/set renders the
##       present values of the run's key terms plus fresh fill up to `len`,
##       and a seq renders all `len` elements.
## Every `sxSat` below is checked by RUNNING the SUT on the witness.
##   (c) the other containers, audited: `string` (Z3's own `str.len`, sound
##       and faithful), `OrderedTable` / `CountTable` (not modelled: declined
##       with `feUnsupportedParamType`, never a claim).
##   (d) the walker version floor.
##   (e) found by replaying EVERY clean `sxSat` of the suite against the real
##       SUT (an audit, not a shipped mechanism): a discriminator assignment
##       that changes the object's branch raises `FieldDefect` in Nim and was
##       modelled as a legal zero-initialising transition, so its witness
##       started on the wrong branch; and a `range` discriminator's `else:`
##       arm rendered `kind: 0` (no enum tags to render its values from).
##   The same audit found `seq`/`array` of `ref T` rendering every element as
##       a fresh default cell; each element now renders its own cell -- nil,
##       an earlier element it aliases, or its observed fields -- in (b).
import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (a)/(b) Table[string, int] ----------------------------------------------

proc tLen2(t: Table[string, int]) =
  if t.len == 2:
    symexTarget("s8f_t_len2")

proc tLen0Key(t: Table[string, int]) =
  if t.len == 0 and t.hasKey("a"):
    symexTarget("s8f_t_len0key")

proc tLen1TwoKeys(t: Table[string, int]) =
  if t.len == 1 and t.hasKey("a") and t.hasKey("b"):
    symexTarget("s8f_t_len1twokeys")

proc tLen1SymKeys(t: Table[string, int]; j, k: string) =
  ## Two symbolic keys: `len == 1` holds only when they are the same string.
  if t.len == 1 and t.hasKey(j) and t.hasKey(k) and j != k:
    symexTarget("s8f_t_len1symkeys")

proc tSymKey(t: Table[string, int]; k: string) =
  if t.hasKey(k) and t[k] == 3 and t.len == 2:
    symexTarget("s8f_t_symkey")

proc tDel(t: Table[string, int]) =
  var u = t
  u.del("a")
  if t.hasKey("a") and u.len == 0:
    symexTarget("s8f_t_del")

proc tSetGrow(t: Table[string, int]) =
  ## `t` holds "b"; writing "a" gives `len == 1` only if "a" was present too
  ## -- which, with "b" also present, needs `t.len >= 2`.
  var u = t
  u["a"] = 1
  if t.hasKey("b") and u.len == 1:
    symexTarget("s8f_t_setgrow")

type Box = object
  t: Table[string, int]

proc tField(b: Box) =
  if b.t.hasKey("a") and b.t["a"] == 3 and b.t.len == 3:
    symexTarget("s8f_t_field")

suite "S8f (a)/(b) Table[string, int]: len is tied to the key set":
  test "len == 2: the witness has two entries and reproduces":
    let r = symexFind(tLen2, tLabel("s8f_t_len2"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 2
    check reproduces(tLen2(r.witness[0]), "s8f_t_len2")

  test "len == 0 with a present key is unreachable (was a false sxSat)":
    let r = symexFind(tLen0Key, tLabel("s8f_t_len0key"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "len == 1 with two distinct present literal keys is unreachable":
    let r = symexFind(tLen1TwoKeys, tLabel("s8f_t_len1twokeys"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "len == 1 with two present symbolic keys that differ is unreachable":
    let r = symexFind(tLen1SymKeys, tLabel("s8f_t_len1symkeys"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "a symbolic key renders, and len fills":
    let r = symexFind(tSymKey, tLabel("s8f_t_symkey"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 2
    check r.witness[0].getOrDefault(r.witness[1], -1) == 3
    check reproduces(tSymKey(r.witness[0], r.witness[1]), "s8f_t_symkey")

  test "del: the witness holds exactly the deleted key":
    let r = symexFind(tDel, tLabel("s8f_t_del"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 1 and r.witness[0].hasKey("a")
    check reproduces(tDel(r.witness[0]), "s8f_t_del")

  test "[]= on a table holding another key cannot leave len == 1":
    let r = symexFind(tSetGrow, tLabel("s8f_t_setgrow"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "a table inside an object field renders its keys and len":
    let r = symexFind(tField, tLabel("s8f_t_field"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].t.len == 3 and r.witness[0].t.getOrDefault("a") == 3
    check reproduces(tField(r.witness[0]), "s8f_t_field")

# ---- (a)/(b) HashSet[int] ----------------------------------------------------

proc sLen3(s: HashSet[int]) =
  if s.len == 3:
    symexTarget("s8f_s_len3")

proc sLen0Mem(s: HashSet[int]) =
  if s.len == 0 and 4 in s:
    symexTarget("s8f_s_len0mem")

proc sInclGrow(s: HashSet[int]) =
  ## `s` holds 5; including 4 cannot give `len == 1`.
  var u = s
  u.incl 4
  if 5 in s and u.len == 1:
    symexTarget("s8f_s_inclgrow")

proc sSymMem(s: HashSet[int]; x: int) =
  if x > 100 and x in s and s.card == 2:
    symexTarget("s8f_s_symmem")

suite "S8f (a)/(b) HashSet[int]: len is tied to the member set":
  test "len == 3: the witness has three members and reproduces":
    let r = symexFind(sLen3, tLabel("s8f_s_len3"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 3
    check reproduces(sLen3(r.witness[0]), "s8f_s_len3")

  test "len == 0 with a member is unreachable (was a false sxSat)":
    let r = symexFind(sLen0Mem, tLabel("s8f_s_len0mem"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "incl on a set holding another member cannot leave len == 1":
    let r = symexFind(sInclGrow, tLabel("s8f_s_inclgrow"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "a symbolic member renders, and card fills":
    let r = symexFind(sSymMem, tLabel("s8f_s_symmem"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 2 and r.witness[1] in r.witness[0]
    check reproduces(sSymMem(r.witness[0], r.witness[1]), "s8f_s_symmem")

# ---- (b) seq: every element renders -----------------------------------------

proc qLen100(s: seq[int]) =
  if s.len == 100 and s[99] == 7:
    symexTarget("s8f_q_len100")

type Node = ref object
  v: int

proc qRefLen70(s: seq[Node]) =
  if s.len == 70 and s[69] != nil and s[69].v == 3:
    symexTarget("s8f_q_reflen70")

proc qRefNil(s: seq[Node]) =
  if s.len == 2 and s[0] == nil and s[1] != nil and s[1].v == 4:
    symexTarget("s8f_q_refnil")

proc qRefAlias(s: seq[Node]) =
  if s.len == 2 and s[0] != nil and s[0] == s[1]:
    symexTarget("s8f_q_refalias")

proc aRef(a: array[2, Node]) =
  if a[0] == nil and a[1] != nil and a[1].v == 6:
    symexTarget("s8f_a_ref")

suite "S8f (b) seq: the witness is not cut at 64 elements":
  test "seq[int] of len 100":
    let r = symexFind(qLen100, tLabel("s8f_q_len100"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 100 and r.witness[0][99] == 7
    check reproduces(qLen100(r.witness[0]), "s8f_q_len100")

  test "seq[ref T] of len 70: the 70th cell renders":
    let r = symexFind(qRefLen70, tLabel("s8f_q_reflen70"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 70
    check reproduces(qRefLen70(r.witness[0]), "s8f_q_reflen70")

  test "seq[ref T]: a nil element renders nil, a live one its fields":
    let r = symexFind(qRefNil, tLabel("s8f_q_refnil"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(qRefNil(r.witness[0]), "s8f_q_refnil")

  test "seq[ref T]: two elements at one address render as one ref":
    let r = symexFind(qRefAlias, tLabel("s8f_q_refalias"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(qRefAlias(r.witness[0]), "s8f_q_refalias")

  test "array[N, ref T]: nil and a live cell's fields render":
    let r = symexFind(aRef, tLabel("s8f_a_ref"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check reproduces(aRef(r.witness[0]), "s8f_a_ref")

# ---- (c) the other containers, audited --------------------------------------

proc strLen100(s: string) =
  if s.len == 100 and s[99] == 'z':
    symexTarget("s8f_str_len100")

proc oLen2(t: OrderedTable[string, int]) =
  if t.len == 2:
    symexTarget("s8f_o_len2")

proc cLen2(t: CountTable[string]) =
  if t.len == 2:
    symexTarget("s8f_c_len2")

suite "S8f (c) the other container models":
  test "string: len is Z3's own str.len, and the witness reproduces":
    let r = symexFind(strLen100, tLabel("s8f_str_len100"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 100
    check reproduces(strLen100(r.witness[0]), "s8f_str_len100")

  test "OrderedTable is not modelled: declined, never a claim":
    let r = symexFind(oLen2, tLabel("s8f_o_len2"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "CountTable is not modelled: declined, never a claim":
    let r = symexFind(cLen2, tLabel("s8f_c_len2"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

# ---- (e) variant witnesses: found by replaying every clean sxSat -------------

type
  S8fTag = range[0..10]
  S8fRangeObj = object
    case kind: S8fTag
    of 1: a: int
    of 2: b: int
    else: e: int

proc eRangeElse(v: S8fRangeObj) =
  if v.kind == 5 and v.e == 42:
    symexTarget("s8f_e_rangeelse")

type
  S8fK = enum sA, sB, sC
  S8fV = object
    shared: int
    case kind: S8fK
    of sA, sC: a: int
    of sB: b: int

proc ePlainSurvives(x: var S8fV) =
  if x.shared == 42:
    x.kind = sB
    if x.shared == 42:
      symexTarget("s8f_e_plain")

proc eUncond(x: var S8fV) =
  x.kind = sB
  symexTarget("s8f_e_uncond")

proc eLocalChange() =
  var v = S8fV(kind: sA, a: 1)
  v.kind = sB
  symexTarget("s8f_e_local")

proc eCarry(x: var S8fV) =
  ## `of sA, sC:` is ONE branch: `kind = sC` keeps `a`.
  if x.kind == sA and x.a == 5:
    x.kind = sC
    if x.a != 5:
      symexTarget("s8f_e_carry")

proc eSym(x: var S8fV; t: S8fK) =
  x.kind = t
  if x.kind == sB:
    symexTarget("s8f_e_sym")

type
  S8fOp = enum opR, opW
  S8fPkt = object
    tag: int
    case op: S8fOp
    of opR: rq: int
    of opW: wq: float

proc eCtorFresh(b: byte) =
  ## A runtime discriminator in constructor syntax sets no arm field, so
  ## every arm field is its type's default -- `rq` is 0, never 777.
  let o = if b == 1'u8: opR else: opW
  let p = S8fPkt(op: o, tag: 3)
  if p.op == opR and p.rq == 777:
    symexTarget("s8f_e_ctor777")

proc eCtorZero(b: byte) =
  let o = if b == 1'u8: opR else: opW
  let p = S8fPkt(op: o)
  if p.op == opW and p.wq == 0.0 and p.tag == 0:
    symexTarget("s8f_e_ctorzero")

proc eLitUnset(n: int) =
  ## A constant discriminator with the arm field left out: default too.
  let v = S8fV(kind: sA, shared: n)
  if v.a != 0:
    symexTarget("s8f_e_litunset")

suite "S8f (e) variant witnesses reproduce":
  test "a range discriminator's else arm renders its tag and fields":
    let r = symexFind(eRangeElse, tLabel("s8f_e_rangeelse"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].kind == 5 and r.witness[0].e == 42
    check reproduces(eRangeElse(r.witness[0]), "s8f_e_rangeelse")

  test "a discriminator reassignment's witness starts on the new branch":
    let r = symexFind(ePlainSurvives, tLabel("s8f_e_plain"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    var w = r.witness[0]
    check w.kind == sB
    check reproduces(ePlainSurvives(w), "s8f_e_plain")

  test "an unconditional reassignment still reaches, from the new branch":
    let r = symexFind(eUncond, tLabel("s8f_e_uncond"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    var w = r.witness[0]
    check w.kind == sB
    check reproduces(eUncond(w), "s8f_e_uncond")

  test "a branch change on a local object raises FieldDefect, never reaches":
    let r = symexFind(eLocalChange, tLabel("s8f_e_local"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    check "FieldDefect" in r.raisedTypeId
    expect FieldDefect:
      eLocalChange()

  test "a same-branch reassignment keeps the branch's fields":
    let r = symexFind(eCarry, tLabel("s8f_e_carry"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "a symbolic reassignment's witness starts on the chosen branch":
    let r = symexFind(eSym, tLabel("s8f_e_sym"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    var w = r.witness[0]
    check w.kind == sB and r.witness[1] == sB
    check reproduces(eSym(w, r.witness[1]), "s8f_e_sym")

  test "a runtime-discriminator constructor's arm fields are default":
    let r = symexFind(eCtorFresh, tLabel("s8f_e_ctor777"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    let z = symexFind(eCtorZero, tLabel("s8f_e_ctorzero"))
    checkpoint($z.status & " " & show(z.errors))
    check z.status == sxSat
    check reproduces(eCtorZero(z.witness[0]), "s8f_e_ctorzero")

  test "a constant-discriminator constructor's omitted arm field is never a claim":
    ## Declined (`feUnsupportedExprKind`) before and after S8f: an honest
    ## `sxUnknown`, never an `sxSat` on a value Nim cannot hold.
    let r = symexFind(eLitUnset, tLabel("s8f_e_litunset"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status in {sxUnsat, sxUnknown}

# ---- (d) walker version floor -------------------------------------------------

suite "S8f (d) walker version":
  test "the walker version is at least 154":
    check parseInt(symexWalkerVersion) >= 154
