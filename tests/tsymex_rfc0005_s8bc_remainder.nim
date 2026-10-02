## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder.
import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (1) `getOrDefault` -----------------------------------------------------

proc hcAnd(s: string) =
  # `Hash` is a plain alias the model does not classify, so `hc` holds a
  # declined placeholder; `and` on it was a walker fault (`r.kind == svBool`).
  var hc: Hash
  hc = hash(s)
  if (hc and 7) == 3: symexTarget("hc_and")

proc godPresent(t: Table[string, int]) =
  if t.getOrDefault("a") == 3: symexTarget("god_present")

proc godAbsent(t: Table[string, int]) =
  if "a" notin t and t.getOrDefault("a") == 0: symexTarget("god_absent")
  if "a" notin t and t.getOrDefault("a") != 0: symexTarget("god_absent_dead")

proc godAnd(t: Table[string, int], x: int) =
  if x == 1 and t.getOrDefault("a", 7) == 7: symexTarget("god_and")

proc godDef(t: Table[string, int]) =
  if "a" notin t and t.getOrDefault("a", 5) == 5: symexTarget("god_def")
  if "a" notin t and t.getOrDefault("a", 5) != 5: symexTarget("god_def_dead")
  if "a" in t and t["a"] == 2 and t.getOrDefault("a", 5) != 2:
    symexTarget("god_def_dead2")

proc godLocal(k: string, x: int) =
  var t = initTable[string, int]()
  t[k] = x
  if t.getOrDefault(k, 1) == 6 and t.getOrDefault("q", 9) == 9 and k != "q":
    symexTarget("god_local")
  if t.getOrDefault(k, 1) != x: symexTarget("god_local_dead")

proc godSeq(t: Table[string, seq[int]]) =
  if "a" notin t and t.getOrDefault("a").len == 0 and t.len == 1:
    symexTarget("god_seq")
  if "a" notin t and t.getOrDefault("a").len != 0: symexTarget("god_seq_dead")
  if "a" in t and t.getOrDefault("a").len == 2 and t["a"][1] == 4:
    symexTarget("god_seq_present")

proc godNan(x: int) =
  var t = initTable[float, int]()
  let n = NaN
  t[n] = 1
  if t.getOrDefault(n, 4) == 4 and x == 2: symexTarget("god_nan")
  if t.getOrDefault(n, 4) != 4: symexTarget("god_nan_dead")

suite "S8bc (1): getOrDefault":
  test "a declined `Hash` under `and` is a scoped decline, not a walker fault":
    let r = symexFind(hcAnd, tLabel("hc_and"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a present key's value":
    let r = symexFind(godPresent, tLabel("god_present"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat: replays(godPresent(r.witness[0]), "god_present")

  test "an absent key is default(V)":
    let r = symexFind(godAbsent, tLabel("god_absent"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(godAbsent(r.witness[0]), "god_absent")
    let d = symexFind(godAbsent, tLabel("god_absent_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "under `and`":
    let r = symexFind(godAnd, tLabel("god_and"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      replays(godAnd(r.witness[0], r.witness[1]), "god_and")

  test "an explicit default":
    let r = symexFind(godDef, tLabel("god_def"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(godDef(r.witness[0]), "god_def")
    block:
      let d = symexFind(godDef, tLabel("god_def_dead"))
      checkpoint "god_def_dead " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(godDef, tLabel("god_def_dead2"))
      checkpoint "god_def_dead2 " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "a local table":
    let r = symexFind(godLocal, tLabel("god_local"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(godLocal(r.witness[0], r.witness[1]), "god_local")
    let d = symexFind(godLocal, tLabel("god_local_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq value: absent is the empty seq":
    let r = symexFind(godSeq, tLabel("god_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(godSeq(r.witness[0]), "god_seq")
    let d = symexFind(godSeq, tLabel("god_seq_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let p = symexFind(godSeq, tLabel("god_seq_present"))
    checkpoint $p.status & " " & show(p.errors)
    check p.status == sxSat
    if p.status == sxSat: replays(godSeq(p.witness[0]), "god_seq_present")

  test "a NaN key is never found, so it is the default":
    let r = symexFind(godNan, tLabel("god_nan"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(godNan, tLabel("god_nan_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

# ---- (8) a conversion of an inlined iterator's parameter --------------------

iterator twice(n: int): int =
  yield int(n)
  yield int(n) + 1

proc icPlain(x: int) =
  if x < -1000 or x > 1000: return
  var s = 0
  for y in twice(x): s += y
  if s == 7: symexTarget("ic_plain")
  if s mod 2 == 0: symexTarget("ic_plain_dead")

iterator widen(n: int8): int =
  yield int(n) * 2

proc icWiden(x: int8) =
  for y in widen(x):
    if y == -256: symexTarget("ic_widen")
    if y > 254: symexTarget("ic_widen_dead")

iterator narrowed(n: int32): int =
  # `yield n` is a hidden int32 -> int conversion of the parameter.
  yield n

proc icHidden(x: int32) =
  for y in narrowed(x):
    if y == -5: symexTarget("ic_hidden")
    if y > int(high(int32)): symexTarget("ic_hidden_dead")

iterator asU8(n: int): uint8 =
  yield uint8(n and 0xFF)

proc icMasked(x: int) =
  for y in asU8(x):
    if y == 200'u8 and x > 1000: symexTarget("ic_masked")

proc litConv(y: int) =
  # `high(int32)` folds to an int32 literal; its explicit widening was a
  # walker fault (`lowerConvIntWidth`: a 64-bit operand), with no iterator.
  if y > int(high(int32)) and y < int(high(int32)) + 3: symexTarget("lit_conv")
  if y < int(low(int8)) and y > int(-131'i16): symexTarget("lit_conv2")
  if y > int(high(int32)) and y < int(high(int32)) + 1:
    symexTarget("lit_conv_dead")

suite "S8bc (8): a conversion of an inlined iterator's parameter":
  test "an explicit widening of a typed literal (not a walker fault)":
    let r = symexFind(litConv, tLabel("lit_conv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] in 2147483648 .. 2147483649
      check reproduces(litConv(r.witness[0]), "lit_conv")
    let r2 = symexFind(litConv, tLabel("lit_conv2"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat: check reproduces(litConv(r2.witness[0]), "lit_conv2")
    let d = symexFind(litConv, tLabel("lit_conv_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "int(n) of an int parameter":
    let r = symexFind(icPlain, tLabel("ic_plain"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icPlain(r.witness[0]), "ic_plain")
    let d = symexFind(icPlain, tLabel("ic_plain_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a widening conversion of an int8 parameter":
    let r = symexFind(icWiden, tLabel("ic_widen"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icWiden(r.witness[0]), "ic_widen")
    let d = symexFind(icWiden, tLabel("ic_widen_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a hidden conversion of an int32 parameter":
    let r = symexFind(icHidden, tLabel("ic_hidden"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icHidden(r.witness[0]), "ic_hidden")
    let d = symexFind(icHidden, tLabel("ic_hidden_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a narrowing conversion of an expression over the parameter":
    let r = symexFind(icMasked, tLabel("ic_masked"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(icMasked(r.witness[0]), "ic_masked")

# ---- (9) seq[char] / seq[enum] witnesses ------------------------------------

type Col = enum cRed, cGreen, cBlue

proc chSeq(s: seq[char]) =
  if s.len == 2 and s[0] == 'q' and s[1] == 'z': symexTarget("ch_seq")

proc enSeq(s: seq[Col]) =
  if s.len == 1 and s[0] == cBlue: symexTarget("en_seq")

proc enArr(a: array[2, Col]) =
  if a[0] == cGreen and a[1] == cBlue: symexTarget("en_arr")

type CHold = object
  cs: seq[char]
  es: seq[Col]

proc chObj(h: CHold) =
  if h.cs.len == 1 and h.cs[0] == 'x' and h.es.len == 1 and h.es[0] == cRed:
    symexTarget("ch_obj")

proc chTabSeq(t: Table[string, seq[char]]) =
  if "k" in t and t["k"].len == 1 and t["k"][0] == 'm': symexTarget("ch_tabseq")

proc enSet(s: HashSet[Col]) =
  if s.len == 1 and cGreen in s: symexTarget("en_set")

suite "S8bc (9): a seq[char] / seq[enum] witness replays at its own type":
  test "seq[char]":
    let r = symexFind(chSeq, tLabel("ch_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      checkpoint $r.witness
      replays(chSeq(r.witness[0]), "ch_seq")

  test "seq[enum]":
    let r = symexFind(enSeq, tLabel("en_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      checkpoint $r.witness
      replays(enSeq(r.witness[0]), "en_seq")

  test "array[2, enum]":
    let r = symexFind(enArr, tLabel("en_arr"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(enArr(r.witness[0]), "en_arr")

  test "seq[char] and seq[enum] object fields":
    let r = symexFind(chObj, tLabel("ch_obj"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chObj(r.witness[0]), "ch_obj")

  test "a seq[char] Table value":
    let r = symexFind(chTabSeq, tLabel("ch_tabseq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chTabSeq(r.witness[0]), "ch_tabseq")

  test "HashSet[enum]":
    let r = symexFind(enSet, tLabel("en_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(enSet(r.witness[0]), "en_set")

# ---- (2) a non-operator {.borrow.} routine ----------------------------------
#
# RFC-0005 S8bc: a borrowed routine has no body (its `getImpl` body is the
# base routine's symbol); `f(a)` is the base routine on `T(a)`, rewrapped
# when `f` returns the distinct. It was walked as a user routine whose body,
# that bare symbol, declined (`feUnsupportedStmtKind`).

type
  BSq = distinct seq[int]
  BM = distinct int
  BName = distinct string
  BBox = object
    w: int
  BDBox = distinct BBox

proc len(d: BSq): int {.borrow.}
proc abs(m: BM): BM {.borrow.}
proc `$`(m: BM): string {.borrow.}
proc len(n: BName): int {.borrow.}
# Full arity: Nim 2.2.10 crashes compiling `proc inc(m: var BM) {.borrow.}`.
proc inc(m: var BM, y: int) {.borrow.}
proc add(d: var BSq, x: int) {.borrow.}
proc area(b: BBox): int = b.w * b.w
proc area(d: BDBox): int {.borrow.}

proc brLen(d: BSq) =
  if d.len == 2: symexTarget("br_len")
  if d.len < 0: symexTarget("br_len_dead")

proc brAbs(m: BM) =
  if int(m) > -100 and int(m) < 100:
    if int(abs(m)) == 5 and int(m) < 0: symexTarget("br_abs")
    if int(abs(m)) < 0: symexTarget("br_abs_dead")

proc brStr(m: BM) =
  if $m == "42": symexTarget("br_str")

proc brStrLen(n: BName) =
  if n.len == 3: symexTarget("br_strlen")

proc brInc(x: int) =
  if x > 100 or x < -100: return
  var m = BM(x)
  inc(m, 2)
  if int(m) == 7: symexTarget("br_inc")
  if int(m) == x: symexTarget("br_inc_dead")

proc brAdd(x: int) =
  var d = BSq(@[1])
  d.add x
  if d.len == 2 and seq[int](d)[1] == 9: symexTarget("br_add")
  if d.len != 2: symexTarget("br_add_dead")

proc brUser(d: BDBox) =
  if BBox(d).w < 100 and BBox(d).w > -100:
    if area(d) == 49: symexTarget("br_user")
    if area(d) < 0: symexTarget("br_user_dead")

suite "S8bc (2): a non-operator {.borrow.} routine":
  test "len of a distinct seq":
    let r = symexFind(brLen, tLabel("br_len"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brLen(r.witness[0]), "br_len")
    let d = symexFind(brLen, tLabel("br_len_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "abs of a distinct int, rewrapped":
    let r = symexFind(brAbs, tLabel("br_abs"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brAbs(r.witness[0]), "br_abs")
    let d = symexFind(brAbs, tLabel("br_abs_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "$ of a distinct int":
    let r = symexFind(brStr, tLabel("br_str"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brStr(r.witness[0]), "br_str")

  test "len of a distinct string":
    let r = symexFind(brStrLen, tLabel("br_strlen"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brStrLen(r.witness[0]), "br_strlen")

  test "a var-parameter borrow (inc)":
    let r = symexFind(brInc, tLabel("br_inc"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == 5
    let d = symexFind(brInc, tLabel("br_inc_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a var-parameter borrow on a distinct seq (add)":
    let r = symexFind(brAdd, tLabel("br_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == 9
    let d = symexFind(brAdd, tLabel("br_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a borrow of a user routine":
    let r = symexFind(brUser, tLabel("br_user"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(brUser, tLabel("br_user_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

# ---- (4) insert on an array element ------------------------------------------
#
# RFC-0005 S8bc: `a[i].insert(x, j)` takes the bare arm's two phases (S8ar):
# grow, write back, then place on the grown element. It fell to the generic
# call (`system.insert` inlined to an unsupported `when`).

type AIHold = object
  a: array[2, seq[int]]

proc aiMid(v: int, j: int) =
  if j < 0 or j > 2: return
  var a: array[2, seq[int]]
  a[1] = @[5, 6]
  a[1].insert(v, j)
  if a[1].len == 3 and a[1][1] == v and a[1][0] == 5 and a[1][2] == 6:
    symexTarget("ai_mid")
  if a[1].len != 3: symexTarget("ai_mid_dead")
  if a[0].len != 0: symexTarget("ai_other_dead")

proc aiRange(j: int) =
  var a: array[2, seq[int]]
  a[0] = @[1, 2]
  try:
    a[0].insert(9, j)
  except RangeDefect:
    if a[0].len == 2: symexTarget("ai_range")
  except IndexDefect:
    if a[0].len == 3 and a[0][2] == 0: symexTarget("ai_index_grown")
    if a[0].len != 3: symexTarget("ai_index_dead")

proc aiField(h: AIHold, v: int) =
  var g = h
  let n0 = g.a[0].len
  g.a[0].insert(v, 0)
  if g.a[0].len == n0 + 1 and g.a[0][0] == v and n0 == 1 and g.a[0][1] == 4:
    symexTarget("ai_field")
  if g.a[0].len != n0 + 1: symexTarget("ai_field_dead")

proc aiTab(t: Table[string, seq[int]], v: int) =
  var u = t
  if "k" in u:
    u["k"].insert(v, 0)
    if u["k"][0] == v and u["k"].len == 2 and u["k"][1] == 3:
      symexTarget("ai_tab")

suite "S8bc (4): insert on an array element":
  test "insert in the middle of an array element":
    let r = symexFind(aiMid, tLabel("ai_mid"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 1
      check reproduces(aiMid(r.witness[0], r.witness[1]), "ai_mid")
    let d = symexFind(aiMid, tLabel("ai_mid_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let o = symexFind(aiMid, tLabel("ai_other_dead"))
    checkpoint $o.status & " " & show(o.errors)
    check o.status == sxUnsat

  test "RangeDefect before any change, IndexDefect after the grow":
    let r = symexFind(aiRange, tLabel("ai_range"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(aiRange(r.witness[0]), "ai_range")
    let g = symexFind(aiRange, tLabel("ai_index_grown"))
    checkpoint $g.status & " " & show(g.errors)
    check g.status == sxSat
    if g.status == sxSat:
      check g.witness[0] > 2
      check reproduces(aiRange(g.witness[0]), "ai_index_grown")
    let d = symexFind(aiRange, tLabel("ai_index_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an array field of a value object":
    let r = symexFind(aiField, tLabel("ai_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(aiField(r.witness[0], r.witness[1]), "ai_field")
    let d = symexFind(aiField, tLabel("ai_field_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a Table value":
    let r = symexFind(aiTab, tLabel("ai_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(aiTab(r.witness[0], r.witness[1]), "ai_tab")

# ---- (5) newSeq ---------------------------------------------------------------
#
# RFC-0005 S8bc: `newSeq[T](n)` / `newSeq(s, n)` is `n` zero elements; a
# negative `n` raises `RangeDefect` (the `Natural` parameter); a length above
# 2^20 declines, scoped to its path. The stdlib body was walked and declined
# (an unsupported `when`, the payload cast).

proc nsLen(n: int) =
  if n < 0 or n > 50: return
  let s = newSeq[int](n)
  if s.len == 3 and s[2] == 0 and s[0] == 0: symexTarget("ns_len")
  if s.len == 3 and s[1] != 0: symexTarget("ns_zero_dead")
  if s.len != n and n >= 0: symexTarget("ns_len_dead")

proc nsRange(n: int) =
  try:
    let s = newSeq[int](n)
    if s.len < 0: symexTarget("ns_range_dead")
  except RangeDefect:
    if n < 0: symexTarget("ns_range")
    if n >= 0: symexTarget("ns_range_dead2")

proc nsHuge(n: int) =
  if n == 7: symexTarget("ns_small")
  if n < 0: return
  let s = newSeq[bool](n)
  if s.len == 2_000_000: symexTarget("ns_huge")

proc nsVar(n: int) =
  if n < 1 or n > 9: return
  var s: seq[string]
  newSeq(s, n)
  s[n - 1] = "x"
  if s.len == 4 and s[3] == "x" and s[0] == "": symexTarget("ns_var")
  if s.len == 4 and s[2] != "": symexTarget("ns_var_dead")

proc nsWrite(i: int) =
  var s = newSeq[int8]()
  s.add 3
  var t = newSeq[int8](3)
  t[i] = 5
  if t[0] == 5 and s[0] == 3 and t[1] == 0 and t.len == 3: symexTarget("ns_write")

proc itBound(n: int) =
  # `initTable`'s own size guard (S8at), behind a bound: its decline arm is
  # infeasible here, so it is dropped, not walked into a taint.
  if n < 0 or n > 9: return
  var t = initTable[int, int](n)
  t[1] = 2
  if t.len != 1: symexTarget("it_bound_dead")

suite "S8bc (5): newSeq":
  test "a scoped decline on an infeasible arm does not taint":
    let d = symexFind(itBound, tLabel("it_bound_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let n = symexFind(nsLen, tLabel("ns_len_dead"))
    checkpoint $n.status & " " & show(n.errors)
    check n.status == sxUnsat


  test "newSeq[T](n) is n zero elements":
    let r = symexFind(nsLen, tLabel("ns_len"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(nsLen(r.witness[0]), "ns_len")
    let d = symexFind(nsLen, tLabel("ns_zero_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let d2 = symexFind(nsLen, tLabel("ns_len_dead"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status == sxUnsat

  test "a negative length raises RangeDefect":
    let r = symexFind(nsRange, tLabel("ns_range"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(nsRange(r.witness[0]), "ns_range")
    # A length above 2^20 is the declined path, so this dead label is
    # sxUnknown, not sxUnsat: the decline must never be a false sxUnsat.
    let d = symexFind(nsRange, tLabel("ns_range_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnknown
    check d.errors.hasKind(feUnsupportedOp)
    check not d.errors.hasKind(weInternalWalkerFault)
    let d2 = symexFind(nsRange, tLabel("ns_range_dead2"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status in {sxUnsat, sxUnknown}
    check not d2.errors.hasKind(weInternalWalkerFault)

  test "a length above the bound declines, scoped":
    # The label before the call is found; the one past the 2^20 bound is
    # an honest sxUnknown, never a false sxUnsat.
    let r = symexFind(nsHuge, tLabel("ns_small"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let h = symexFind(nsHuge, tLabel("ns_huge"))
    checkpoint $h.status & " " & show(h.errors)
    check h.status == sxUnknown
    check h.errors.hasKind(feUnsupportedOp)

  test "newSeq(s, n) on a seq[string]":
    let r = symexFind(nsVar, tLabel("ns_var"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(nsVar(r.witness[0]), "ns_var")
    let d = symexFind(nsVar, tLabel("ns_var_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "newSeq[int8]() and a write into newSeq[int8](3)":
    let r = symexFind(nsWrite, tLabel("ns_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 0
      check reproduces(nsWrite(r.witness[0]), "ns_write")

# ---- (7) mgetOrPut, and inc / dec / += on an element ----------------------
#
# RFC-0005 S8bc: `mgetOrPut(t, k, d)` is a get-or-insert whose result is a
# reference to the cell; its writers (`.add`, `+=`, `inc`, `=`) write back
# through `t[k]`. Found en route (SOUNDNESS): `inc`/`dec` on any receiver
# but a bare int variable walked the bodiless `{.magic.}` as an empty body,
# dropping the write with no record -- a clean, wrong sxSat. Also: an empty
# `@[]` passed as a `seq[T]` argument was built over the unbacked sort (a
# walker fault on the first store).

proc mgAdd(k, v: int) =
  var t = initTable[int, seq[int]]()
  t.mgetOrPut(k, @[]).add v
  t.mgetOrPut(k, @[]).add 4
  if t[k].len == 2 and t[k][0] == 9 and t[k][1] == 4: symexTarget("mg_add")
  if t[k].len != 2 or t.len != 1: symexTarget("mg_add_dead")

proc mgCount(a, b: int) =
  var t = initTable[int, int]()
  let xs = [a, b]   # (`for x in [a, b]` is a walker fault: reported, not fixed here)
  for x in xs:
    inc t.mgetOrPut(x, 0)
  t.mgetOrPut(a, 0) += 10
  if t[b] == 12: symexTarget("mg_count")
  if t[a] == 11 and a == b: symexTarget("mg_count_dead")

proc mgRead(k: int) =
  var t = initTable[int, int]()
  t[1] = 7
  let x = t.mgetOrPut(k, 5)
  if x == 7 and t.len == 1: symexTarget("mg_read_hit")
  if x == 5 and t.len == 2 and t[k] == 5: symexTarget("mg_read_miss")
  if x == 5 and t.len == 1: symexTarget("mg_read_dead")

proc mgAsg(k: int) =
  var t = initTable[int, int]()
  t.mgetOrPut(k, 3) = 8
  if t[k] == 8 and k == 6 and t.len == 1: symexTarget("mg_asg")
  if t[k] == 3: symexTarget("mg_asg_dead")

type IncObj = object
  f: int

proc incDropped(k: int) =
  var t = initTable[int, int]()
  t[k] = 1
  inc t[k]
  var a: array[3, int]
  inc a[1], 2
  var o = IncObj(f: 1)
  dec o.f
  var s = @[1, 2]
  dec s[1]
  if t[k] == 2 and a[1] == 2 and o.f == 0 and s[1] == 1 and k == 3:
    symexTarget("inc_ok")
  if t[k] == 1 or a[1] == 0 or o.f == 1 or s[1] == 2:
    symexTarget("inc_dropped")

proc incRanged(k: int) =
  var a: array[2, range[0 .. 5]]
  inc a[0]
  if k == 1: symexTarget("inc_ranged")

proc augAbsent(k: int) =
  var t = initTable[int, int]()
  t[1] = 1
  try:
    t[k] += 1
    if t[k] == 2: symexTarget("aug_present")
  except KeyError:
    symexTarget("aug_absent")

proc emptyArg(k: int) =
  var t = initTable[int, seq[int]]()
  t[k] = @[]
  t[k].add 3
  let g = t.getOrDefault(k + 1, @[])
  if t[k][0] == 3 and g.len == 0 and k == 1: symexTarget("empty_arg")

suite "S8bc (7): mgetOrPut":
  test "mgetOrPut(...).add":
    let r = symexFind(mgAdd, tLabel("mg_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 9
      check reproduces(mgAdd(r.witness[0], r.witness[1]), "mg_add")
    let d = symexFind(mgAdd, tLabel("mg_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc and += through mgetOrPut: the counting idiom":
    let r = symexFind(mgCount, tLabel("mg_count"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == r.witness[1]
      check reproduces(mgCount(r.witness[0], r.witness[1]), "mg_count")
    let d = symexFind(mgCount, tLabel("mg_count_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "mgetOrPut read: a present key, and an inserted one":
    let h = symexFind(mgRead, tLabel("mg_read_hit"))
    checkpoint $h.status & " " & show(h.errors)
    check h.status == sxSat
    if h.status == sxSat:
      check h.witness[0] == 1
      check reproduces(mgRead(h.witness[0]), "mg_read_hit")
    let m = symexFind(mgRead, tLabel("mg_read_miss"))
    checkpoint $m.status & " " & show(m.errors)
    check m.status == sxSat
    if m.status == sxSat:
      check m.witness[0] != 1
      check reproduces(mgRead(m.witness[0]), "mg_read_miss")
    let d = symexFind(mgRead, tLabel("mg_read_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "mgetOrPut(...) = v":
    let r = symexFind(mgAsg, tLabel("mg_asg"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(mgAsg(r.witness[0]), "mg_asg")
    let d = symexFind(mgAsg, tLabel("mg_asg_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc / dec on an element or a field is no longer dropped":
    # Was sxSat with no errors for `inc_dropped` (the write dropped).
    let r = symexFind(incDropped, tLabel("inc_ok"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(incDropped(r.witness[0]), "inc_ok")
    let d = symexFind(incDropped, tLabel("inc_dropped"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc on a ranged element declines, never the silent no-op":
    let r = symexFind(incRanged, tLabel("inc_ranged"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and "`inc`" in it.msg)

  test "t[k] += v raises KeyError for an absent key":
    let a = symexFind(augAbsent, tLabel("aug_absent"))
    checkpoint $a.status & " " & show(a.errors)
    check a.status == sxSat
    if a.status == sxSat:
      check a.witness[0] != 1
      check reproduces(augAbsent(a.witness[0]), "aug_absent")
    let p = symexFind(augAbsent, tLabel("aug_present"))
    checkpoint $p.status & " " & show(p.errors)
    check p.status == sxSat
    if p.status == sxSat: check reproduces(augAbsent(p.witness[0]), "aug_present")

  test "an empty @[] argument is a seq of the parameter's element":
    let r = symexFind(emptyArg, tLabel("empty_arg"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat: check reproduces(emptyArg(r.witness[0]), "empty_arg")

# ---- (6) Table iteration ---------------------------------------------------
#
# RFC-0005 S8bc: `pairs` / `keys` / `values` (and `for k, v in t`) over a
# Table is a bounded unroll over an enumeration of its present keys in a
# FREE order (`isTabKeys`). Nim's order is the hash order, so a table that
# can hold two or more entries taints the path `feTableIterOrder`
# (`dcFreshSymbol`): the candidate is replayed, and one whose label needs an
# order Nim does not produce is refuted to sxUnknown.

proc tiSum(a, b: int) =
  if a < -100 or a > 100 or b < -100 or b > 100: return   # no overflow
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var s = 0
  for k, v in t:
    s += v + k
  if s == 13 and a == 4: symexTarget("ti_sum")
  # Every enumeration sums the same: a + b + 3 over two entries, b + 2 over
  # one (a == b, the second write wins).
  if a != b and s != a + b + 3: symexTarget("ti_sum_dead")
  if a == b and s != b + 2: symexTarget("ti_sum_dead")

proc tiOrder(a, b: int) =
  # Nim 2.2.10 visits the keys 1, 2 of this table as 2 then 1 (probed).
  if a != 1 or b != 2: return
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var first = -1
  for k in t.keys:
    if first == -1: first = k
  if first == 2: symexTarget("ti_order_real")
  if first == 1: symexTarget("ti_order_other")

proc tiValues(a: int) =
  var t = initTable[string, int]()
  t["x"] = a
  t["y"] = 3
  var s = 0
  for v in t.values:
    s += v
  if s == 10: symexTarget("ti_values")

proc tiTuple(a: int) =
  var t = initTable[int, int]()
  t[1] = a
  t[2] = 5
  var s = 0
  for (k, v) in t.pairs:
    s += k * v
  var u = 0
  for kv in t.pairs:
    u += kv[1]
  if s == 16 and u == a + 5: symexTarget("ti_tuple")

proc tiStrKey(x: string) =
  var t = initTable[string, int]()
  t["a"] = 1
  t[x] = 2
  var found = false
  for k in t.keys:
    if k == "zz":
      found = true
      break
  if found: symexTarget("ti_strkey")
  if t.len == 1 and x != "a": symexTarget("ti_strkey_dead")

proc tiParam(t: Table[int, int]) =
  symexAssume(t.len <= 3)
  var c = 0
  for k in t.keys:
    inc c
  if c != t.len: symexTarget("ti_param_dead")

proc tiOne(a: int) =
  var t = initTable[int, int]()
  for k in t.keys: symexTarget("ti_empty_dead")
  t[a] = 7
  for k, v in t:
    if k == 3 and v == 7: symexTarget("ti_one")

proc tiGrow(a: int) =
  var t = initTable[int, int]()
  t[1] = 1
  for k in t.keys:
    t[k + a] = 0
  symexTarget("ti_grow")

proc tiFloat(a: float) =
  var t = initTable[float, int]()
  t[a] = 1
  var c = 0
  for k in t.keys: inc c
  if c == 1: symexTarget("ti_float")

suite "S8bc (6): Table iteration":
  test "for k, v in t: an order-independent fold":
    let r = symexFind(tiSum, tLabel("ti_sum"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(tiSum(r.witness[0], r.witness[1]), "ti_sum")
    let d = symexFind(tiSum, tLabel("ti_sum_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an order Nim produces is found; another declines":
    let r = symexFind(tiOrder, tLabel("ti_order_real"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(tiOrder(r.witness[0], r.witness[1]), "ti_order_real")
    let o = symexFind(tiOrder, tLabel("ti_order_other"))
    checkpoint $o.status & " " & show(o.errors)
    check o.status == sxUnknown
    check o.errors.hasKind(feReplayRefuted)
    check o.errors.hasKind(feTableIterOrder)

  test "values, over a string-keyed table":
    let r = symexFind(tiValues, tLabel("ti_values"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
      check reproduces(tiValues(r.witness[0]), "ti_values")

  test "for (k, v) in t.pairs, and for kv in t.pairs":
    let r = symexFind(tiTuple, tLabel("ti_tuple"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
      check reproduces(tiTuple(r.witness[0]), "ti_tuple")

  test "keys of a string-keyed table, with a break":
    let r = symexFind(tiStrKey, tLabel("ti_strkey"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "zz"
      check reproduces(tiStrKey(r.witness[0]), "ti_strkey")
    let d = symexFind(tiStrKey, tLabel("ti_strkey_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an input table: the enumeration is all of its keys":
    let d = symexFind(tiParam, tLabel("ti_param_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an empty or one-entry table is exact (no order taint)":
    let d = symexFind(tiOne, tLabel("ti_empty_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(tiOne, tLabel("ti_one"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feTableIterOrder)
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(tiOne(r.witness[0]), "ti_one")

  test "a body that changes the length declines on that path":
    let r = symexFind(tiGrow, tLabel("ti_grow"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check r.errors.anyIt(it.kind == feUnsupportedOp and
                         "length changed" in it.msg)
    if r.status == sxSat:
      check r.witness[0] == 0
      check reproduces(tiGrow(r.witness[0]), "ti_grow")

  test "a float key declines":
    let r = symexFind(tiFloat, tLabel("ti_float"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and "float" in it.msg)

suite "S8bc: walker version floor":
  test "walker version floor >= 203":
    check parseInt(symexWalkerVersion) >= 203
