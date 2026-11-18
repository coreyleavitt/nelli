## RFC-0016 S8cp-r, PRC-34 (S8cp item 7): shapes that declined.
##
##   * `==` on two tuples or two plain objects whose fields are all builtin
##     atoms (integers, `bool`, `char`, floats, `string`): system's generic
##     `==` compares field by field, which the walker now lowers to the
##     conjunction of the fields' own `==` (was `eqBV` on a tuple, declined).
##     A field whose `==` may be a user's (a `distinct`, an enum, a nested
##     record) keeps the decline: system's `==` reaches it through `mixin`;
##   * a `type` section in a routine body declares, and runs nothing (was
##     `feUnsupportedStmtKind`);
##   * the shapes S8cp listed that later slices modelled, each pinned with its
##     native run: a `let b = addr o.y` alias across a whole assignment, a
##     parameter pragma `x {.inject.}: int`, a nested `addr t[1][0]`, and
##     `s[1].b = 7`.
## Each symbolic pin has the compiled program's run beside it.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  Obj = object
    x, y: int
  Mixed = object
    a: int8
    b: uint16
    c: bool
    d: char
    e: float
    s: string
  Meters = distinct int
  WithDistinct = object
    m: Meters
    k: int
  Inner = object
    v: int
  Outer = object
    i: Inner
  Pt = object
    b: int
  Hue = enum hRed, hBlue
  WithHue = object
    h: Hue
    k: int
  Wrap = object
    v: int
  Holder = object
    w: Wrap
    k: int
  Pair = tuple[p: int, q: uint8]
    ## `uint8` keeps `Pair`'s `==` off the `(int, int)` tuples above: a
    ## tuple type is structural, so it would bind for every such tuple.
  HasPair = object
    t: Pair
  HasSS = object
    ss: seq[seq[int]]
    k: int

proc `==`(a, b: Meters): bool = int(a) div 10 == int(b) div 10
proc `==`(a, b: Hue): bool = ord(a) + ord(b) >= 0
  ## Every two hues are equal: an enum's `==` is overloadable, and system's
  ## generic `==` on a record or a seq reaches this one through `mixin`.
proc `==`(a, b: Wrap): bool = a.v div 10 == b.v div 10
  ## A nested object's own `==`, coarser than field-wise.
proc `==`(a, b: Pair): bool = a.p == b.p
  ## A named tuple's own `==`, which ignores `q`.

proc tupEq(a, b: int) =
  let t = (a, b)
  let u = (b, 3)
  if t == u: symexTarget("hit")

proc tupNe(a, b: int) =
  if (a, b) != (3, 4): discard
  else: symexTarget("hit")

proc tupEqDead(a: int) =
  if (a, a) == (5, 6): symexTarget("hit")

proc objEq(a, b: int) =
  if Obj(x: a, y: 1) == Obj(x: 2, y: b): symexTarget("hit")

proc mixedEq(a: int8; c: char; s: string) =
  let l = Mixed(a: a, b: 7, c: true, d: c, e: 0.5, s: s)
  let r = Mixed(a: -3, b: 7, c: true, d: 'q', e: 0.5, s: "ab")
  if l == r: symexTarget("hit")

proc nanEq(f: float) =
  if (f, 1) == (f, 1): discard
  else: symexTarget("hit")

proc distinctField(a, b: int) =
  # The user's `==` on `Meters` makes 12 and 15 equal; system's `==` on the
  # object reaches it, so the field-by-field model must not decide this.
  let l = WithDistinct(m: Meters(a), k: 0)
  let r = WithDistinct(m: Meters(b), k: 0)
  if l == r and a != b: symexTarget("hit")

proc enumField(a: int) =
  # An enum lifts to an integer, so only the field type's name tells the
  # user's `==` apart; under it `hRed` equals `hBlue`.
  let l = WithHue(h: (if a > 0: hRed else: hBlue), k: 0)
  if l == WithHue(h: hBlue, k: 0) and a > 0: symexTarget("hit")

proc nestedRecord(a: int) =
  if Outer(i: Inner(v: a)) == Outer(i: Inner(v: 4)): symexTarget("hit")

proc nestedRecordDead(a: int) =
  if Outer(i: Inner(v: a)) == Outer(i: Inner(v: 4)) and a != 4:
    symexTarget("hit")

proc nestedUserEq(a, b: int) =
  # `Wrap`'s own `==` makes 12 and 15 equal; field-wise they differ.
  if Holder(w: Wrap(v: a), k: 1) == Holder(w: Wrap(v: b), k: 1) and a != b:
    symexTarget("hit")

proc nestedUserEqDead(a, b: int) =
  # Under `Wrap`'s `==`, 12 and 25 differ.
  if Holder(w: Wrap(v: a), k: 1) == Holder(w: Wrap(v: b), k: 1) and
     a div 10 != b div 10 and a >= 0 and b >= 0:
    symexTarget("hit")

proc tupleUserEq(a: int; b: uint8) =
  # `Pair`'s own `==` ignores `q`.
  if HasPair(t: (a, 1'u8)) == HasPair(t: (a, b)) and b != 1: symexTarget("hit")

proc typeSection(v: int) =
  type L = object
    a: int
  var l = L(a: v)
  if l.a == 5: symexTarget("hit")

proc typeSectionDead(v: int) =
  type L = object
    a: int
  var l = L(a: v)
  if l.a == 5 and v != 5: symexTarget("hit")

proc aliasWhole(v: int) =
  var o = Obj(x: 1, y: 2)
  let b = addr o.y
  o = Obj(x: 0, y: v)
  if b[] == 7: symexTarget("hit")

proc injectParam(x {.inject.}: int) =
  if x == 5: symexTarget("hit")

proc nestedAddr(v: int) =
  var t = [[0, 0], [0, 0]]
  let p = addr t[1][0]
  p[] = v
  if t[1][0] == 7: symexTarget("hit")

proc seqFieldWrite(v: int) =
  var s = @[Pt(b: 0), Pt(b: 0)]
  s[1].b = 7
  if s[1].b == v: symexTarget("hit")

proc seqEqLit(a, b: int) =
  if @[a, 2] == @[1, b]: symexTarget("hit")

proc seqEqLenDead(a: int) =
  if @[a] == @[a, a]: symexTarget("hit")

proc seqNe(a: int) =
  if @[a, 1] != @[3, 1]: discard
  else: symexTarget("hit")

proc seqEqParam(s: seq[int]) =
  if s == @[3, 4]: symexTarget("hit")

proc seqEqParamDead(s: seq[int]) =
  if s == @[3, 4] and s.len != 2: symexTarget("hit")

proc seqEqParamElemDead(s: seq[int]) =
  if s == @[3, 4] and s[1] != 4: symexTarget("hit")

proc seqEqSym(s, t: seq[int]) =
  if s.len == 2 and s == t and t[1] == 5: symexTarget("hit")

proc seqEqSymDead(s, t: seq[int]) =
  if s.len > 1 and s == t and s[1] != t[1]: symexTarget("hit")

proc seqEqSymLenDead(s, t: seq[int]) =
  if s == t and s.len != t.len: symexTarget("hit")

proc seqNeSymDead(s, t: seq[int]) =
  # Equal lengths and elements, so equal: what the data arrays hold past the
  # length (or below 0) must not make them differ.
  if s.len == 1 and t.len == 1 and s[0] == t[0] and s != t:
    symexTarget("hit")

proc seqEqLoop(s, t: seq[int]) =
  var hits = 0
  for k in 0 ..< 3:
    if s == t and s.len == k: inc hits
  if hits == 1 and t.len == 2: symexTarget("hit")

proc seqEqLoopDead(s, t: seq[int]) =
  var hits = 0
  for k in 0 ..< 3:
    if s == t and s.len == k: inc hits
  if hits == 1 and t.len == 2 and s.len != 2: symexTarget("hit")

proc seqStrSym(s, t: seq[string]) =
  if s == t and s.len == 1 and s[0] == "ab": symexTarget("hit")

proc seqStrSymDead(s, t: seq[string]) =
  if s == t and t.len == 1 and t[0] == "ab" and s[0] != "ab":
    symexTarget("hit")

proc seqFloatSym(s, t: seq[float]) =
  if s == t: symexTarget("hit")

proc seqEqBranch(c: bool; t: seq[int]) =
  let s = if c: @[1, 2] else: @[1]
  if s == t and t.len == 2 and t[1] == 2: symexTarget("hit")

proc seqEqIdx(i: int; t: seq[int]) =
  let a = [@[1, 2], @[1]]
  if i >= 0 and i <= 1 and a[i] == t and t.len == 2: symexTarget("hit")

proc seqNeIdx(i: int; t: seq[int]) =
  # The unroll runs to the larger arm's length: `a[0]` and `t` differ only
  # at index 1.
  let a = [@[1, 2], @[1]]
  if i >= 0 and i <= 1 and t == @[1, 5] and a[i] != t and i == 0:
    symexTarget("hit")

proc seqNeIdxDead(i: int; t: seq[int]) =
  # `a[i]` over a symbolic index is an `ite` of the elements, so its length
  # is `ite(i == 1, 1, 2)`: bounded by 2 but not exact. Past its length the
  # seq holds no element, so each unrolled index is guarded by `i < len`;
  # without the guard `t[1]` (no element either) would make the two differ.
  let a = [@[1, 2], @[1]]
  if i >= 0 and i <= 1 and t == @[1] and a[i] != t and i == 1:
    symexTarget("hit")

proc seqNan(f: float) =
  if @[f] == @[f]: discard
  else: symexTarget("hit")

proc seqStrEq(s: string; c: char) =
  if @[s, "x"] == @["ab", "x"] and @[c] == @['q']: symexTarget("hit")

proc seqStrEqDead(s: string) =
  if @[s, "x"] == @["ab", "y"]: symexTarget("hit")

proc seqEnum(a: int) =
  let c = if a > 0: hRed else: hBlue
  if @[c] == @[hBlue] and a > 0: symexTarget("hit")

proc seqNested(a: int) =
  if @[@[a]] == @[@[4]]: symexTarget("hit")

proc nestStore(x: int) =
  var s = @[@[1, 2], @[3, 4]]
  s[1][0] = x
  if s[1][0] == 7 and s[1][1] == 4 and s[0][0] == 1 and s.len == 2 and
     s[1].len == 2:
    symexTarget("hit")

proc nestStoreDead(x: int) =
  var s = @[@[1, 2], @[3, 4]]
  s[1][0] = x
  if s[1][0] != x or s[0][0] != 1 or s[1][1] != 4: symexTarget("hit")

proc nestOuterOob(i: int) =
  var s = @[@[1, 2], @[3, 4]]
  s[i][0] = 5
  symexTarget("hit")

proc nestInnerOob(j: int) =
  var s = @[@[1, 2], @[3]]
  s[1][j] = 5
  symexTarget("hit")

proc nestOuterOobDead(i: int) =
  # Past the store only an in-bounds outer index survives.
  var s = @[@[1, 2], @[3, 4]]
  s[i][0] = 5
  if i < 0 or i > 1: symexTarget("hit")

proc nestInnerOobDead(j: int) =
  # Past the store only an in-bounds inner index survives.
  var s = @[@[1, 2], @[3]]
  s[1][j] = 5
  if j != 0: symexTarget("hit")

proc nestInBounds(i, j: int) =
  # Both indexes in bounds: no IndexDefect.
  var s = @[@[1, 2], @[3]]
  if i >= 0 and i < 2 and j >= 0 and j < s[i].len:
    s[i][j] = 5
    if s[i][j] == 5: symexTarget("hit")

proc nestAlias(x: int) =
  # A `var` copy: a `let` of memory written later keeps its decline
  # (`feUnsupportedOp`, whether ARC shares it is cursor inference's call).
  var s = @[@[1, 2], @[3, 4]]
  var t = s
  var u = s[1]
  s[1][0] = x
  if t[1][0] == 3 and u[0] == 3 and s[1][0] == x and x == 9:
    symexTarget("hit")

proc nestAliasDead(x: int) =
  var s = @[@[1, 2], @[3, 4]]
  var t = s
  var u = s[1]
  s[1][0] = x
  if t[1][0] != 3 or u[0] != 3: symexTarget("hit")

proc nestLet(x: int) =
  var s = @[@[1, 2], @[3, 4]]
  let t = s
  s[1][0] = x
  if t[1][0] == 3 and s[1][0] == x and x == 9: symexTarget("hit")

proc flatLet(x: int) =
  var s = @[1, 2]
  let t = s
  s[0] = x
  if t[0] == 1 and s[0] == x and x == 9: symexTarget("hit")

proc ssField(h: HasSS) =
  if h.ss.len == 2 and h.ss[1].len == 1 and h.ss[1][0] == 7: symexTarget("hit")

proc ssFieldLenDead(h: HasSS) =
  if h.ss.len > 0 and h.ss[0].len < 0: symexTarget("hit")

proc ssFieldOob(h: HasSS) =
  if h.ss.len == 1 and h.ss[0][0] == 3: symexTarget("hit")

proc ssFieldCopy(h: HasSS; x: int) =
  var s = h.ss
  if s.len == 1 and s[0].len == 1:
    s[0][0] = x
    if s[0][0] == 5 and h.ss[0][0] != 5: symexTarget("hit")

proc ssFieldCopyDead(h: HasSS; x: int) =
  var s = h.ss
  if s.len == 1 and s[0].len == 1:
    let old = h.ss[0][0]
    s[0][0] = x
    if h.ss[0][0] != old or s[0][0] != x: symexTarget("hit")

proc ssParam(s: seq[seq[int]]) =
  if s.len == 1 and s[0].len == 1 and s[0][0] == 7: symexTarget("hit")

proc ssParamDead(s: seq[seq[int]]) =
  if s.len > 0 and s[0].len < 0: symexTarget("hit")

proc ssPop(s: seq[seq[int]]) =
  var t = s
  if t.len > 0:
    let x = t.pop()
    if x.len == 2: symexTarget("hit")

proc ssPopDead(s: seq[seq[int]]) =
  # `pop` reads the last inner seq with no element read's well-formedness
  # facts: its length is non-negative only through `seqElemAt`'s clamp.
  var t = s
  if t.len > 0:
    let x = t.pop()
    if x.len < 0: symexTarget("hit")

proc nestRead(i: int) =
  let s = @[@[1, 2], @[3]]
  if i >= 0 and i < 2 and s[i].len == 1 and s[i][0] == 3: symexTarget("hit")

proc nestReadDead(i: int) =
  let s = @[@[1, 2], @[3]]
  if i >= 0 and i < 2 and s[i].len == 1 and s[i][0] != 3: symexTarget("hit")

proc nestNewSeq(x: int) =
  var s = newSeq[seq[int]](2)
  s[1].add x
  if s[1].len == 1 and s[0].len == 0 and s[1][0] == 4: symexTarget("hit")

proc nestNewSeqDead(x: int) =
  var s = newSeq[seq[int]](2)
  if s[0].len != 0 or s[1].len < 0: symexTarget("hit")

suite "RFC-0016 PRC-34 / PRC-23: a seq of seqs":
  test "native":
    check native(nestStore(7)) == "hit"
    check native(nestStore(8)) == "ran"
    for v in [low(int), 0, 7, high(int)]:
      check native(nestStoreDead(v)) == "ran"
    check native(nestOuterOob(1)) == "hit"
    check native(nestOuterOob(2)) == "IndexDefect"
    check native(nestOuterOob(-1)) == "IndexDefect"
    check native(nestInnerOob(0)) == "hit"
    check native(nestInnerOob(1)) == "IndexDefect"
    for v in [low(int), -1, 0, 1, 2, high(int)]:
      check native(nestOuterOobDead(v)) in ["ran", "IndexDefect"]
      check native(nestInnerOobDead(v)) in ["ran", "IndexDefect"]
    for i in -1 .. 2:
      for j in -1 .. 2:
        check native(nestInBounds(i, j)) in ["hit", "ran"]
    check native(nestAlias(9)) == "hit"
    for v in [low(int), 0, 9, high(int)]:
      check native(nestAliasDead(v)) == "ran"
    check native(nestRead(1)) == "hit"
    check native(nestNewSeq(4)) == "hit"
    check native(nestNewSeq(5)) == "ran"
    check native(nestNewSeqDead(0)) == "ran"
    for i in -1 .. 2:
      check native(nestReadDead(i)) == "ran"
    check native(nestLet(9)) == "hit"
    check native(flatLet(9)) == "hit"
    check native(ssField(HasSS(ss: @[newSeq[int](), @[7]]))) == "hit"
    check native(ssField(HasSS(ss: @[newSeq[int](), @[8]]))) == "ran"
    check native(ssFieldLenDead(HasSS(ss: @[newSeq[int]()]))) == "ran"
    check native(ssFieldOob(HasSS(ss: @[@[3]]))) == "hit"
    check native(ssFieldOob(HasSS(ss: @[newSeq[int]()]))) == "IndexDefect"
    check native(ssFieldCopy(HasSS(ss: @[@[1]]), 5)) == "hit"
    check native(ssFieldCopyDead(HasSS(ss: @[@[1]]), 5)) == "ran"
    check native(ssParam(@[@[7]])) == "hit"
    check native(ssParamDead(@[newSeq[int]()])) == "ran"
    check native(ssPop(@[@[1, 2]])) == "hit"
    check native(ssPopDead(@[newSeq[int]()])) == "ran"
  test "an in-bounds store: reached":
    decides(nestStore, sxSat)
  test "an in-bounds store: unreachable":
    decides(nestStoreDead, sxUnsat)
  test "an out-of-bounds outer index raises IndexDefect":
    let r = symexFind(nestOuterOob, tRaisedExn("IndexDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "an out-of-bounds inner index raises IndexDefect":
    let r = symexFind(nestInnerOob, tRaisedExn("IndexDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "the in-bounds outer index reaches the store":
    decides(nestOuterOob, sxSat)
  test "the store itself checks the outer index":
    # No path passes the store with the index out of bounds: the label is
    # unreached (an unchecked store would make it `sxSat`), and what is left
    # is the store's own `IndexDefect`.
    let r = symexFind(nestOuterOobDead, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "the in-bounds inner index reaches the store":
    decides(nestInnerOob, sxSat)
  test "the store itself checks the inner index":
    # No path passes the store with the index out of bounds: the label is
    # unreached (an unchecked store would make it `sxSat`), and what is left
    # is the store's own `IndexDefect`.
    let r = symexFind(nestInnerOobDead, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "indexes checked in bounds raise nothing":
    let r = symexFind(nestInBounds, tRaisedExn("IndexDefect"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    decides(nestInBounds, sxSat)
  test "a copy before the store keeps its value: reached":
    decides(nestAlias, sxSat)
  test "a copy before the store keeps its value: unreachable":
    decides(nestAliasDead, sxUnsat)
  test "a symbolic outer index reads an inner seq: reached":
    decides(nestRead, sxSat)
  test "a symbolic outer index reads an inner seq: unreachable":
    decides(nestReadDead, sxUnsat)
  test "newSeq of seqs, then add to an inner seq: reached":
    decides(nestNewSeq, sxSat)
  test "newSeq of seqs holds empty inner seqs":
    decides(nestNewSeqDead, sxUnsat)
  test "a `let` of a seq of seqs written later declines (PRC-05)":
    # `let t = s` shares the memory under `--mm:refc`, and under orc and arc
    # when cursor inference proves it; a copy otherwise (this build: a copy,
    # the native run). The decline is `letCursorDecline`'s, general to any
    # seq (`flatLet`), and PRC-05 owns it.
    for f in [symexFind(nestLet, tLabel("hit")), symexFind(flatLet, tLabel("hit"))]:
      checkpoint show(f.errors)
      check f.status == sxUnknown
      check f.errors.named(feUnsupportedOp)
  test "a seq of seqs field of a parameter: reached":
    decides(ssField, sxSat)
  test "a seq of seqs field of a parameter: no negative inner length":
    decides(ssFieldLenDead, sxUnsat)
  test "a seq of seqs field of a parameter: an empty inner seq raises":
    let r = symexFind(ssFieldOob, tRaisedExn("IndexDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "a seq of seqs field of a parameter: in bounds reached":
    decides(ssFieldOob, sxSat)
  test "a store into a copy of a parameter's seq of seqs: reached":
    decides(ssFieldCopy, sxSat)
  test "a store into a copy leaves the parameter: unreachable":
    decides(ssFieldCopyDead, sxUnsat)
  test "a seq of seqs parameter: reached":
    decides(ssParam, sxSat)
  test "a seq of seqs parameter: no negative inner length":
    decides(ssParamDead, sxUnsat)
  test "pop of a seq of seqs parameter: reached":
    decides(ssPop, sxSat)
  test "pop of a seq of seqs parameter: no negative inner length":
    decides(ssPopDead, sxUnsat)

suite "RFC-0016 PRC-34: record ==":
  test "native":
    check native(tupEq(3, 3)) == "hit"
    check native(tupEq(3, 4)) == "ran"
    for v in [low(int), 5, 6, high(int)]:
      check native(tupEqDead(v)) == "ran"
    check native(tupNe(3, 4)) == "hit"
    check native(objEq(2, 1)) == "hit"
    check native(mixedEq(-3, 'q', "ab")) == "hit"
    check native(mixedEq(-3, 'q', "abc")) == "ran"
    check native(nanEq(NaN)) == "hit"
    check native(nanEq(1.0)) == "ran"
    check native(distinctField(12, 15)) == "hit"
    check native(nestedRecord(4)) == "hit"
    check native(nestedRecord(5)) == "ran"
    for v in [low(int), 4, 5, high(int)]:
      check native(nestedRecordDead(v)) == "ran"
    check native(nestedUserEq(12, 15)) == "hit"
    check native(nestedUserEq(12, 25)) == "ran"
    check native(nestedUserEqDead(12, 15)) == "ran"
    check native(nestedUserEqDead(12, 25)) == "ran"
    check native(tupleUserEq(3, 2)) == "hit"
    check native(enumField(1)) == "hit"
    check native(enumField(0)) == "ran"
  test "a tuple: reached":
    decides(tupEq, sxSat)
  test "a tuple, `!=`: reached":
    decides(tupNe, sxSat)
  test "a tuple: unreachable":
    decides(tupEqDead, sxUnsat)
  test "a plain object: reached":
    decides(objEq, sxSat)
  test "every atom kind: reached":
    decides(mixedEq, sxSat)
  test "a NaN field: unequal to itself":
    decides(nanEq, sxSat)
  # Step 5: a record with a non-atom field walks the compiler's instance of
  # system's `==`, so each field compares with the `==` Nim resolved for it.
  test "a distinct field follows its user `==`":
    decides(distinctField, sxSat)
  test "an enum field follows its user `==`":
    decides(enumField, sxSat)
  test "a nested plain record: reached":
    decides(nestedRecord, sxSat)
  test "a nested plain record: unreachable":
    decides(nestedRecordDead, sxUnsat)
  test "a nested object follows its user `==`: reached":
    decides(nestedUserEq, sxSat)
  test "a nested object follows its user `==`: unreachable":
    decides(nestedUserEqDead, sxUnsat)
  test "a named tuple field follows its user `==`":
    decides(tupleUserEq, sxSat)

suite "RFC-0016 PRC-34: whole-seq ==":
  test "native":
    check native(seqEqLit(1, 2)) == "hit"
    check native(seqEqLit(1, 3)) == "ran"
    for v in [low(int), 0, high(int)]:
      check native(seqEqLenDead(v)) == "ran"
    check native(seqNe(3)) == "hit"
    check native(seqNe(4)) == "ran"
    check native(seqEqParam(@[3, 4])) == "hit"
    check native(seqEqParam(@[3, 4, 5])) == "ran"
    check native(seqEqParam(@[3])) == "ran"
    check native(seqEqParamDead(@[3, 4])) == "ran"
    check native(seqEqParamElemDead(@[3, 4])) == "ran"
    check native(seqEqSym(@[1, 5], @[1, 5])) == "hit"
    check native(seqEqSym(@[1, 5], @[1, 5, 0])) == "ran"
    check native(seqEqSymDead(@[1, 5], @[1, 5])) == "ran"
    check native(seqEqSymLenDead(@[], @[])) == "ran"
    check native(seqNeSymDead(@[4], @[4])) == "ran"
    check native(seqNeSymDead(@[4], @[5])) == "ran"
    check native(seqEqLoop(@[1, 2], @[1, 2])) == "hit"
    check native(seqEqLoop(@[1, 2], @[1, 3])) == "ran"
    check native(seqEqLoopDead(@[1, 2], @[1, 2])) == "ran"
    check native(seqStrSym(@["ab"], @["ab"])) == "hit"
    check native(seqStrSym(@["ab"], @["a"])) == "ran"
    check native(seqStrSymDead(@["ab"], @["ab"])) == "ran"
    check native(seqFloatSym(@[1.0], @[1.0])) == "hit"
    check native(seqFloatSym(@[NaN], @[NaN])) == "ran"
    check native(seqFloatSym(@[0.0], @[-0.0])) == "hit"
    check native(seqEqBranch(true, @[1, 2])) == "hit"
    check native(seqEqBranch(false, @[1])) == "ran"
    check native(seqEqIdx(0, @[1, 2])) == "hit"
    check native(seqEqIdx(1, @[1])) == "ran"
    check native(seqNeIdx(0, @[1, 5])) == "hit"
    check native(seqNeIdxDead(1, @[1])) == "ran"
    check native(seqNeIdxDead(0, @[1])) == "ran"
    check native(seqNan(NaN)) == "hit"
    check native(seqNan(1.0)) == "ran"
    check native(seqStrEq("ab", 'q')) == "hit"
    check native(seqStrEq("abc", 'q')) == "ran"
    check native(seqStrEqDead("ab")) == "ran"
    check native(seqEnum(1)) == "hit"
    check native(seqNested(4)) == "hit"
  test "literals: reached":
    decides(seqEqLit, sxSat)
  test "literals of unequal lengths: unreachable":
    decides(seqEqLenDead, sxUnsat)
  test "`!=`: reached":
    decides(seqNe, sxSat)
  test "a parameter against a literal: reached":
    decides(seqEqParam, sxSat)
  test "a parameter against a literal fixes its length":
    decides(seqEqParamDead, sxUnsat)
  test "a parameter against a literal fixes its elements":
    decides(seqEqParamElemDead, sxUnsat)
  # Two seqs with no length bound in the term compare as equal lengths and
  # equal masked data arrays (a lambda term, no `forall`: the G4 hang
  # lesson).
  test "two parameters with no length bound: reached":
    decides(seqEqSym, sxSat)
  test "two parameters with no length bound: elements unreachable":
    decides(seqEqSymDead, sxUnsat)
  test "two parameters with no length bound: lengths unreachable":
    decides(seqEqSymLenDead, sxUnsat)
  test "equal seqs are not unequal past their length":
    decides(seqNeSymDead, sxUnsat)
  test "inside a loop: reached":
    decides(seqEqLoop, sxSat)
  test "inside a loop: unreachable":
    decides(seqEqLoopDead, sxUnsat)
  test "string elements with no length bound: reached":
    decides(seqStrSym, sxSat)
  test "string elements with no length bound: unreachable":
    decides(seqStrSymDead, sxUnsat)
  test "float elements with no length bound decline (IEEE `==`)":
    let r = symexFind(seqFloatSym, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feUnsupportedOp)
  test "a branch-merged length bounds the unroll: reached":
    decides(seqEqBranch, sxSat)
  test "an indexed element's `ite` length bounds the unroll: reached":
    decides(seqEqIdx, sxSat)
  test "an indexed element's `ite` length: unrolled to the larger arm":
    decides(seqNeIdx, sxSat)
  test "an indexed element's `ite` length: guarded past the length":
    decides(seqNeIdxDead, sxUnsat)
  test "a NaN element: unequal to itself":
    decides(seqNan, sxSat)
  test "string and char elements: reached":
    decides(seqStrEq, sxSat)
  test "string elements: unreachable":
    decides(seqStrEqDead, sxUnsat)
  test "an enum element with a user `==` declines":
    let r = symexFind(seqEnum, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feUnsupportedOp)
  test "a nested seq declines":
    let r = symexFind(seqNested, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feUnsupportedOp)

suite "RFC-0016 PRC-34: a type section in a routine body":
  test "native":
    check native(typeSection(5)) == "hit"
    check native(typeSectionDead(5)) == "ran"
  test "reached":
    decides(typeSection, sxSat)
  test "unreachable":
    decides(typeSectionDead, sxUnsat)

suite "RFC-0016 PRC-34: shapes later slices modelled":
  test "native":
    check native(aliasWhole(7)) == "hit"
    check native(injectParam(5)) == "hit"
    check native(nestedAddr(7)) == "hit"
    check native(seqFieldWrite(7)) == "hit"
  test "an alias across a whole assignment":
    decides(aliasWhole, sxSat)
  test "a parameter pragma":
    decides(injectParam, sxSat)
  test "a nested address":
    decides(nestedAddr, sxSat)
  test "a field write through a seq element":
    decides(seqFieldWrite, sxSat)

suite "RFC-0016 S8cp-r: walker version":
  test "symexWalkerVersion is at least 400":
    check parseInt(symexWalkerVersion) >= 400
