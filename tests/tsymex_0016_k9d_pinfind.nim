## RFC-0016 K9d -- `pinFind`, the generator that pins a suite's own
## `symexFind` call (W-54).
##
## `pinFind(fn, target, settings)` is `symexFind` with the same arguments and
## the same result, plus K9a's differential judgement of that result: a
## definite verdict (trusted `sxSat`, `sxUnsat`, `sxRaised`) is reproduced
## natively and written as a pin record; anything else (a decline, an untrusted
## or undefined-behaviour claim, a witness unsafe to run in-process) is
## returned as it came, with no record. The `sxUnsat` domain is generated per
## parameter from its type (`boundaryOf`): exhaustive for `bool` and for an
## ordinal of at most 256 values, the boundary sample otherwise. The cell is
## `family:generic:k9d/<file>/<fn>/<target>`, so the record says which suite
## and which call it evidences.
import std/[unittest, os, strutils, sequtils]
import nelli/symex
import ./s8cu_helpers

let pinTmp = getTempDir() / ("k9d_pinfind_" & $getCurrentProcessId())
createDir(pinTmp)
# Private, as in K9a's file: the tests count this file's records.
putEnv("NELLI_PIN_DIR", pinTmp)

proc records(): seq[PinRecord] =
  for r in pinRecords(pinTmp): result.add r

proc recordsWith(part: string): seq[PinRecord] =
  records().filterIt(part in it.cell.key)

proc sutHit(x: int) =
  if x == 7: symexTarget("hit")

proc sutNever(x: int) =
  if x > 5 and x < 3: symexTarget("hit")

proc sutBool(a, b: bool) =
  if a and not a and b: symexTarget("hit")

proc sutI8(x: int8) =
  if x > 100 and x < 101: symexTarget("hit")

proc sutRange(x: range[3 .. 9]; y: int) =
  if x == 2: symexTarget("hit")

proc sutWide(x: range[0'u64 .. 5_000_000_000'u64]; y: range[1 .. 1_000_000]) =
  if x > 5_000_000_000'u64 or y > 1_000_000: symexTarget("hit")

proc sutVar(x: var int) =
  if x == 4 and x == 5: symexTarget("hit")
  x = 1

proc sutRet(x: int): int =
  if x == 9: symexTarget("hit")
  x + 1

proc sutRaise(x: int) =
  if x == 3: raise newException(ValueError, "three")

type
  Color = enum cRed, cGreen, cBlue
  Holey = enum hA = 1, hB = 5, hC = 9
  Cents = distinct int
  Tiny = distinct int8
  Flag = distinct bool

proc sutEnum(c: Color; n: int) =
  if c == cBlue and n == 2 and c == cRed: symexTarget("hit")

proc sutHoley(h: Holey) =
  if ord(h) == 5: symexTarget("hit")

proc sutDistinct(c: Cents) =
  if int(c) > 5 and int(c) < 3: symexTarget("hit")

proc sutTiny(t: Tiny) =
  if int(t) > 100 and int(t) < 101: symexTarget("hit")

# symexAssume: the walker restricts to the assumption; the native replay must
# reject a run that violates it.
proc sutAssumeUnsat(x: int) =
  symexAssume(x < 5)
  if x == 7: symexTarget("hit")

proc sutAssumeSat(x: int) =
  symexAssume(x > 5)
  if x == 7: symexTarget("hit")

proc sutAssumeAll(x: int) =
  symexAssume(x == 1000)
  if x == 7: symexTarget("hit")


proc sutAssumeSwallow(x: int) =
  try:
    symexAssume(x < 5)
  except Exception:
    discard
  if x == 7: symexTarget("hit")

# K9d-5: tuple, object and variant-object parameters (field-product domain).
type
  Pt = object
    x: int
    flag: bool
    c: Color
  Shape = object
    common: int8
    case k: Color
    of cRed: a: int
    of cGreen: b: bool
    else: c: int8
  Wide = object
    f0, f1, f2, f3, f4, f5: int
  Nested = tuple[p: Pt, n: int8]
  BoolColor = (bool, Color)
  IntBool = (int, bool)

proc sutTuple(t: (int, bool)) =
  if t[0] > 5 and t[0] < 3: symexTarget("hit")

proc sutTupleSat(t: (int, bool)) =
  if t[0] == 123_456 and t[1]: symexTarget("hit")

proc sutObject(p: Pt) =
  if p.x > 5 and p.x < 3 and p.flag: symexTarget("hit")

proc sutObjectSat(p: Pt) =
  if p.x == 4242 and p.c == cBlue: symexTarget("hit")

proc sutVariant(s: Shape) =
  if s.k == cRed and s.a > 5 and s.a < 3: symexTarget("hit")

proc sutWideObj(w: Wide) =
  if w.f0 > 5 and w.f0 < 3: symexTarget("hit")

proc sutNested(n: Nested) =
  if n.p.x > 5 and n.p.x < 3: symexTarget("hit")

type
  Flip = object
    case on: bool
    of true: x: int
    of false: y: int8

proc sutFlip(f: Flip) =
  if f.on and f.x > 5 and f.x < 3: symexTarget("hit")

proc sutSix(a, b, c, d, e, f: int) =
  if a > 5 and a < 3 and (b + c + d + e + f) == 0: symexTarget("hit")

# K9d-6: string and cstring parameters (literal-mined domain).
proc strHelper(s: string): bool =
  s == "helper-lit"

proc sutStrLit(s: string; n: int) =
  if s == "foo" and n > 5 and n < 3: symexTarget("hit")
  if s.len > 0 and s[0] == 'q' and s.len == 17: discard
  if strHelper(s): discard
  case s
  of "alpha": discard
  else: discard

proc sutStrUnsat(s: string) =
  if s.startsWith("config") and s.len > 9 and s.len < 3: symexTarget("hit")

proc sutStrSat(s: string) =
  if s.len == 4 and s[1] == '\x9C' and s[3] == 'k': symexTarget("hit")

proc sutStrTuple(t: (string, bool)) =
  if t[0] == "needle" and t[1] and not t[1]: symexTarget("hit")

type StrObj = object
  name: string
  n: int8

proc sutStrObj(o: StrObj) =
  if o.name == "obj-lit" and o.n > 5 and o.n < 3: symexTarget("hit")

proc sutStrTwo(a, b: string) =
  if a == "one" and b == "two" and a == "x": symexTarget("hit")

proc sutCstr(s: cstring) =
  if s == "cs-lit" and s == "other": symexTarget("hit")

# The bug sits at a literal's neighbour: it fires on "config" with its last
# byte removed, which only a neighbour-aware domain reaches.
proc sutNeighbour(s: string) =
  if s == "confi": symexTarget("hit")


suite "K9d: pinFind":
  test "boundaryOf: exhaustive for bool and a small ordinal, sampled for int":
    check boundaryOf(bool).exhaustive
    check boundaryOf(bool).values == @[false, true]
    check boundaryOf(int8).exhaustive
    check boundaryOf(int8).values.len == 256
    check boundaryOf(range[3 .. 9]).values == @[3, 4, 5, 6, 7, 8, 9].mapIt(range[3 .. 9](it))
    check not boundaryOf(int).exhaustive
    check boundaryOf(int).values == boundaryInts.values
    check low(uint64) in boundaryOf(uint64).values
    check high(uint64) in boundaryOf(uint64).values

  test "a sat verdict is returned as symexFind's and pinned on its witness":
    let r = pinFind(sutHit, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 7
    let rs = recordsWith("/sutHit/")
    check rs.len == 1
    if rs.len == 1:
      check rs[0].cell.scope == faGeneric
      check rs[0].cell.key == "k9d/tsymex_0016_k9d_pinfind/sutHit/tLabel(\"hit\")"
      check rs[0].entry == "symexFind"
      check rs[0].verdict == pvExact
      check rs[0].walker == "sxSat"

  test "an unsat verdict is pinned over the generated domain":
    check pinFind(sutNever, tLabel("hit")).status == sxUnsat
    check pinFind(sutBool, tLabel("hit")).status == sxUnsat
    check pinFind(sutI8, tLabel("hit")).status == sxUnsat
    let n = recordsWith("/sutNever/")
    check n.len == 1 and not n[0].exhaustive and "[8]" in n[0].domain
    let b = recordsWith("/sutBool/")
    check b.len == 1 and b[0].exhaustive and "[4]" in b[0].domain
    let i = recordsWith("/sutI8/")
    check i.len == 1 and i[0].exhaustive and "[256]" in i[0].domain

  test "mixed parameter types, a range, a var parameter, a result":
    check pinFind(sutRange, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutRange/").len == 1
    check pinFind(sutVar, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutVar/").len == 1
    check pinFind(sutRet, tLabel("hit")).status == sxSat
    check recordsWith("/sutRet/").len == 1

  test "a raise verdict is pinned on its raising witness":
    let r = pinFind(sutRaise, tRaisedExn("ValueError"))
    check r.status == sxRaised or r.status == sxSat
    let rs = recordsWith("/sutRaise/")
    check rs.len == 1
    if rs.len == 1: check rs[0].verdict in {pvExact, pvRaised}

  test "the suite's own settings reach symexFind":
    const s = block:
      var s = defaultSymexSettings()
      s.budget.queryTimeoutMs = 0
      s
    check pinFind(sutHit, tLabel("hit"), s).status == sxSat
    check recordsWith("/sutHit/").len == 2

  test "a wide range parameter is generated and replayed at its declared type":
    ## the witness tuple holds a range as its base type, so the domain must
    ## come from the declared type or a native call would raise on conversion
    check pinFind(sutWide, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutWide/").len == 1

  test "boundaryOf an enum: every declared value, holes excluded":
    check boundaryOf(Color).exhaustive
    check boundaryOf(Color).values == @[cRed, cGreen, cBlue]
    check boundaryOf(Holey).exhaustive
    check boundaryOf(Holey).values == @[hA, hB, hC]

  test "boundaryOf a distinct type: its base type's domain, converted":
    check boundaryOf(Tiny).exhaustive
    check boundaryOf(Tiny).values.len == 256
    check boundaryOf(Flag).values.len == 2
    check not boundaryOf(Cents).exhaustive
    check boundaryOf(Cents).values.mapIt(int(it)) == boundaryInts.values

  test "enum, holey enum and distinct parameters are pinned":
    check pinFind(sutEnum, tLabel("hit")).status == sxUnsat
    check pinFind(sutHoley, tLabel("hit")).status == sxSat
    check pinFind(sutDistinct, tLabel("hit")).status == sxUnsat
    check pinFind(sutTiny, tLabel("hit")).status == sxUnsat
    let e = recordsWith("/sutEnum/")
    check e.len == 1 and not e[0].exhaustive and "[24]" in e[0].domain
    check "exhaustive[3]{cRed,cGreen,cBlue}" in e[0].domain
    check recordsWith("/sutHoley/").len == 1
    let t = recordsWith("/sutTiny/")
    check t.len == 1 and t[0].exhaustive and "[256]" in t[0].domain

  test "symexAssume: an unsat verdict that holds only under the assumption is pinned":
    check pinFind(sutAssumeUnsat, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutAssumeUnsat/").len == 1

  test "symexAssume: a sat witness satisfies the assumption and hits":
    let r = pinFind(sutAssumeSat, tLabel("hit"))
    check r.status == sxSat
    check recordsWith("/sutAssumeSat/").len == 1

  test "symexAssume: a domain every run of which is rejected fails the pin":
    ## the assumption holds only at 1000, outside the boundary sample
    check symexFind(sutAssumeAll, tLabel("hit")).status == sxUnsat
    expect PinFailure:
      discard pinFind(sutAssumeAll, tLabel("hit"))

  test "symexAssume: a SUT that catches every exception stays rejected":
    check pinFind(sutAssumeSwallow, tLabel("hit")).status == sxUnsat

  test "symexAssume: outside a pin it is unchanged (no raise, no state)":
    sutAssumeUnsat(7)
    symexAssume(false)
    let nr = nativeRun(sutAssumeUnsat(7))
    check nr.rejected
    check nr.hits.len == 0 and nr.raised.len == 0
    symexAssume(false)   # the gate is closed again after the run
    check not nativeRun(sutAssumeUnsat(1)).rejected

  test "pairwiseRows: every pair of values across two fields is in some row":
    for sizes in [@[2, 3], @[8, 8, 8, 8, 8, 8], @[3, 1, 5, 2], @[4], @[]]:
      let rows = pairwiseRows(sizes)
      check rows.len >= 1
      for i in 0 ..< sizes.len:
        for j in i + 1 ..< sizes.len:
          for a in 0 ..< sizes[i]:
            for b in 0 ..< sizes[j]:
              check rows.anyIt(it[i] == a and it[j] == b)
    check pairwiseRows(@[8, 8, 8, 8, 8, 8]).len < 1000
    check pairwiseRows(@[8, 8, 8, 8, 8, 8]) == pairwiseRows(@[8, 8, 8, 8, 8, 8])

  test "boundaryOf a tuple: the field product, exhaustive when its fields are":
    let d = boundaryOf(BoolColor)
    check d.exhaustive and d.values.len == 6
    check (true, cBlue) in d.values
    let m = boundaryOf(IntBool)
    check not m.exhaustive and m.values.len == 16

  test "boundaryOf an object: the field product, each field its own domain":
    let d = boundaryOf(Pt)
    check not d.exhaustive and d.values.len == 8 * 2 * 3
    check Pt(x: high(int), flag: true, c: cBlue) in d.values

  test "boundaryOf a variant object: each branch with its discriminator":
    let d = boundaryOf(Shape)
    check d.values.anyIt(it.k == cRed and it.a == 7)
    check d.values.anyIt(it.k == cGreen and it.b)
    check d.values.anyIt(it.k == cBlue and it.c == 127'i8)
    check d.values.anyIt(it.k == cBlue and it.common == -128'i8)
    # branch fields pair with the common field: 3 branches, 256 x ... capped
    check d.values.len > 0

  test "boundaryOf a large object is pairwise, bounded, and records its size":
    let d = boundaryOf(Wide)
    check not d.exhaustive
    check d.values.len < fieldProductFull
    check d.values.len >= 64
    for i in 0 ..< 8:
      for j in 0 ..< 8:
        let a = boundaryInts.values[i]
        let b = boundaryInts.values[j]
        check d.values.anyIt(it.f0 == a and it.f5 == b)
        check d.values.anyIt(it.f2 == a and it.f3 == b)

  test "tuple and object parameters are pinned over the field product":
    check pinFind(sutTuple, tLabel("hit")).status == sxUnsat
    check pinFind(sutObject, tLabel("hit")).status == sxUnsat
    check pinFind(sutVariant, tLabel("hit")).status == sxUnsat
    check pinFind(sutWideObj, tLabel("hit")).status == sxUnsat
    check pinFind(sutNested, tLabel("hit")).status == sxUnsat
    let t = recordsWith("/sutTuple/")
    check t.len == 1 and not t[0].exhaustive and "sampled[16]" in t[0].domain
    let o = recordsWith("/sutObject/")
    check o.len == 1 and "[48]" in o[0].domain
    check recordsWith("/sutVariant/").len == 1
    check recordsWith("/sutNested/").len == 1
    let w = recordsWith("/sutWideObj/")
    check w.len == 1 and not w[0].exhaustive

  test "a sat witness outside the pairwise set is still replayed exactly":
    let t = pinFind(sutTupleSat, tLabel("hit"))
    check t.status == sxSat
    check t.witness[0][0] == 123_456
    check not boundaryOf(IntBool).values.anyIt(it[0] == 123_456)
    let r = pinFind(sutObjectSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].x == 4242
    check recordsWith("/sutTupleSat/").len == 1
    check recordsWith("/sutObjectSat/").len == 1

  test "a parameter product beyond the cap is an all-pairs array over the parameters":
    check pinFind(sutSix, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutSix/")
    check r.len == 1 and not r[0].exhaustive
    check "sampled[" in r[0].domain and "sampled[65536]" notin r[0].domain

  test "a large exhaustive field is thinned only when the product is too large":
    check boundaryOf(Shape).values.len > 0
    let blue = boundaryOf(Shape).values.filterIt(it.k == cBlue)
    check blue.len == 81
    check blue.anyIt(it.common == low(int8) and it.c == high(int8))
    check boundaryOf(Shape).values.filterIt(it.k == cRed).len == 256 * 8

  test "a variant object whose case has no else is generated branch by branch":
    let d = boundaryOf(Flip)
    check d.values.anyIt(it.on and it.x == 7)
    check d.values.anyIt(not it.on and it.y == 127'i8)
    check d.values.len == 8 + 256
    check pinFind(sutFlip, tLabel("hit")).status == sxUnsat


  test "string literals and char literals of the SUT are harvested":
    let h = harvestLiterals(sutStrLit)
    check "foo" in h.strs and "alpha" in h.strs
    check "q" in h.strs                    # a char literal
    check "helper-lit" in h.strs           # followed into a helper
    check "hit" notin h.strs               # a symexTarget label is not data
    check 17 in h.ints and 5 in h.ints

  test "boundaryOf string: the fixed core, bounded and deterministic":
    clearStringHints()
    let d = boundaryOf(string)
    check not d.exhaustive
    check "" in d.values
    for c in ['\0', 'a', 'z', '0', '9', ' ', '-', '\x7F', '\x80', '\xFF']:
      check $c in d.values
    check "\xC3\xA9" in d.values and "\xE2\x82\xAC" in d.values
    check d.values.anyIt(it.len == 3 and it[0] == '\0')
    check d.values.len <= stringDomainCap
    check boundaryOf(string).values == d.values
    check d.values.deduplicate.len == d.values.len

  test "boundaryOf string with hints: each literal, its neighbours and its thresholds":
    setStringHints(harvestLiterals(sutStrUnsat))
    let d = boundaryOf(string)
    clearStringHints()
    check "config" in d.values
    check "confi" in d.values and "onfig" in d.values        # prefix, suffix
    check "configa" in d.values and "config\0" in d.values   # one byte appended
    check "confg" in d.values                                # one byte removed
    check "confih" in d.values                               # one byte changed
    check "CONFIG" in d.values
    check d.values.anyIt(it.len == 9) and d.values.anyIt(it.len == 10)
    check d.values.anyIt(it.len == 8)
    check d.values.len <= stringDomainCap

  test "the string domain is bounded however many literals the SUT holds":
    var strs: seq[string]
    for i in 0 ..< 200: strs.add "literal-number-" & $i
    setStringHints(StringHints(strs: strs, ints: @[3, 64, 1000]))
    let d = boundaryOf(string)
    clearStringHints()
    check d.values.len <= stringDomainCap
    check "literal-number-0" in d.values
    check "" in d.values

  test "boundaryOf cstring: the string set without an embedded NUL":
    setStringHints(StringHints(strs: @["cs-lit", "a\0b"], ints: @[]))
    let d = boundaryOf(cstring)
    clearStringHints()
    check not d.exhaustive
    check d.values.len > 100
    check d.values.allIt(it.len == ($it).len)   # no NUL cut a value short
    check "cs-lit" in d.values.mapIt($it)
    check "cs-lit".cstring in d.values

  test "a string sat witness outside the domain is still replayed exactly":
    let r = pinFind(sutStrSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 4
    check not boundaryOf(string).values.anyIt(it == r.witness[0])
    check recordsWith("/sutStrSat/").len == 1

  test "a string unsat verdict is pinned over the literal-mined domain":
    check pinFind(sutStrUnsat, tLabel("hit")).status == sxUnsat
    let r = recordsWith("/sutStrUnsat/")
    check r.len == 1 and not r[0].exhaustive
    check "sampled[" in r[0].domain
    # the record is text: a NUL or a high byte in the domain shows escaped
    check r[0].domain.allIt(it in {' ' .. '~'})
    check pinFind(sutStrLit, tLabel("hit")).status == sxUnsat
    # the walker declines a cstring parameter: returned as it came, no record
    check pinFind(sutCstr, tLabel("hit")).status == sxUnknown
    check recordsWith("/sutCstr/").len == 0

  test "a planted unsat claim over a literal's neighbour is refused":
    ## sutNeighbour hits on "confi", reachable only as "config" minus a byte;
    ## the harvested neighbour finds it where the fixed core cannot
    type W = tuple[s: string]
    let key = cellKey(faGeneric, "k9d6/neighbour")
    let settled = Soundness(replay: rsNotNeeded)
    let lie = SymexResult[W](status: sxUnsat, soundness: settled)
    setStringHints(StringHints(strs: @["config"], ints: @[]))
    let dom = boundaryOf(string)
    clearStringHints()
    check "confi" in dom.values
    expect PinFailure:
      discard pinExactOn(sutNeighbour, lie, key, domain = dom)
    check "confi" notin boundaryOf(string).values

  test "strings inside a tuple, an object and beside another string":
    check pinFind(sutStrTuple, tLabel("hit")).status == sxUnsat
    check pinFind(sutStrObj, tLabel("hit")).status == sxUnsat
    check pinFind(sutStrTwo, tLabel("hit")).status == sxUnsat
    let t = recordsWith("/sutStrTuple/")
    check t.len == 1 and not t[0].exhaustive
    let o = recordsWith("/sutStrObj/")
    check o.len == 1
    let w = recordsWith("/sutStrTwo/")
    check w.len == 1
    # the pair of strings stays inside the run cap, thinned not truncated
    check "sampled[" in w[0].domain and "sampled[65536]" notin w[0].domain

  test "the hints do not outlive a pinFind call":
    discard pinFind(sutStrUnsat, tLabel("hit"))
    check "config" notin boundaryOf(string).values
