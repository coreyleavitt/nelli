## RFC-0005 slice S8cn -- what Nim does, on each memory manager, for the shapes
## `tsymex_rfc0005_s8cn_lent` declines or keeps. No walker: run it under
## `--mm:refc`, `--mm:orc` and `--mm:arc`, with and without `-d:release`.
##
## `let c = s` shares under refc. Under orc and arc it shares over a by-value
## formal (cursor inference, `letFormal`) and copies a global or a local written
## in the routine: the same spelling gives both answers. A verdict either way
## holds under one setting. The loops give one answer on every setting, pinned
## here.
import std/[unittest, tables]

var gs: seq[int]
var gstr: string
var gt: Table[string, int]
proc wg() = gs[0] = 99
proc ws() = gstr[0] = 'z'
proc wt() = gt["a"] = 99

proc letCallee(): int =
  let c = gs
  wg()
  c[0]
proc letFormal(s: seq[int]): int =
  let c = s
  gs[0] = 99
  c[0]
proc letAndWritten(): int =
  gs = @[1]
  let c = gs
  gs[0] = 99
  c[0]
proc letLocal(): int =
  var s = @[1]
  let c = s
  s[0] = 99
  c[0]
proc letStr(): char =
  let c = gstr
  ws()
  c[0]
proc letTab(): int =
  let c = gt
  wt()
  c["a"]
proc varCallee(): int =
  var c = gs
  wg()
  c[0]
proc itemsSeq(): int =
  var s = @[1]
  for x in s:
    s[0] = 99
    return x
proc itemsOpen(a: openArray[int]): int =
  for x in a:
    gs[0] = 99
    return x
proc pairsSeq(): int =
  var s = @[1]
  for i, x in s:
    s[0] = 99
    return x
proc pairsObj(): int =
  var s = @[@[1]]
  for i, x in s:
    s[0][0] = 99
    return x[0]
proc itemsArr(): int =
  var a = [1, 2]
  for x in a:
    a[0] = 99
    return x
proc itemsStr(): char =
  var st = "ab"
  for c in st:
    st[0] = 'z'
    return c
proc tabValues(): int =
  var t = {"a": 1}.toTable
  for v in t.values:
    t["a"] = 99
    return v
proc tabPairs(): int =
  var t = {"a": 1}.toTable
  for k, v in t.pairs:
    t["a"] = 99
    return v
proc mitemsSeq(): int =
  var s = @[1]
  for x in s.mitems:
    s[0] = 99
    return x
proc mvaluesTab(): int =
  var t = {"a": 1}.toTable
  for v in t.mvalues:
    t["a"] = 99
    return v

suite "S8cn: a `let` over a container":
  setup:
    gs = @[1]
    gstr = "ab"
    gt = {"a": 1}.toTable
  when defined(gcRefc):
    test "refc: it shares":
      check letCallee() == 99
      check letFormal(gs) == 99
      gs = @[1]
      check letAndWritten() == 99
      check letLocal() == 99
      check letStr() == 'z'
      check letTab() == 99
  else:
    test "orc and arc: by what cursor inference proved":
      check letCallee() == 1
      gs = @[1]
      check letFormal(gs) == 99
      gs = @[1]
      check letAndWritten() == 1
      check letLocal() == 1
  test "a `var` copies on every setting":
    check varCallee() == 1

suite "S8cn: the loops, one answer on every setting":
  setup:
    gs = @[1]
  test "the element's memory":
    check itemsSeq() == 99
    check itemsOpen(gs) == 99
    check tabValues() == 99
    check mitemsSeq() == 99
    check mvaluesTab() == 99
  test "a scalar copied":
    check pairsSeq() == 1
    check itemsArr() == 1
    check itemsStr() == 'a'
    check tabPairs() == 1
  test "a non-scalar through `pairs`":
    check pairsObj() in [1, 99]   # the shape declines either way
