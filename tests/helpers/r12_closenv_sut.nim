## RFC-0016 W3-z R12. Module-level closure variables holding, when the run
## starts, a closure whose environment R11 declined: two or more captured
## values of one type, a value of a type declared outside the module the
## check runs in (this one, or the library's), and a closure of a routine
## nested in a nested one. Each opaque body names the routine that builds the
## closure (on a branch the witness does not take), so the route scan and the
## replay's footprint read it. Shared by the fork-mode suite
## (`tsymex_0016_w3z_r12_closenv`) and the re-executed one
## (`tsymex_0016_prc02_reexec`). This module declares no lifetime hook.
import std/tables
import nelli
import nelli/symex

var gR12Out*: int

# Two captured strings: values of one type, laid out as an array whichever
# order the compiler gives them.
var gStartStrPair*: proc (v: int): int
proc mkStartStrPair*() =
  var a = "abcde"
  var b = "xy"
  gStartStrPair = proc (v: int): int = v + a.len * 10 + b.len
proc runStartStrPair(v: int) {.symexOpaque.} =
  if v == 99: mkStartStrPair()
  gR12Out = gStartStrPair(v)
proc sutStartStrPair*(v: int) =
  symexAssume(v == 3)
  runStartStrPair(v)
  if gR12Out == 55: symexTarget("t")

# Three captured seq[int]s, one of whose elements makes an unchecked routine
# overflow: the slot that holds it must reach the child as itself.
var gStartSeqTrio*: proc (v: int): int
{.push overflowChecks: off.}
proc mkStartSeqTrio*() =
  var xs = @[1]
  var ys = @[high(int) - 2]
  var zs = @[7, 8]
  gStartSeqTrio = proc (v: int): int = v + ys[0] + xs.len * 0 + zs.len * 0
{.pop.}
proc runStartSeqTrio(v: int) {.symexOpaque.} =
  if v == 99: mkStartSeqTrio()
  gR12Out = gStartSeqTrio(v)
proc sutStartSeqTrio*(v: int) =
  symexAssume(v == 3)
  runStartSeqTrio(v)
  if gR12Out < 0: symexTarget("t")

# An object declared in this module, not the one the check runs in. The route
# scan declines it before the environment is read: the builder's code holds a
# value of a type of another module, whose copy hooks a probe outside that
# module cannot rule out (`routeProbeRead`).
type BoxR12* = object
  s: string
  n: int

var gStartForeignBox*: proc (v: int): int
proc mkStartForeignBox*() =
  var b = BoxR12(s: "abcd", n: 1)
  gStartForeignBox = proc (v: int): int = v + b.s.len + b.n
proc runStartForeignBox(v: int) {.symexOpaque.} =
  if v == 99: mkStartForeignBox()
  gR12Out = gStartForeignBox(v)
proc sutStartForeignBox*(v: int) =
  symexAssume(v == 3)
  runStartForeignBox(v)
  if gR12Out == 8: symexTarget("t")

# A library object: `system`'s `HSlice[string, string]`, whose hooks the
# compiler generates over its two strings.
var gStartSlice*: proc (v: int): int
proc mkStartSlice*() =
  var sl = "abcd" .. "xy"
  gStartSlice = proc (v: int): int = v + sl.a.len * 10 + sl.b.len
proc runStartSlice(v: int) {.symexOpaque.} =
  if v == 99: mkStartSlice()
  gR12Out = gStartSlice(v)
proc sutStartSlice*(v: int) =
  symexAssume(v == 3)
  runStartSlice(v)
  if gR12Out == 45: symexTarget("t")

# A library object: a `Table[int, string]`, whose hooks the compiler
# generates over a seq of tuples. Its lookup hashes with unchecked
# arithmetic, which the walk reports as possibly undefined.
var gStartTable*: proc (v: int): int
proc mkStartTable*() =
  var t = initTable[int, string]()
  t[1] = "abc"
  gStartTable = proc (v: int): int = v + t.getOrDefault(1).len
proc runStartTable(v: int) {.symexOpaque.} =
  if v == 99: mkStartTable()
  gR12Out = gStartTable(v)
proc sutStartTable*(v: int) =
  symexAssume(v == 3)
  runStartTable(v)
  if gR12Out == 6: symexTarget("t")

# A closure of a routine nested in a nested one: its environment links to
# the one of the routine enclosing its own.
var gStartNested*: proc (v: int): int
proc mkStartNested*() =
  var s = "abcd"
  proc mid() =
    var t = "xy"
    gStartNested = proc (v: int): int = v + s.len + t.len
  mid()
proc runStartNested(v: int) {.symexOpaque.} =
  if v == 99: mkStartNested()
  gR12Out = gStartNested(v)
proc sutStartNested*(v: int) =
  symexAssume(v == 3)
  runStartNested(v)
  if gR12Out == 9: symexTarget("t")
