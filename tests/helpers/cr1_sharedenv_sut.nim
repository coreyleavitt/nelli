## RFC-0016 0.10.0 review H1. Module-level closure variables that hold, when
## the run starts, closures sharing ONE captured environment: one closure
## writes the captured value and another reads it, so the run's answer depends
## on the two being one environment. A replay that hands the child two copies
## runs a program the host does not. Shared by the forked suite
## (`tsymex_0016_cr1_sharedenv`) and the re-executed one
## (`tsymex_0016_cr1_sharedenv_reexec`).
##
## Each opaque body names the routine that builds the closures (on a branch the
## witness does not take), so their nested routines are code the replay's
## footprint reads. Natively every SUT computes `gShOut == 1` from a fresh
## `mk*`, so its target is unreachable.
import nelli
import nelli/symex

var gShOut*: int

# An int captured by two closures (the plain-bytes path, W3-z R10).
var gShIncr*: proc () {.closure.}
var gShGet*: proc (): int {.closure.}
proc mkShared*() =
  var n = 0
  gShIncr = proc () = inc n
  gShGet = proc (): int = n
proc runShared*(v: int) {.symexOpaque.} =
  if v == 99: mkShared()
  gShIncr()
  gShOut = gShGet()
proc sutShared*(v: int) =
  symexAssume(v == 3)
  runShared(v)
  if gShOut == 0: symexTarget("t")

# A string captured by two closures (the codec path, W3-z R11).
var gShAdd*: proc () {.closure.}
var gShLen*: proc (): int {.closure.}
proc mkSharedStr*() =
  var s = ""
  gShAdd = proc () = s.add 'x'
  gShLen = proc (): int = s.len
proc runSharedStr*(v: int) {.symexOpaque.} =
  if v == 99: mkSharedStr()
  gShAdd()
  gShOut = gShLen()
proc sutSharedStr*(v: int) =
  symexAssume(v == 3)
  runSharedStr(v)
  if gShOut == 0: symexTarget("t")

# One environment reached from a closure variable and from a ref's field.
type ShBox* = ref object
  get*: proc (): int {.closure.}
var gShBump*: proc () {.closure.}
var gShBox*: ShBox
proc mkSharedBox*() =
  var n = 0
  gShBump = proc () = inc n
  gShBox = ShBox(get: proc (): int = n)
proc runSharedBox*(v: int) {.symexOpaque.} =
  if v == 99: mkSharedBox()
  gShBump()
  gShOut = gShBox.get()
proc sutSharedBox*(v: int) =
  symexAssume(v == 3)
  runSharedBox(v)
  if gShOut == 0: symexTarget("t")
