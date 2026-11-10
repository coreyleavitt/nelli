## RFC-0016 W3-z R11. A module-level closure variable holding, when the run
## starts, a closure whose environment captures a `string` or a `seq[int]`:
## the environment's type has a destructor, which the compiler generated and
## which only frees the captured buffers. Each opaque body names the routine
## that builds the closure (on a branch the witness does not take), so the
## route scan and the replay's footprint read it. Shared by the fork-mode suite
## (`tsymex_0016_w3z_r11_closstr`) and the re-executed one
## (`tsymex_0016_prc02_reexec`).
import nelli
import nelli/symex

var gStrOut*: int

# A checked routine, a string captured: the call runs no undefined behaviour.
var gStartStr*: proc (v: int): int
proc mkStartStr*() =
  var s = "abcde"
  gStartStr = proc (v: int): int = v + s.len
proc runStartStr(v: int) {.symexOpaque.} =
  if v == 99: mkStartStr()
  gStrOut = gStartStr(v)
proc sutStartStr*(v: int) =
  symexAssume(v == 3)
  runStartStr(v)
  if gStrOut == 8: symexTarget("t")

# An unchecked routine, a seq[int] captured whose element makes it overflow.
var gStartSeqOvf*: proc (v: int): int
{.push overflowChecks: off.}
proc mkStartSeqOvf*() =
  var xs = @[1, high(int) - 2]
  gStartSeqOvf = proc (v: int): int = v + xs[1]
{.pop.}
proc runStartSeqOvf(v: int) {.symexOpaque.} =
  if v == 99: mkStartSeqOvf()
  gStrOut = gStartSeqOvf(v)
proc sutStartSeqOvf*(v: int) =
  symexAssume(v == 3)
  runStartSeqOvf(v)
  if gStrOut < 0: symexTarget("t")

# The routine appends to the string it captured: the run's own write to the
# environment, which the second call reads ("ab" -> "abx" -> "abxx").
var gStartStrMut*: proc (v: int): int
proc mkStartStrMut*() =
  var s = "ab"
  gStartStrMut = proc (v: int): int =
    s.add 'x'
    v + s.len
proc runStartStrMut(v: int) {.symexOpaque.} =
  if v == 99: mkStartStrMut()
  discard gStartStrMut(v)
  gStrOut = gStartStrMut(v)
proc sutStartStrMut*(v: int) =
  symexAssume(v == 3)
  runStartStrMut(v)
  if gStrOut == 7: symexTarget("t")

# Two captured values, a string among them: a fork copies the environment; a
# re-executed child cannot be handed it (the order of an environment's
# fields is the compiler's), and the decline says so.
var gStartTwo*: proc (v: int): int
proc mkStartTwo*() =
  var s = "abc"
  var k = 2
  gStartTwo = proc (v: int): int = v + s.len + k
proc runStartTwo(v: int) {.symexOpaque.} =
  if v == 99: mkStartTwo()
  gStrOut = gStartTwo(v)
proc sutStartTwo*(v: int) =
  symexAssume(v == 3)
  runStartTwo(v)
  if gStrOut == 8: symexTarget("t")
