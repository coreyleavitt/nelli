## RFC-0016 W3-z R10. A module-level closure variable holding, when the run
## starts, a closure WITH a captured environment. Each opaque body names the
## routine that builds the closure (on a branch the witness does not take), so
## the closure's nested routine is code the replay's footprint reads. Shared by
## the fork-mode suite (`tsymex_0016_w3z_r10_closenv`) and the re-executed one
## (`tsymex_0016_prc02_reexec`).
import nelli
import nelli/symex

var gEnvOut*: int

# A checked routine, an int captured: the call runs no undefined behaviour.
var gStartEnv*: proc (v: int): int
proc mkStartEnv*() =
  var n = 5
  gStartEnv = proc (v: int): int = v + n
proc runStartEnv(v: int) {.symexOpaque.} =
  if v == 99: mkStartEnv()
  gEnvOut = gStartEnv(v)
proc sutStartEnv*(v: int) =
  symexAssume(v == 3)
  runStartEnv(v)
  if gEnvOut == 8: symexTarget("t")

# An unchecked routine, an int captured that makes it overflow.
var gStartEnvOvf*: proc (v: int): int
{.push overflowChecks: off.}
proc mkStartOvf*() =
  var n = high(int) - 2
  gStartEnvOvf = proc (v: int): int = v + n
{.pop.}
proc runStartOvf(v: int) {.symexOpaque.} =
  if v == 99: mkStartOvf()
  gEnvOut = gStartEnvOvf(v)
proc sutStartOvf*(v: int) =
  symexAssume(v == 3)
  runStartOvf(v)
  if gEnvOut < 0: symexTarget("t")

# A captured `ptr`: the environment runs no destructor, but its bytes hold an
# address, which another process cannot be handed and the settle does not read.
var gStartEnvPtr*: proc (v: int): int
proc mkStartPtr*() =
  var p: ptr int = nil
  gStartEnvPtr = proc (v: int): int = (if p == nil: v + 5 else: v)
proc runStartPtr(v: int) {.symexOpaque.} =
  if v == 99: mkStartPtr()
  gEnvOut = gStartEnvPtr(v)
proc sutStartPtr*(v: int) =
  symexAssume(v == 3)
  runStartPtr(v)
  if gEnvOut == 8: symexTarget("t")
