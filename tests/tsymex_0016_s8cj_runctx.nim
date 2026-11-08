## RFC-0016 S8cj (PRC-32, CI-03). A run's Z3 context does not outlive the
## run. `resetSymexRunState` makes the walk's context the thread's current
## one (nim-z3's `currentZ3Ctx` threadvar holds a reference); before S8cj
## nothing put the previous one back, so the context lived until the
## thread's next run, or for ever on a thread that exits (a threadvar is
## never destroyed with its thread). A context is 17 MB of Z3 allocation
## before a single term is made, and Z3's process-wide allocation counter
## (`Z3_get_estimated_alloc_size`, the tactic layer's `memory` probe) is an
## input to its default solver's strategy: the QF_NIA portfolio skips its
## `nla2bv` / SAT stage above 100 MB and the preamble's `cofactor_term_ite`
## above 20 MB (`docs/rfc/0016-research/S8cj.md`), so every leaked run
## moved every later query's spend, on every thread, which is what made
## `tsymex_rfc0005_s8by_remainder`'s units check flaky under load (CI-03).
##
## Pinned: after `symexFind` on a thread with no current context, the
## current context is nil again and Z3's allocation counter is back within
## 2 MB of what it was before the run (the context, 17 MB, is gone).
import std/[unittest, dynlib]
import nelli/symex
import z3

proc sut(x, y: int) =
  if x > 1 and y > 1 and x < 2000 and y < 2000 and x * y == 1022117:
    symexTarget("s8cj_runctx")

type AllocSizeFn = proc (): uint64 {.cdecl.}

var allocFound = false

proc allocSize(): uint64 =
  ## `Z3_get_estimated_alloc_size`, looked up in the loaded libz3 (nim-z3's
  ## FFI does not bind it). 0 when it cannot be found (`allocFound` says);
  ## also genuinely 0 before the process's first context.
  const names = when defined(windows): ["libz3.dll", "z3.dll"]
                elif defined(macosx): ["libz3.dylib"]
                else: ["libz3.so", "libz3.so.5", "libz3.so.4", "libz3.so.5.1",
                       "libz3.so.5.1.0.0", "libz3.so.4.13", "libz3.so.4.13.4"]
  for name in names:
    let h = loadLib(name)
    if h != nil:
      let p = symAddr(h, "Z3_get_estimated_alloc_size")
      if p != nil:
        allocFound = true
        return cast[AllocSizeFn](p)()
  0

type Probe = tuple[ctxBefore, ctxAfter: bool, allocBefore, allocAfter: uint64,
                   status: SymexStatusKind]
var probe: Probe

proc runOnThread() {.thread.} =
  {.cast(gcsafe).}:
    probe.ctxBefore = currentContext().isNil
    probe.allocBefore = allocSize()
    let r = symexFind(sut, tLabel("s8cj_runctx"))
    probe.status = r.status
    probe.ctxAfter = currentContext().isNil
    probe.allocAfter = allocSize()

suite "S8cj: a run's context does not outlive the run":

  test "after symexFind on a fresh thread, no current context and the memory is back":
    var th: Thread[void]
    createThread(th, runOnThread)
    joinThread(th)
    checkpoint "status=" & $probe.status & " alloc before=" & $probe.allocBefore &
      " after=" & $probe.allocAfter
    check probe.status == sxSat
    check probe.ctxBefore
    check probe.ctxAfter
    checkpoint(if allocFound: "Z3_get_estimated_alloc_size found"
               else: "Z3_get_estimated_alloc_size not found; memory not checked")
    if allocFound:
      check probe.allocAfter < probe.allocBefore + 2_000_000
