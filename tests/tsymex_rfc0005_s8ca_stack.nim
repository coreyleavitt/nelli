## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 1:
## the walker overflowed the native stack before `maxCallDepth` declined.
##
## `walk` recurses natively once per inlined call. `maxCallDepth` bounds
## that by a count, but what one level costs depends on the backend and
## what the stack holds depends on the thread: `tsymex_configdefaults`'
## round-2 crash pin (`maxCallDepth: 50`, a linear recursion with `n` free)
## was sized by a probe on the c backend (safe through 85 levels on an 8 MB
## stack), and on cpp the same 50 levels ran off the 8 MB stack (SIGSEGV,
## rc=139, the whole test binary). A Windows main thread has 1 MB unless
## the link raises it; a Nim `createThread` thread has 2 MB everywhere.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (1) a call is not inlined when the stack left below it is under the
##       reserve the walk needs (`nativeStackShort`): the call declines
##       in-band, `beBudgetExhaustedUnmodelled` naming the native stack, at
##       any `maxCallDepth`;
##   (2) on a 2 MB thread, the default budget and an explicit deep one both
##       decline in-band; with about 1 MB left (a Windows main thread's
##       whole stack) a shallow call is still inlined and decides;
##   (3) a decline the stack forced is the machine's, not the program's,
##       and is not cached (`symexNativeStackCut`).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/nativestack

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc stackNamed(errs: seq[SymexErrorInfo]): bool =
  for e in errs:
    if e.kind == beBudgetExhaustedUnmodelled and "native stack" in e.msg:
      return true

# The crash pin's SUT (`tsymex_configdefaults`): linear recursion, `n` free.
proc s8caRunaway(n: int): int =
  if n > 0:
    result = s8caRunaway(n - 1) + 1
  else:
    result = 0

proc s8caRunawaySut(n: int) =
  if s8caRunaway(n) > 1_000_000:
    symexTarget("s8ca_runaway_never")

proc s8caHelper(x: int): int = x + 1

proc s8caShallow(x: int) =
  if s8caHelper(x) == 8:
    symexTarget("s8ca_shallow")

const deep = SymexSettings(budget: ResourceBudget(maxCallDepth: 100_000,
                                                  maxRecursionDepth: 100_000))

suite "S8ca (1): the walk declines before the native stack runs out":

  test "the stack this thread has is measured":
    let left = nativeStackLeft()
    check left > 0
    check left < high(int)

  test "maxCallDepth past what the stack holds declines in-band, named":
    let r = symexFind(s8caRunawaySut, tLabel("s8ca_runaway_never"), deep)
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check stackNamed(r.errors)
    check symexNativeStackCut()

  test "the crash pin's budget (maxCallDepth: 50) declines cleanly":
    let r = symexFind(s8caRunawaySut, tLabel("s8ca_runaway_never"),
        SymexSettings(budget: ResourceBudget(maxCallDepth: 50)))
    checkpoint show(r.errors)
    check r.status == sxUnknown

  test "a run the stack does not cut is not flagged":
    let r = symexFind(s8caRunawaySut, tLabel("s8ca_runaway_never"))
    check r.status == sxUnknown
    check not symexNativeStackCut()

# (2) A 2 MB stack: a Nim thread's on every platform, twice a Windows main
# thread's.
type ThreadOut = object
  status: SymexStatusKind
  named: bool
  cut: bool
  left: int

var outs: array[4, ThreadOut]

proc analyse(which: int) =
  let r =
    case which
    of 0, 2: symexFind(s8caRunawaySut, tLabel("s8ca_runaway_never"))
    of 1: symexFind(s8caRunawaySut, tLabel("s8ca_runaway_never"), deep)
    else: symexFind(s8caShallow, tLabel("s8ca_shallow"))
  outs[which] = ThreadOut(status: r.status, named: stackNamed(r.errors),
                          cut: symexNativeStackCut(),
                          left: nativeStackLeft())

proc underFiller(which: int) {.noinline.} =
  ## About 1 MB of this 2 MB thread's stack held by this frame: the walk
  ## below it has what a 1 MB Windows main thread has, less its own start.
  var filler: array[1024 * 1024, byte]
  filler[0] = 1
  analyse(which)
  outs[which].left = outs[which].left + int(filler[0]) - 1

proc onThread(which: int) {.thread.} =
  {.cast(gcsafe).}:
    if which >= 2: underFiller(which) else: analyse(which)

suite "S8ca (2): a 2 MB thread":

  test "the default budget declines in-band":
    var t: Thread[int]
    createThread(t, onThread, 0)
    joinThread(t)
    check outs[0].left > 0
    check outs[0].left < 2 * 1024 * 1024
    check outs[0].status == sxUnknown

  test "an explicit deep budget declines in-band, named":
    var t: Thread[int]
    createThread(t, onThread, 1)
    joinThread(t)
    check outs[1].status == sxUnknown
    check outs[1].named
    check outs[1].cut

  test "with about 1 MB left, the default budget declines in-band":
    var t: Thread[int]
    createThread(t, onThread, 2)
    joinThread(t)
    check outs[2].left < 1024 * 1024
    check outs[2].status == sxUnknown

  test "with about 1 MB left, a shallow call is still inlined and decides":
    var t: Thread[int]
    createThread(t, onThread, 3)
    joinThread(t)
    check outs[3].status == sxSat
    check not outs[3].cut

suite "S8ca: walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
