# Minimal standalone repro — Nim devel (2.3.1), 2.2.10 (latest) & 2.2.8, --mm:arc/orc --panics:on
#
#   nim c -r --mm:arc --panics:on nim_repro_inErrorMode.nim
#   -> Error: unhandled exception: over- or underflow [OverflowDefect]
#
# Correct (the Overrun propagates) on Nim <= 2.2.6, and on any version with
# --panics:off. The dropped check is --panics:on-specific; regressed 2.2.6 -> 2.2.8.
#
# Cause: on the goto-exceptions backend the compiler omits the error-flag
# (`*nimErr_`) propagation check after an indirect *closure* call whose result
# is consumed by another call (`result.add elem(src)`). When the closure raises,
# the loop keeps going instead of unwinding; the next raise then runs
# `inc nimInErrorMode` (lib/system/excpt.nim) on the bool flag while it is still
# `true` from the first raise — and `inc` past `high(bool)` is itself an overflow,
# fatal under --panics:on.

type
  Overrun = object of CatchableError
  Source = object
    data: seq[bool]
    cursor: int
  ElemFn = proc(src: var Source): bool {.closure.}

proc drawBool(src: var Source): bool =
  if src.cursor >= src.data.len:
    raise newException(Overrun, "exhausted")
  result = src.data[src.cursor]
  inc src.cursor

proc listRun(elem: ElemFn, src: var Source): seq[bool] =
  result = @[]
  while true:
    if not src.drawBool(): break
    result.add elem(src)          # closure call; error-flag check omitted after it

let elem: ElemFn = proc(src: var Source): bool = src.drawBool()
var src = Source(data: @[true])
discard listRun(elem, src)
echo "done (no crash)"
