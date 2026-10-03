## RFC-0005 S8ca -- the native stack the walker runs on.
##
## `walk` recurses natively once per inlined call, and one level costs tens
## of kilobytes (measured on the Linux/podman debug build, in
## `tsymex_rfc0005_s8ca_stack`'s header). `maxCallDepth` bounds that depth by
## a count, which cannot know the frame size of the backend (cpp's frames
## are larger than c's) or the size of the thread's stack (8 MB for a Linux
## main thread, 1 MB for a Windows one, 2 MB for a Nim `createThread`). This
## module reads the second directly from the OS, so the walker can decline
## in-band (`walk`'s `isCall` arm) before the stack runs out instead of
## taking the process down with a SIGSEGV.
##
## The bound is read once per thread and cached. On a platform this module
## has no query for, `nativeStackLeft` is `high(int)`: the stack is not
## measured there and `maxCallDepth` alone bounds the walk, as before S8ca.

when defined(windows):
  proc getCurrentThreadStackLimits(low, high: ptr uint) {.
    importc: "GetCurrentThreadStackLimits", stdcall, dynlib: "kernel32".}
elif defined(macosx):
  import std/posix
  proc pthread_get_stackaddr_np(t: Pthread): pointer {.
    importc, header: "<pthread.h>".}
  proc pthread_get_stacksize_np(t: Pthread): csize_t {.
    importc, header: "<pthread.h>".}
elif defined(linux):
  import std/posix
  proc pthread_getattr_np(t: Pthread; attr: ptr Pthread_attr): cint {.
    importc, header: "<pthread.h>".}

var stackLowCache {.threadvar.}: uint
  ## The lowest usable address of this thread's stack (the stack grows
  ## down on every platform this module measures); 0 until first read.
var stackLowRead {.threadvar.}: bool

proc readStackLow(): uint =
  ## The OS's record of this thread's stack, low end. 0 when unknown.
  when defined(windows):
    var lo, hi: uint
    getCurrentThreadStackLimits(addr lo, addr hi)
    lo
  elif defined(macosx):
    let t = pthread_self()
    cast[uint](pthread_get_stackaddr_np(t)) - uint(pthread_get_stacksize_np(t))
  elif defined(linux):
    var attr: Pthread_attr
    if pthread_getattr_np(pthread_self(), addr attr) != 0: return 0
    var base: pointer
    var size: int
    let rc = pthread_attr_getstack(addr attr, base, size)
    discard pthread_attr_destroy(addr attr)
    if rc != 0: 0'u else: cast[uint](base)
  else:
    0'u

proc nativeStackPointer*(): uint {.noinline.} =
  ## An address in the caller's frame region: the stack pointer, to within
  ## this one small frame.
  var marker: int
  result = cast[uint](addr marker)
  # Keep `marker` on the stack: an address taken and returned is enough.

proc nativeStackLeft*(): int =
  ## Bytes of native stack below the current frame on this thread;
  ## `high(int)` where the stack is not measured.
  if not stackLowRead:
    stackLowCache = readStackLow()
    stackLowRead = true
  if stackLowCache == 0'u: return high(int)
  let sp = nativeStackPointer()
  if sp <= stackLowCache: 0 else: int(sp - stackLowCache)
