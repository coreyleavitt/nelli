## RFC-0005 S8bj. Which engine std/re's libpcre runs an unanchored call on.
##
## `std/re`'s `re()` studies every pattern with PCRE_STUDY_JIT_COMPILE when
## the linked libpcre reports `PCRE_CONFIG_JIT` (Windows builds and most
## Linux distributions' do), and `pcre_exec` then runs the JIT for every
## call without PCRE_ANCHORED. The JIT's start-of-match scan and its match
## limit differ from the interpreter's (`pcre_select.jitDeclined`), which
## is the semantics the walker models. So the walker asks, at walk time,
## the library std/re would load: the same names as Nim's `pcre` wrapper,
## `pcre_config(PCRE_CONFIG_JIT)`. A library it cannot load or ask counts as
## a JIT one (the declines then stand: sound).
import std/[dynlib, strutils]

const pcreConfigJit = 9'i32   ## pcre.h's PCRE_CONFIG_JIT

when defined(windows):
  when defined(nimOldDlls):
    const pcreLib = "pcre.dll"
  elif defined(cpu64):
    const pcreLib = "pcre64.dll"
  else:
    const pcreLib = "pcre32.dll"
elif defined(macosx):
  const pcreLib = "libpcre(.3|.1|).dylib"
else:
  const pcreLib = "libpcre.so(.3|.1|)"

type PcreConfig = proc (what: int32; where: pointer): int32 {.cdecl, gcsafe.}

var engineKnown {.threadvar.}: bool
var engineJit {.threadvar.}: bool

proc probeJit(): bool =
  let h = loadLibPattern(pcreLib)
  if h == nil: return true
  let f = cast[PcreConfig](symAddr(h, "pcre_config"))
  if f == nil: return true
  var v: int32 = 0
  if f(pcreConfigJit, addr v) != 0: return true
  v != 0

proc pcreRunsJit*(): bool =
  ## RFC-0005 S8bj. Whether std/re's unanchored calls run on PCRE's JIT
  ## (true when the library cannot be asked). Cached per thread.
  if not engineKnown:
    engineJit = probeJit()
    engineKnown = true
  engineJit

type PcreVersion = proc (): cstring {.cdecl, gcsafe.}

var versionKnown {.threadvar.}: bool
var versionStr {.threadvar.}: string

proc pcreVersion*(): string =
  ## RFC-0005 S8bj. std/re's libpcre's `pcre_version()` ("8.45 2021-06-15"),
  ## "" when it cannot be asked. Cached per thread.
  if not versionKnown:
    versionKnown = true
    let h = loadLibPattern(pcreLib)
    if h != nil:
      let f = cast[PcreVersion](symAddr(h, "pcre_version"))
      if f != nil: versionStr = $f()
  versionStr

proc pcreBefore838*(): bool =
  ## RFC-0005 S8bj. Whether std/re's libpcre is older than 8.38 (true when
  ## it cannot be asked). PCRE 8.37 (the Windows legs') drops the caseless
  ## flag of a required character after a `{0}` item: `x{0}(?i)a` does not
  ## match "A" there, and does in 8.45 (probed).
  let v = pcreVersion()
  var major, minor = 0
  var i = 0
  while i < v.len and v[i] in {'0'..'9'}:
    major = major * 10 + ord(v[i]) - ord('0')
    inc i
  if i >= v.len or v[i] != '.': return true
  inc i
  while i < v.len and v[i] in {'0'..'9'}:
    minor = minor * 10 + ord(v[i]) - ord('0')
    inc i
  major < 8 or (major == 8 and minor < 38)

proc pcreEngineName*(): string =
  ## The engine as the symex cache key records it (with the version).
  (if pcreRunsJit(): "pcre-jit-" else: "pcre-interp-") &
    pcreVersion().split(' ')[0]
