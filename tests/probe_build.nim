## The child-build half of `s8cu_helpers`: building a probe in a child `nim`
## with the host's build-relevant flags (`prepareProbe`), and running it under a
## bounded main stack. It imports no part of the engine, so a suite that only
## builds and inspects a probe (`tsymex_0016_d1vcc_frame`) does not compile the
## engine twice, once for itself and once for the child. `s8cu_helpers`
## re-exports all of it.
##
## Its platform arms (`defined(windows)`, `defined(vcc)`) pick the child's
## flags and how its stack is bounded; none of them leaves a check unrun. They
## sat in `s8cu_helpers` before this split, where the K2a census counts a
## platform arm as recordable because the file defines `skipCell`. A suite
## that cannot build or run a probe on a platform records that with
## `skipCell` (`s8cu_helpers`).
import std/[compilesettings, os, osproc, streams, strutils, tempfiles]
import nelli/smt/buildprofile

type
  PinFailure* = object of CatchableError
    ## A pin's claim did not hold. A unittest test fails on it uncaught; a test
    ## that expects a failure catches it with `expect PinFailure`.

proc probeFail(msg: string) {.noreturn.} =
  raise newException(PinFailure, msg)

var probeCounter {.threadvar.}: int
const hostSearchPaths = querySettingSeq(searchPaths)  ## the host build's `--path`s
const hostCIncludes = querySettingSeq(cincludes)
  ## the host build's `--cincludes`: where it found `z3.h`. CI passes the Z3
  ## prefix's include dir on the command line (Linux artifact, mingw, MSVC),
  ## so a child that does not carry it dies on `fatal error: z3.h`.

const winProbePrologue = when defined(windows): """
# A first-chance vectored handler: a divide trap, integer overflow trap or
# access violation ends the process at once with the exception code. Without
# it the mingw CRT can resume the faulting instruction forever (no SIGFPE
# mapping for 0xC0000095), and the probe hangs instead of dying.
proc nelliAddVeh(first: culong; h: pointer): pointer
  {.importc: "AddVectoredExceptionHandler", stdcall, dynlib: "kernel32".}
proc nelliExitProcess(code: cuint) {.importc: "ExitProcess", stdcall,
                                      dynlib: "kernel32".}
proc nelliVeh(p: pointer): int32 {.stdcall.} =
  let code = cast[ptr ptr uint32](p)[][]
  if code == 0xC0000094'u32 or code == 0xC0000095'u32 or
     code == 0xC0000005'u32:
    nelliExitProcess(cuint(code))
  0'i32
discard nelliAddVeh(1, cast[pointer](nelliVeh))
""" else: ""

proc childBuildArgs*(): seq[string] =
  ## What any child `nim` this suite starts needs to compile against the host
  ## build's sources and C compiler: the repo's `src` and every search path
  ## THIS test was compiled with (the dependencies', wherever the host build got
  ## them from, CI's command-line `--path`s included), absolute so the child's
  ## cwd does not matter; the host's `--cincludes`; and its C compiler (the
  ## toolchain ships Nim alone, so on Windows the child would otherwise fall
  ## through to `vcc`). A search path inside the host's `lib/` is left to the
  ## child's own configuration, which adds its own `lib/`'s: a child built
  ## against another `lib/` must not search the host's.
  let lib = absolutePath(querySetting(libPath)).replace('\\', '/')
  var paths = @[currentSourcePath().parentDir.parentDir / "src"]
  for q in hostSearchPaths:
    let a = absolutePath(q)
    let norm = a.replace('\\', '/')
    if norm == lib or norm.startsWith(lib & "/"): continue
    if a notin paths: paths.add a
  for q in paths: result.add "--path:" & q
  for q in hostCIncludes: result.add "--cincludes:" & absolutePath(q)
  when defined(vcc): result.add "--cc:vcc"
  elif defined(windows): result.add "--cc:gcc"   # the toolchain ships Nim alone

type ProbeBuild* = object
  dir*, exe*, backend*: string
  args*: seq[string]
  cmd*: string

proc prepareProbe*(who: string; probe: string; flags: openArray[string]
                 ): ProbeBuild =
  ## The child build shared by `pinCrash` and `pinRefused`: the host's
  ## build-relevant defines plus `flags`; `probe` is a path or, with a newline,
  ## the source text itself.
  let nim = findExe("nim")
  if nim.len == 0: probeFail(who & ": nim is not on PATH")
  inc probeCounter
  result.dir = createTempDir("k9a_probe_", "_" & $probeCounter)
  var src = probe
  if '\n' in probe or defined(windows):
    src = result.dir / "probe_src.nim"
    let body = if '\n' in probe: probe else: readFile(absolutePath(probe))
    writeFile(src, winProbePrologue & body)
  else:
    src = absolutePath(probe)
  result.exe = result.dir / ("probe" & ExeExt)
  # The child compiles `probe_src.nim` in a temp dir, so it finds no `nim.cfg`
  # and nothing resolves `import nelli` but what `childBuildArgs` gives it.
  result.args = @["--hints:off", "--warnings:off", "--threads:on",
               "--nimcache:" & (result.dir / "cache"), "--out:" & result.exe,
               "--panics:" & (when defined(nimPanics): "on" else: "off"),
               "--mm:" & $buildSemantics.mm] & childBuildArgs()
  when defined(nelliFwrapv): result.args.add "-d:nelliFwrapv"
  when defined(release): result.args.add "-d:release"
  when defined(danger): result.args.add "-d:danger"
  for f in flags: result.args.add f
  result.backend = when defined(cpp): "cpp" else: "c"
  result.cmd = quoteShellCommand(@[nim, result.backend] & result.args & @[src])

# ---- a probe run under a bounded main stack ---------------------------------
# One bound, two mechanisms: POSIX caps the stack at run time (`ulimit -s`, from
# `sh` as a real argv), Windows has no such limit (a PE thread's reserve is
# fixed at link time, 1 MB by default) so the probe is LINKED with the reserve.
# The builders are pure so a test can assert every OS x compiler combination
# on a host that has only one of them.

proc stackBoundKb*(windows, vcc, cpp: bool; gccCKb, gccCppKb, sites, siteCapKb:
                   int): int =
  ## The bound, in KB. gcc (any OS) is the caller's measured `gccCKb` /
  ## `gccCppKb`. MSVC debug frames are about 5.3x gcc's, so its bound is
  ## re-derived from the same model: a site may cost `siteCapKb` / the 91
  ## sites k4a overran with (11.25 KB at MSVC, the 1 MB reserve spread over
  ## them), so `sites` of them cost sites * siteCapKb / 91 on top of the
  ## runtime base (gcc's bound less its own 34 KB of sites, kept for MSVC), and
  ## the result rounds down to 16. The C++ offset (+32) is carried over as is.
  discard windows
  let gcc = if cpp: gccCppKb else: gccCKb
  if not vcc: return gcc
  let base = gccCKb - 32            # 160 - 32 = 128: the runtime's own need
  let msvc = base + sites * siteCapKb div 91
  (msvc + (if cpp: gccCppKb - gccCKb else: 0)) div 16 * 16

proc stackLinkFlags*(windows, vcc: bool; kb: int): seq[string] =
  ## Flags for the probe's build. POSIX bounds the run, not the link. mingw
  ## ld takes `--stack,<reserve>`; MSVC's driver takes `/F<bytes>` (cl's own
  ## stack-size option), placed in `--passL` ahead of any `/link` the vcc
  ## config appends for release builds, so it never meets a second `/link`.
  if not windows: return @[]
  let bytes = kb * 1024
  if vcc: @["--passL:/F" & $bytes] else: @["--passL:-Wl,--stack," & $bytes]

proc stackRunCommand*(windows: bool; exe: string; kb: int
                     ): tuple[exe: string, args: seq[string]] =
  ## What to execute. POSIX: `sh -c 'ulimit -s N && exec "$0"' <exe>`, the
  ## probe path a separate argument so it needs no quoting. Windows: the probe
  ## itself, its reserve already linked in.
  if windows: (exe, @[])
  else: ("sh", @["-c", "ulimit -s " & $kb & " && exec \"$0\"", exe])

proc runBoundedStack*(exe: string; kb: int): tuple[output: string, rc: int] =
  ## Run `exe` under the bound of `stackLinkFlags`/`stackRunCommand`.
  let c = stackRunCommand(defined(windows), exe, kb)
  let p = startProcess(c.exe, getCurrentDir(), c.args,
                       options = {poStdErrToStdOut, poUsePath})
  result.output = p.outputStream.readAll()
  result.rc = p.waitForExit()
  p.close()

proc hostStackBoundKb*(cpp: bool; gccCKb, gccCppKb, sites, siteCapKb: int): int =
  stackBoundKb(defined(windows), defined(vcc), cpp, gccCKb, gccCppKb, sites,
               siteCapKb)

proc hostStackLinkFlags*(kb: int): seq[string] =
  stackLinkFlags(defined(windows), defined(vcc), kb)
