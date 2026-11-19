## RFC-0016 INT-31 (W-18). The toolchain this build compiles under, as the
## verdict cache key's `|tc=` segment.
##
## A cached claim is a fact about the native `fn`, which runs the compiler's
## `lib/` routines the walker models by name (`ceilDiv`, the string routines)
## or never reads at all. `|nim=` (`NimVersion`) named the toolchain, but the
## patched toolchain is republished under the same version, so a changed
## `lib/` routine was served the verdicts made under the old one.
##
## `toolchainIdentity` is a content digest: every file under the build's
## `lib/` (`--lib:` honoured) and the compiler binary itself
## (`toolchain_hash.nim` says how it is formed). It is computed at compile
## time by a small native program (the VM is too slow to hash ~15 MB), built
## once into the build's nimcache by the running compiler and run on every
## compile. Only the program is kept between compiles, under a name that is a
## digest of its own source; the digest is recomputed from content each time,
## so no file time or size stands in for it.
##
## When the program cannot be built or run (no C compiler reachable from the
## compile, a sandbox that forbids `staticExec`), the build warns and the
## identity names this compile alone (its date, time, `lib/` and compiler
## paths): its claims are never served to another build, which is sound, and
## served within it, which is what the cache is for.
import std/[os, strutils, compilesettings]
import ./sha256
import ./buildprofile  ## the build's C compiler (`buildProvenance.ccFamily`)

const toolchainIdTag* = "tc1"
  ## The digest's version: a change of what it covers or how the manifest is
  ## written bumps it (and `toolchain_hash.nim`'s own prefix).

proc hostQuote(s: string): string {.compileTime.} =
  ## `s` as one word of a command line on the HOST that runs the compile:
  ## `staticExec` hands the line to `/bin/sh` on POSIX and to `CreateProcess`
  ## on Windows, which both read a double-quoted word. Not `quoteShell`, which
  ## quotes for the TARGET, nor `/`, which joins with the target's separator
  ## (a `--os:windows` cross compile on Linux quoted and joined for Windows).
  ## "" when `s` holds a character a POSIX double-quoted word does not take
  ## literally; the caller then gives up.
  for ch in s:
    if ch in {'"', '$', '`'}: return ""
  '"' & s & '"'

proc ccSwitches(): string {.compileTime.} =
  ## The C compiler of this build, so the helper is built by the same one (a
  ## Windows build that names none falls through to `vcc`).
  let cc = case buildProvenance.ccFamily
           of ccVcc: "vcc"
           of ccClang: "clang"
           of ccGcc: "gcc"
           else: ""
  if cc.len == 0: return ""
  result = " --cc:" & cc
  let p = hostQuote(querySetting(ccompilerPath))
  if p.len > 2: result.add " --" & cc & ".path:" & p

proc toolchainProbe(): tuple[id, why: string] {.compileTime.} =
  const me = currentSourcePath
  const src = me[0 .. max(me.rfind('/'), me.rfind('\\'))] &
    "toolchain_hash.nim"   # not parentDir: it rejoins for the target OS
  const tag = sha256Hex(staticRead("toolchain_hash.nim") & "\0" &
                        staticRead("sha256.nim"))[0 ..< 16]
  let lib = querySetting(libPath)
  let exe = getCurrentCompilerExe()
  let dir = querySetting(nimcacheDir) & "/nelli_tchash_" & tag
  let bin = dir & "/toolchain_hash.exe"
  let words = [hostQuote(bin), hostQuote(lib), hostQuote(exe),
               hostQuote(dir & "/nc"), hostQuote(src)]
  for w in words:
    if w.len == 0:
      return ("", "a path holds a quote, `$` or backquote: " & bin & ", " &
                  lib & ", " & exe & ", " & src)
  let run = words[0] & " " & words[1] & " " & words[2]
  proc valid(o: string; c: int): bool =
    let s = o.strip
    c == 0 and s.len == toolchainIdTag.len + 1 + 64 and
      s.startsWith(toolchainIdTag & ":")
  var (o, c) = gorgeEx(run)
  if not valid(o, c):
    let build = words[2] & " c --skipUserCfg --skipParentCfg " &
      "--skipProjCfg --hints:off --warnings:off --verbosity:0 -d:release" &
      ccSwitches() & " --nimcache:" & words[3] & " -o:" & words[0] & " " &
      words[4]
    let (bo, bc) = gorgeEx(build)
    if bc != 0:
      return ("", "building the toolchain digest program failed (" & build &
                  "): " & bo.strip)
    (o, c) = gorgeEx(run)
    if not valid(o, c):
      return ("", "the toolchain digest program failed (" & run & ", exit " &
                  $c & "): " & o.strip)
  (o.strip, "")

const probe = toolchainProbe()

when probe.id.len > 0:
  const toolchainIdentity* = probe.id
    ## `tc1:` and the digest of the build's `lib/` tree and compiler binary.
else:
  {.warning: "nelli: the verdict cache cannot identify this toolchain, so " &
    "its claims are kept to this build: " & probe.why.}
  const toolchainIdentity* = "unhashed:" & CompileDate & "T" & CompileTime &
    ":" & querySetting(libPath) & ":" & getCurrentCompilerExe()
