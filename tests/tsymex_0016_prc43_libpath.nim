## RFC-0016 PRC-43 -- a build that overrides `--lib:` keeps the walker's
## stdlib models. Stdlib identity was matched by the `/lib/` path spelling
## (`check_options.isSystemFile`/`isStdlibFile`, `check_scan.isLibraryFile`,
## `replay_footprint.isRuntimeFile`, `dsl_parser.isStdMathProc`), so a lib
## directory not named `lib` turned `math.ceilDiv` (modelled exactly) into
## `feCheckOption` and a walked body. Each now also asks whether the file is
## under the configured lib path, as `isStdlibDecl` does.
import std/[unittest, os, osproc, strutils, compilesettings]
import nelli/smt/canonicalize
from ./probe_build import childBuildArgs

const
  libDir = querySetting(libPath)
  child = currentSourcePath.parentDir / "prc43_lib_child.nim"

proc verdict(tmp, name: string; extra: string): seq[string] =
  let exe = tmp / name & ExeExt
  let cmd = quoteShell(getCurrentCompilerExe()) &
    " c --threads:on --hints:off " &
    quoteShellCommand(childBuildArgs()) & " " & getEnv("NELLI_NIM_FLAGS") & " " & extra &
    " --nimcache:" & quoteShell(tmp / ("nc_" & name)) &
    " -o:" & quoteShell(exe) & " " & quoteShell(child)
  let (output, code) = execCmdEx(cmd)
  checkpoint output
  doAssert code == 0, "the child build " & name & " failed"
  let (o2, c2) = execCmdEx(quoteShell(exe))
  checkpoint o2
  doAssert c2 == 0, exe & " exited " & $c2
  for line in o2.splitLines:
    if line.startsWith("VERDICT ") or line.startsWith("ERR "): result.add line

suite "PRC-43":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 414

  test "ceilDiv is exact under a --lib: copy not named lib":
    let tmp = getTempDir() / ("nelli_prc43_" & $getCurrentProcessId())
    removeDir(tmp)
    createDir(tmp)
    copyDir(libDir, tmp / "stdlib2")
    let base = verdict(tmp, "childBase", "")
    checkpoint "default: " & $base
    check base.len > 0 and base[0].startsWith("VERDICT status=sxSat trusted=true")
    let moved = verdict(tmp, "childLib",
                        "--lib:" & quoteShell(tmp / "stdlib2"))
    checkpoint "--lib: " & $moved
    # the same verdict and the same errors as the default build (RED was
    # `sxUnknown`: `feCheckOption`, `feOverflowCheckOption`, then
    # `feUnsupportedStmtKind` from `ceilDiv`'s walked body)
    check moved == base
    removeDir(tmp)
