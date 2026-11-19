## RFC-0016 INT-31 (W-18), the `lib/` hole: the verdict cache never serves a
## claim made under one toolchain `lib/` to a build against another.
##
## The key covered the standard library only through `|nim=` (`NimVersion`),
## and the patched toolchain is republished under the same version, so a
## changed `lib/` routine behind a modelled call served the old verdict. The
## suite copies the toolchain twice (its compiler, `lib/` and `config/`, so each
## copy's compiler finds its own `lib/` as a republished toolchain does),
## changes `math.ceilDiv` in the second copy's `lib/` (the walker models
## `ceilDiv` by name and never reads its body, so the program it parses is the
## same), and builds `int31_lib_child.nim` with each copy's compiler. The
## first build's run fills a database directory; the second build's run
## against it may not be served a witness that misses the label natively in
## the second build. (A `--lib:` override is not used: the walker's stdlib
## recognition degrades `ceilDiv` under it, so no claim is made to go stale.)
##
## RED before the fix: the second build was served the first one's witness
## (`x = 41`) from the cache, and `ceilDiv(41'u8, 1'u8)` is 0 in the second
## `lib/`.
import std/[unittest, os, osproc, strutils, compilesettings]
import nelli/smt/admission
import nelli/smt/canonicalize
import nelli/smt/toolchain_id
import nelli/smt/types
from ./s8cu_helpers import pinNever

const
  cell = cellKey(axConstruct, "cache/key/toolchain")
  nimRoot = getCurrentCompilerExe().parentDir.parentDir
  libDir = querySetting(libPath)
  child = currentSourcePath.parentDir / "int31_lib_child.nim"
  marker = "func ceilDiv*[T: SomeInteger](x, y: T): T"
  patchAt = "  when sizeof(T) == 8:"

proc patchCeilDiv(lib: string) =
  ## `ceilDiv(41, y)` returns 0 in this `lib/`.
  let path = lib / "pure" / "math.nim"
  var src = readFile(path)
  let m = src.find(marker)
  doAssert m >= 0, "no ceilDiv in " & path
  let at = src.find(patchAt, m)
  doAssert at >= 0, "no ceilDiv body in " & path
  src.insert("  if x == T(41): return T(0)\n", at)
  writeFile(path, src)

proc copyToolchain(dest: string) =
  ## The toolchain's compiler, `lib/` and `config/` under `dest`.
  createDir(dest / "bin")
  copyFileWithPermissions(getCurrentCompilerExe(),
                          dest / "bin" / "nim" & ExeExt)
  if dirExists(nimRoot / "config"): copyDir(nimRoot / "config", dest / "config")
  copyDir(libDir, dest / "lib")

proc build(tmp, name, root: string): string =
  result = tmp / name & ExeExt
  let cmd = quoteShell(root / "bin" / "nim" & ExeExt) &
    " c --threads:on --hints:off " & getEnv("NELLI_NIM_FLAGS") &
    " --nimcache:" & quoteShell(tmp / ("nc_" & name)) &
    " -o:" & quoteShell(result) & " " & quoteShell(child)
  let (output, code) = execCmdEx(cmd)
  checkpoint output
  doAssert code == 0, "the child build under " & root & " failed"

proc run(exe, db: string): seq[string] =
  let (output, code) = execCmdEx(quoteShell(exe) & " " & quoteShell(db))
  checkpoint output
  doAssert code == 0, exe & " exited " & $code
  for line in output.splitLines:
    if line.startsWith("FINDING "): result.add line

suite "INT-31: a claim made under one lib/ is not served under another":

  test "this build's toolchain is identified by content, and keyed":
    check toolchainIdentity.startsWith(toolchainIdTag & ":")
    let prog = SymexProgram(body: IRStmt(kind: isBlock))
    check symexCacheKey(prog, tLabel("t"), SymexSettings(), "z", "n", "w", "r",
                        toolchain = "tc1:a") !=
          symexCacheKey(prog, tLabel("t"), SymexSettings(), "z", "n", "w", "r",
                        toolchain = "tc1:b")

  test "a changed ceilDiv in a copied lib/ gets no cached witness":
    let tmp = getTempDir() / ("nelli_int31_lib_" & $getCurrentProcessId())
    removeDir(tmp)
    createDir(tmp)
    copyToolchain(tmp / "nimA")
    copyToolchain(tmp / "nimB")
    patchCeilDiv(tmp / "nimB" / "lib")
    let a = build(tmp, "childA", tmp / "nimA")
    let b = build(tmp, "childB", tmp / "nimB")
    let db = tmp / "db"
    let first = run(a, db)
    checkpoint "first: " & $first
    var cold = false
    for l in first:
      if "status=sfSat" in l and "fromCache=false" in l and "hits=true" in l:
        cold = true
    check cold
    let second = run(b, db)
    checkpoint "second: " & $second
    var stale = false
    for l in second:
      if "status=sfSat" in l and "fromCache=true" in l and "hits=false" in l:
        stale = true
    check second.len > 0
    check not stale
    pinNever(cell, not stale, "a cached claim served across a changed lib/")
    removeDir(tmp)

suite "INT-31/INT-33: the walker version floor":
  test "the toolchain segment and the flip's roots moved every key: 407":
    check parseInt(symexWalkerVersion) >= 407
