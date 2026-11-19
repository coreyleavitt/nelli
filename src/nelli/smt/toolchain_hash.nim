## RFC-0016 INT-31 (W-18). A standalone program, never imported:
## `toolchain_id.nim` builds it and runs it at compile time to digest the
## toolchain the build compiles under.
##
## Usage: `toolchain_hash <lib dir> <compiler binary>`. Prints `tc1:` and the
## SHA-256 of a manifest listing, in byte order of their paths relative to
## `<lib dir>` (with `/` separators), every file under it and the SHA-256 of
## its content, then the SHA-256 of the compiler binary. Any change to a file
## under `lib/`, a file added or removed, or a different compiler moves it.
## Exits non-zero, printing nothing on stdout, when a file cannot be read.
import std/[os, algorithm, strutils]
import ./sha256

proc main(): int =
  let args = commandLineParams()
  if args.len != 2: return 2
  let lib = args[0]
  let exe = args[1]
  if not dirExists(lib) or not fileExists(exe): return 3
  var files: seq[string]
  for f in walkDirRec(lib, yieldFilter = {pcFile, pcLinkToFile},
                      relative = true):
    files.add f.replace('\\', '/')
  if files.len == 0: return 4
  files.sort(system.cmp[string])
  var manifest = "tc1\n"
  try:
    for f in files:
      manifest.add f & "\0" & sha256Hex(readFile(lib / f)) & "\n"
    manifest.add "\0compiler\0" & sha256Hex(readFile(exe)) & "\n"
  except IOError, OSError:
    return 5
  stdout.write "tc1:" & sha256Hex(manifest) & "\n"
  0

when isMainModule:
  quit main()
