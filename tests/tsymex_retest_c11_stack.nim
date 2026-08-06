## Chapulin 0.1.0 re-test triage — catalog #11 (depth-3 nested-if string
## helper + later string op → native crash), walker v64. Root cause was a
## Windows STACK OVERFLOW: the walker's recursive lowering + Z3's recursive
## rewriters overran the 1 MB (MSVC) / 2 MB (MinGW) default main-thread
## stack — empirically a BARE SILENT EXIT (code 255 in the toolchain
## container; 0xC00000FD never surfaces through the CRT), which is why the
## re-test could only report "bare non-zero exit". The identical shapes
## prove sxUnsat under a 16 MB stack — and the depth-2 STATEMENT-form twin
## below crashed too at 1 MB, so the cliff was never really "depth 3": it
## is stack size. Never reproducible on Linux (8 MB default) — the RFC's
## "healed, depth 1-6 clean" note was a Linux-only artifact.
##
## v64 fix: on Windows, `runSymex` executes the whole solve on a FIBER with
## an explicitly reserved 16 MB stack (`runSymexWithBigStack`, runtime.nim;
## `-d:symexNoBigStack` opts out). These tests are the Windows regression
## pins; on Linux they always passed and simply keep passing.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

proc stripDepth2(s: string): string =
  result = s
  if s.len >= 1 and (s[0] == '/' or s[0] == '\\'):
    if s.len >= 2 and (s[1] == '/' or s[1] == '\\'):
      result = s[2 .. ^1]
    else:
      result = s[1 .. ^1]

proc depth2Caller(filename: string) =
  var cleanName = stripDepth2(filename)
  cleanName = cleanName.replace("\\", "/")
  if cleanName.contains(".."):
    return

proc stripDepth3(s: string): string =
  result = s
  if s.len >= 1 and (s[0] == '/' or s[0] == '\\'):
    if s.len >= 2 and (s[1] == '/' or s[1] == '\\'):
      if s.len >= 3 and (s[2] == '/' or s[2] == '\\'):
        result = s[3 .. ^1]
      else:
        result = s[2 .. ^1]
    else:
      result = s[1 .. ^1]

proc depth3Caller(filename: string) =
  var cleanName = stripDepth3(filename)
  cleanName = cleanName.replace("\\", "/")
  if cleanName.contains(".."):
    return

suite "symex re-test C11 — nested-if string helper depth cliff (stack)":

  test "depth-2 statement-form strip + replace/contains proves sxUnsat (crashed at 1 MB stack)":
    let r = symexFind(depth2Caller, tIndexError())
    check r.status == sxUnsat

  test "depth-3 strip + replace/contains proves sxUnsat (the catalog-#11 shape)":
    let r = symexFind(depth3Caller, tIndexError())
    check r.status == sxUnsat

suite "symex re-test C11 — walker version pin":

  test "walker version floor >= 64 (big-stack fiber execution on Windows)":
    check parseInt(symexWalkerVersion) >= 64
