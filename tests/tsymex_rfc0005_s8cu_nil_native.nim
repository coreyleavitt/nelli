## RFC-0005 S8cu -- what a nil dereference does natively, on the host that runs this.
##
## `crashRaise` models a nil read as a crash no `except` catches and no `finally`
## survives, in every build but `--exceptions:setjmp`, where it declines under a
## `try` (`tsymex_rfc0005_s8cu_nil_setjmp`). This suite checks the premise on the
## platform it runs on, Windows included: it compiles `s8cu_nil_probe.nim` (a nil
## read under `except NilAccessDefect` and a `finally`) in each mode, runs it,
## and prints what happened (`NATIVE ...` lines). Without setjmp, nothing may
## catch it and the `finally` may not run; with setjmp, either is allowed, since
## the walker declines there. Default goto exceptions without `std/segfaults` are
## `tsymex_rfc0005_s8cu_nil`'s native rows.
import std/[unittest, os, osproc, strutils, streams]

type Outcome = object
  rc: int
  caught, finallyRan, returned, timedOut: bool
  output: string

proc probe(tag: string; flags: seq[string]): Outcome =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim is not on PATH"
  let dir = getTempDir() / ("s8cu_nil_native_" & $getCurrentProcessId())
  createDir(dir)
  let exe = dir / (tag & ExeExt)
  var args = @["c", "--hints:off", "--warnings:off", "--threads:on",
               "--nimcache:" & (dir / ("cache_" & tag)), "--out:" & exe]
  when defined(windows): args.add "--cc:gcc"   # the toolchain ships Nim alone
  args.add flags
  args.add currentSourcePath().parentDir / "s8cu_nil_probe.nim"
  let (cout, crc) = execCmdEx(quoteShellCommand(@[nim] & args))
  doAssert crc == 0, "probe build failed (" & tag & "):\n" & cout
  let p = startProcess(exe, options = {poStdErrToStdOut})
  let rc = p.waitForExit(20_000)
  result.output = p.outputStream.readAll()
  if p.running:
    p.kill()
    result.timedOut = true
  p.close()
  result.rc = rc
  result.caught = "CAUGHT" in result.output
  result.finallyRan = "FINALLY" in result.output
  result.returned = "RET " in result.output
  echo "NATIVE ", hostOS, " ", tag, ": rc=", rc, " caught=", result.caught,
       " finally=", result.finallyRan, " returned=", result.returned,
       " timedOut=", result.timedOut

suite "S8cu: a nil dereference, natively, on this host":

  test "goto exceptions with std/segfaults: not caught, no finally":
    let o = probe("goto_segfaults", @["-d:withSegfaults"])
    checkpoint o.output
    check not o.caught
    check not o.finallyRan
    check not o.returned

  test "goto exceptions, release, with std/segfaults: not caught, no finally":
    let o = probe("goto_segfaults_release", @["-d:withSegfaults", "-d:release"])
    checkpoint o.output
    check not o.caught
    check not o.finallyRan
    check not o.returned

  test "setjmp exceptions: recorded (the walker declines under a try)":
    let o = probe("setjmp", @["--exceptions:setjmp"])
    checkpoint o.output
    check o.rc != 0 or o.returned          # it ran to some end

  test "setjmp exceptions with std/segfaults: recorded (the walker declines)":
    let o = probe("setjmp_segfaults", @["--exceptions:setjmp", "-d:withSegfaults"])
    checkpoint o.output
    check o.rc != 0 or o.returned
