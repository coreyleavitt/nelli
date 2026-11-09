## RFC-0016 K10c -- `-ffp-contract`: the Linux x86-64 row does not contract.
##
## gcc's default is `-ffp-contract=fast`: it MAY fuse `a * b + c` into one
## rounding. Whether it does depends on the target having a fused multiply-add
## instruction, and baseline x86-64 has none, so the default build computes
## the two roundings the walker's floating-point terms model. nelli cannot
## read C flags (`BuildProvenance.assumedAbsent`), so this is the pin:
##
##  * the walker (`symexFind`) finds the operands for which the unfused and
##    the fused result differ, and the witness hits natively in this build;
##  * a one-off child build with `-ffp-contract=off` computes the same bits as
##    a default child build;
##  * a child built with `-mfma -ffp-contract=fast` computes the OTHER bits
##    (so the operands do tell the two apart, and the claim above has teeth).
##    A CPU without FMA declares that cell instead of running it.
##
## The operands: with a = b = 1 + 2^-30 and c = -(1 + 2^-29), a*b is
## 1 + 2^-29 + 2^-60, which one rounding keeps as 1 + 2^-29 + 2^-60 and two
## roundings drop to 1 + 2^-29. The sum is 2^-60 fused and 0 unfused.
##
## MSVC is declared, not run (its contraction default is the compiler's own
## and has no leg that pins it).
import std/[unittest, strutils, os, osproc, sequtils]
import nelli
import nelli/symex
import nelli/smt/buildprofile
import ./s8cu_helpers

const
  cell = "cflags/fpContract"
  aLit = 1.000000000931322574615478515625          # 1 + 2^-30
  cLit = -1.00000000186264514923095703125          # -(1 + 2^-29)
  fusedBits = (1023'u64 - 60'u64) shl 52           # 2^-60
  unfusedBits = 0'u64

proc sutFma(a, b, c: float) =
  if a == 1.000000000931322574615478515625 and
     b == 1.000000000931322574615478515625 and
     c == -1.00000000186264514923095703125 and a * b + c == 0.0:
    symexTarget("hit")

const probeSrc = """
import std/[os, strutils]
proc mac(a, b, c: float64): float64 {.noinline.} = a * b + c
let a = cast[float64](parseBiggestUInt(paramStr(1)))
let b = cast[float64](parseBiggestUInt(paramStr(2)))
let c = cast[float64](parseBiggestUInt(paramStr(3)))
echo cast[uint64](mac(a, b, c))
"""

proc hasFma(): bool =
  when defined(linux):
    try: " fma " in (readFile("/proc/cpuinfo").splitLines.filterIt(it.startsWith("flags"))[0] & " ")
    except CatchableError: false
  else: false

proc bitsOf(v: float64): uint64 = cast[uint64](v)

proc runProbe(extra: seq[string]): uint64 =
  ## Builds the one-off probe with `extra` C flags (at -O2: contraction is an
  ## optimiser pass) and returns the bits of `a * b + c`.
  let pb = prepareProbe("fma", probeSrc, @["--passC:-O2"] & extra)
  defer: removeDir(pb.dir)
  let (cout, crc) = execCmdEx(pb.cmd)
  doAssert crc == 0, "the fma probe did not build:\n" & cout
  let (o, rc) = execCmdEx(quoteShellCommand(
    @[pb.exe, $bitsOf(aLit), $bitsOf(aLit), $bitsOf(cLit)]))
  doAssert rc == 0, "the fma probe failed: " & o
  parseBiggestUInt(o.strip).uint64

suite "K10c: -ffp-contract":
  test "the operands separate fused from unfused":
    check bitsOf(aLit * aLit + cLit) == unfusedBits       # this build: unfused

  when defined(vcc):
    test "msvc: declared, not run":
      skipCell(cellKey(axBuild, cell), "cl.exe has no -ffp-contract flag and " &
        "no leg pins its contraction default; the row is declared")
  else:
    test "the walker's unfused result hits natively in the default build":
      let r = pinExact(sutFma, cellKey(axBuild, cell),
                      domain = sampled([0.0, 1.0, aLit, cLit]))
      check r.status == sxSat

    when defined(windows):
      test "mingw: the one-off builds are the Linux row's":
        skipCell(cellKey(axBuild, cell), "the -ffp-contract one-off builds are " &
          "pinned on the Linux x86-64 legs; mingw is covered by the walker pin")
    else:
      test "-ffp-contract=off equals the default build":
        let dflt = runProbe(@[])
        let off = runProbe(@["--passC:-ffp-contract=off"])
        check dflt == unfusedBits
        check off == dflt
        pinNever(cellKey(axBuild, cell), dflt == unfusedBits and off == dflt,
          "default and -ffp-contract=off both compute " & $dflt &
          " (a*b rounded, then +c)")

      test "-mfma -ffp-contract=fast computes the fused bits":
        if hasFma():
          let fused = runProbe(@["--passC:-mfma", "--passC:-ffp-contract=fast"])
          check fused == fusedBits
        else:
          skipCell(cellKey(axBuild, cell), "this CPU has no FMA, so the " &
            "contracting build cannot run; the default/off equality above stands")
