## RFC-0016 K10c. The native UBSan witness for the definedness table.
##
## The definedness axis (`smt/definedness.nim`) says what the C a build
## compiles makes of an operation. This module is the C compiler's own answer:
## one child program, built once with `-fsanitize=undefined
## -fno-sanitize-recover=all`, that performs one arithmetic operation of one
## integer type on operands from its command line. An input the table calls
## undefined must trip UBSan ("runtime error:", a non-zero exit); an input it
## calls defined must run clean. A disagreement fails the pin, so the table is
## checked against C and not against itself.
##
## The operands arrive at run time, through a `noinline` routine, so no
## optimisation level can fold the operation away before UBSan sees it.
## Linux and macOS gcc/clang only: mingw and MSVC have no UBSan runtime, and
## the callers declare those legs with `skipCell`.
import std/[os, osproc, strutils, sequtils]
import ./s8cu_helpers

const ubsanProbeSrc* = """
import std/[os, strutils]

proc calc[S](op: string; a, b: S): S {.noinline.} =
  case op
  of "add": a + b
  of "sub": a - b
  of "mul": a * b
  of "div": a div b
  of "mod": a mod b
  else: quit(2)

proc conv[S](u: uint64): S {.noinline.} = cast[S](u)

let ty = paramStr(1)
let op = paramStr(2)
let a = parseBiggestUInt(paramStr(3))
let b = parseBiggestUInt(paramStr(4))

template go(S: typedesc) =
  echo calc[S](op, conv[S](a), conv[S](b))

case ty
of "int64": go(int64)
of "int32": go(int32)
of "int16": go(int16)
of "int8": go(int8)
of "uint64": go(uint64)
of "uint32": go(uint32)
of "uint16": go(uint16)
else: quit(3)
"""

const floatToIntProbeSrc* = """
import std/[os, strutils]

proc conv[S](x: float64): S {.noinline.} = S(x)

let ty = paramStr(1)
let f = cast[float64](parseBiggestUInt(paramStr(3)))

template go(S: typedesc) =
  echo conv[S](f)

case ty
of "int64": go(int64)
of "int32": go(int32)
of "int16": go(int16)
of "int8": go(int8)
else: quit(3)
"""
  ## RFC-0016 K10c, the float -> int cell. The operand is the bit pattern of a
  ## `float64` (argument 3); the conversion is Nim's plain C cast. Built with
  ## `-fsanitize=float-cast-overflow`, which gcc does not include in
  ## `-fsanitize=undefined`.

type
  UbExpect* = enum
    ueClean   ## the C operation is defined for these operands: exit 0
    ueTrip    ## undefined: UBSan reports it (or, where allowed, the CPU traps)

  UbCase* = object
    ty*, op*: string     ## "int32", "div"
    a*, b*: uint64       ## operand bit patterns (sign-extended for signed)
    expect*: UbExpect
    cond*: bool          ## the operands meet the row's condition (overflow,
                         ## zero divisor, low by -1), decided without C

  UbsanProbe* = object
    build*: ProbeBuild
    fwrapv*: bool

func ubsanFlags*(fwrapv: bool): seq[string] =
  ## The probe's checks-off build (the profile `dpUnchecked`; with `fwrapv`,
  ## `dpFwrapv`) with the sanitizer on and made fatal.
  result = @["--overflowChecks:off", "--rangeChecks:off",
             "--passC:-fsanitize=undefined",
             "--passC:-fno-sanitize-recover=all",
             "--passL:-fsanitize=undefined"]
  if fwrapv: result.add "--passC:-fwrapv"

proc buildUbsanProbe*(who: string; fwrapv = false): UbsanProbe =
  ## Compiles the probe once. A compile failure fails the pin with the
  ## compiler's output (a missing `libubsan` shows up here, by name).
  result.fwrapv = fwrapv
  result.build = prepareProbe(who, ubsanProbeSrc, ubsanFlags(fwrapv))
  let (cout, crc) = execCmdEx(result.build.cmd)
  if crc != 0:
    raise newException(PinFailure, who & ": the UBSan probe did not build:\n" &
                       cout)

func floatToIntFlags*(): seq[string] =
  ## The checks-off build with the float-cast sanitizer on and made fatal.
  ubsanFlags(false) & @["--passC:-fsanitize=float-cast-overflow",
                        "--passL:-fsanitize=float-cast-overflow"]

proc buildFloatToIntProbe*(who: string): UbsanProbe =
  ## Compiles the float -> int probe once (`-fsanitize=float-cast-overflow`).
  result.build = prepareProbe(who, floatToIntProbeSrc, floatToIntFlags())
  let (cout, crc) = execCmdEx(result.build.cmd)
  if crc != 0:
    raise newException(PinFailure, who & ": the float-cast probe did not " &
                       "build:\n" & cout)

proc dispose*(p: UbsanProbe) = removeDir(p.build.dir)

proc runCase*(p: UbsanProbe; c: UbCase): tuple[rc: int, output: string] =
  let (o, rc) = execCmdEx(quoteShellCommand(
    @[p.build.exe, c.ty, c.op, $c.a, $c.b]))
  (rc, o)

func tripped(rc: int; output: string): bool =
  rc != 0 and "runtime error:" in output

func hardTrapped(rc: int; output: string): bool =
  ## SIGFPE from the divide instruction: `-fwrapv` retires the signed-overflow
  ## instrumentation, and the hardware still faults on `low(T) div -1`.
  rc == 128 + 8 or "SIGFPE" in output

proc pinUbsanCell*(key: CellKey; p: UbsanProbe; cases: openArray[UbCase];
                   hardTrapOk = false) =
  ## Every case of a cell holds: `ueTrip` cases trip, `ueClean` cases run
  ## clean. The cases must include operands that meet the row's condition and
  ## operands that do not (a cell whose cases all agree proves nothing): where
  ## the row is undefined the first kind trips, where it is defined it runs
  ## clean, and that difference is what the table is checked on. With `hardTrapOk` a `ueTrip` case may end
  ## in the CPU's divide fault instead of a UBSan report (`-fwrapv`).
  ## Records one `pvCrashed` record, entry `pinUbsan`: it is not one of the
  ## six public entries, so it is the native half and never the evidence.
  let cell = render(key)
  var trips, cleans, met, unmet = 0
  for c in cases:
    let (rc, output) = p.runCase(c)
    let what = cell & " " & c.ty & " " & c.op & " " & $c.a & " " & $c.b
    case c.expect
    of ueTrip:
      let ok = tripped(rc, output) or (hardTrapOk and hardTrapped(rc, output))
      if not ok:
        raise newException(PinFailure, "pinUbsan " & what &
          ": the table calls this undefined but C ran it (rc=" & $rc &
          "): " & output.strip)
      inc trips
    of ueClean:
      if rc != 0:
        raise newException(PinFailure, "pinUbsan " & what &
          ": the table calls this defined but it faulted (rc=" & $rc &
          "): " & output.strip)
      inc cleans
    if c.cond: inc met else: inc unmet
  if met == 0 or unmet == 0:
    raise newException(PinFailure, "pinUbsan " & cell & ": " & $met &
      " cases meet the condition and " & $unmet & " do not; a cell needs both")
  writePinRecord(PinRecord(testFile: splitFile(getAppFilename()).name & ".nim",
    entry: "pinUbsan", cell: key, target: "-", domain: "-",
    verdict: pvCrashed,
    native: $trips & " tripped, " & $cleans & " clean (" &
            (if p.fwrapv: "-fwrapv " else: "") & "UBSan)",
    flags: @(p.build.args) & @[p.build.backend]))
