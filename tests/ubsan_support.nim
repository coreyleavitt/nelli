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
proc conv32[S](x: float32): S {.noinline.} = S(x)

let ty = paramStr(1)
let op = paramStr(2)      # "f2i": a float64 operand, "f32i": a float32 one
let f = cast[float64](parseBiggestUInt(paramStr(3)))

template go(S: typedesc) =
  if op == "f32i": echo conv32[S](float32(f))
  else: echo conv[S](f)

case ty
of "int64": go(int64)
of "int32": go(int32)
of "int16": go(int16)
of "int8": go(int8)
of "uint64": go(uint64)
of "uint32": go(uint32)
of "uint16": go(uint16)
of "uint8": go(uint8)
else: quit(3)
"""
  ## RFC-0016 K10c, the float -> int cells. The operand is the bit pattern of a
  ## `float64` (argument 3; narrowed to a `float32` for op `f32i`, so the
  ## caller passes only float32-representable values there); the conversion is
  ## Nim's plain C cast. Built with
  ## `-fsanitize=float-cast-overflow`, which gcc does not include in
  ## `-fsanitize=undefined`.

const indexProbeSrc* = """
import std/[os, strutils]

type
  R = range[0 .. 10]
  E = enum ea, eb, ec

var gR: array[R, int]
var gI: array[11, int]
var gE: array[E, int]

proc idv(x: int): int {.noinline.} = x
proc rdR(i: int): int {.noinline.} = gR[R(i)]
proc wrR(i: int) {.noinline.} = gR[R(i)] = 1
proc rdE(i: int): int {.noinline.} = gE[E(i)]
proc rdI(i: int): int {.noinline.} = gI[i]
proc wrI(i: int) {.noinline.} = gI[i] = 1
proc rdS(s: seq[int]; i: int): int {.noinline.} = s[i]
proc wrS(s: var seq[int]; i: int) {.noinline.} = s[i] = 1
proc rdO(s: openArray[int]; i: int): int {.noinline.} = s[i]
proc rdT(s: string; i: int): char {.noinline.} = s[i]
proc wrT(s: var string; i: int) {.noinline.} = s[i] = 'x'

let ty = paramStr(1)          # the container
let op = paramStr(2)          # "rd" or "wr"
let k = cast[int](parseBiggestUInt(paramStr(3)))
var sq = newSeq[int](3)
var st = newString(3)
case ty
of "arrR": (if op == "rd": echo rdR(idv(k)) else: wrR(idv(k)))
of "arrE": echo rdE(idv(k))
of "arrI": (if op == "rd": echo rdI(idv(k)) else: wrI(idv(k)))
of "seq": (if op == "rd": echo rdS(sq, idv(k)) else: wrS(sq, idv(k)))
of "oa": echo rdO(sq, idv(k))
of "str": (if op == "rd": echo ord(rdT(st, idv(k))) else: wrT(st, idv(k)))
else: quit(3)
"""
  ## RFC-0016 PRC-07, the `index/unchecked` cell. One element access of one
  ## container, at an index from the command line (the bit pattern of an
  ## `int`), through `noinline` routines so no optimisation folds it away. The
  ## arrays are globals: gcc's `-fsanitize=bounds` sees a C array object, never
  ## a parameter (which decays to a pointer). A seq's, an openArray's and a
  ## string's elements are heap memory behind a pointer, which only
  ## AddressSanitizer over `malloc` (`-d:useMalloc`) bounds.

const objProbeSrc* = """
import std/os

type
  Base = ref object of RootObj
    x: int
  Der = ref object of Base
    pad: array[16, int]
    y: int

proc mk(ty: string): Base {.noinline.} =
  case ty
  of "base": Base(x: 1)
  of "der": Der(x: 1, y: 2)
  else: nil

proc rd(b: Base): int {.noinline.} =
  let d = Der(b)
  if d == nil: 0 else: d.pad[15] + d.y

echo rd(mk(paramStr(1)))
"""
  ## RFC-0016 PRC-07, the `conv/objDowncast` cell. `Der(b)` of a `Base` whose
  ## dynamic type is `ty` (`base`, `der`, `nil`), then a read of `Der`'s last
  ## fields. `Der` is the larger type, so for an actual `Base` the read is
  ## past the allocation, which AddressSanitizer over `malloc`
  ## (`-d:useMalloc`) bounds.

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

func indexBoundsFlags*(extra: openArray[string]): seq[string] =
  ## The index probe's build: the option under test (`extra`), UBSan's
  ## `bounds` check made fatal (it sees an indexed C array object).
  @extra & @["--passC:-fsanitize=bounds", "--passL:-fsanitize=bounds",
             "--passC:-fno-sanitize-recover=all"]

func indexAsanFlags*(extra: openArray[string]): seq[string] =
  ## The index probe's build for heap containers: Nim's allocator is its own
  ## arena AddressSanitizer cannot see into, so `-d:useMalloc` puts a seq's and
  ## a string's data on `malloc`'s redzones.
  @extra & @["-d:useMalloc", "--passC:-fsanitize=address",
             "--passL:-fsanitize=address", "--passC:-fno-omit-frame-pointer"]

proc buildIndexProbe*(who: string; flags: openArray[string]): UbsanProbe =
  ## Compiles the index probe once with `flags`.
  result.build = prepareProbe(who, indexProbeSrc, flags)
  let (cout, crc) = execCmdEx(result.build.cmd)
  if crc != 0:
    raise newException(PinFailure, who & ": the index probe did not build:\n" &
                       cout)

func objAsanFlags*(extra: openArray[string]): seq[string] =
  ## `indexAsanFlags` for the object-conversion probe.
  indexAsanFlags(extra)

proc buildObjProbe*(who: string; flags: openArray[string]): UbsanProbe =
  ## Compiles the object-conversion probe once with `flags`.
  result.build = prepareProbe(who, objProbeSrc, flags)
  let (cout, crc) = execCmdEx(result.build.cmd)
  if crc != 0:
    raise newException(PinFailure, who & ": the object probe did not " &
                       "build:\n" & cout)

proc dispose*(p: UbsanProbe) = removeDir(p.build.dir)

proc runCase*(p: UbsanProbe; c: UbCase): tuple[rc: int, output: string] =
  let (o, rc) = execCmdEx(quoteShellCommand(
    @[p.build.exe, c.ty, c.op, $c.a, $c.b]))
  (rc, o)

func tripped(rc: int; output: string): bool =
  rc != 0 and ("runtime error:" in output or "AddressSanitizer" in output)

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
