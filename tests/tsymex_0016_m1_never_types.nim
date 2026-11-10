## RFC-0016 W3-z (M1): the `never` magic rows that are types, threadpool or
## DrNim names, or routines this toolchain does not declare for a SUT. Each is
## `pinNever`: the native fact that says the walker has nothing to model (the
## magic is a type, not a callee; or the routine does not compile under the
## default --mm:orc, a flag a test file cannot set). Nothing here reaches the
## walker; the rows stay `iNever`.
import std/[unittest, math, isolation, importutils, logic]
import std/macros
{.push warning[Deprecated]: off.}
import std/threadpool
{.pop.}
import nelli/smt/admission
import nelli/smt/magic_rows
import ./s8cu_helpers

type M1Obj = object
  x: int

proc m1Void() = discard
proc m1Id(x: int): int = x
proc m1Oa(x: openArray[int]): int = x.len
proc m1Va(x: varargs[int]): int = x.len
proc m1St(x: static int): int = x
proc m1Sink(x: sink string): int = x.len

proc isNeverRow(cell: string): bool =
  for c in magicAxis.cells:
    if c.cell.key == cell: return not c.admitted and c.intent == iNever

template never(cell: static string; holds: bool; native: string) =
  test cell:
    check isNeverRow(cell)
    pinNever(cellKey(axMagic, cell), holds, native)

suite "M1: type and construct magics are not callees":
  never("Array", sizeof(array[3, int16]) == 6,
        "array[3, int16] is a 6-byte type, not a call")
  never("Bool", sizeof(bool) == 1 and (true is bool),
        "bool is a 1-byte enum type")
  never("BuiltinType", m1Sink("abc") == 3,
        "sink/lent/owned are type constructors; a sink parameter is an ordinary call")
  never("Exception", ValueError is Exception,
        "Exception is the root type of the hierarchy")
  never("Nil", (block:
          var p: ptr int = nil
          p.isNil),
        "nil is a literal of every pointer type")
  never("Range", high(range[0 .. 3]) == 3, "range[0..3] is a type")
  never("Seq", newSeq[int](2).len == 2, "seq[T] is a type constructor")
  never("Set", sizeof(set[char]) == 32, "set[char] is a 32-byte bitset type")
  never("Static", m1St(4) == 4, "static[int] is a parameter type")
  never("Type", type(3) is int, "type(x) is a type expression")
  never("UncheckedArray", compiles((var u: ptr UncheckedArray[int])),
        "UncheckedArray[T] is a type constructor")
  never("OpenArray", m1Oa([1, 2]) == 2, "openArray[T] is a parameter type")
  never("Varargs", m1Va(1, 2, 3) == 3, "varargs[T] is a parameter type")
  never("VoidType", typeof(m1Void()) is void, "void is the absent type")
  never("PNimrodNode", sizeof(NimNode) == sizeof(pointer),
        "NimNode is a compile-time reference type")

suite "M1: threadpool, experimental and DrNim names":
  never("Spawn", (^spawn m1Id(3)) == 3,
        "spawn runs on the threadpool; it is not a SUT shape")
  never("Parallel", not compiles(block:
          parallel:
            discard),
        "parallel needs {.experimental: \"parallel\".}, which no SUT sets")
  never("OmpParFor", (block:
          var s = 0
          for i in 0 || 3: s += i
          s == 6),
        "|| is an ordinary serial loop without --openmp")
  never("Isolate", typeof(isolate(3)) is Isolated[int],
        "isolate is a move wrapper of std/isolation")
  never("Unown", unown(3) == 3, "unown is the identity under --mm:orc")
  never("PrivateAccess", (block:
          privateAccess(M1Obj)
          true),
        "privateAccess only widens symbol lookup at compile time")
  never("Plugin", (block:
          var z = 2
          let t = locals()
          t.z == 2),
        "locals() builds a tuple of the scope; an iterToProc plugin is compiler code")
  never("Implies", compiles(true -> true),
        "-> passes semantic checking but codegen fails (genMagicExpr: mImplies): a DrNim operator")
  never("Iff", compiles(true <-> true),
        "<-> passes semantic checking but has no codegen: a DrNim operator")
  never("Forall", compiles(forall(true)),
        "forall passes semantic checking (varargs[untyped]) but is a DrNim quantifier, used only inside .ensures")
  never("Exists", compiles(exists(true)),
        "exists passes semantic checking (varargs[untyped]) but is a DrNim quantifier, used only inside .ensures")
  never("Old", not compiles(old(1)),
        "old is a DrNim postcondition operator, used only inside .ensures; ordinary code does not compile it")

suite "M1: routines this toolchain does not offer a SUT":
  never("ShallowCopy", not compiles((var a, b = 1; shallowCopy(a, b))) and
        not defined(gcRefc),
        "shallowCopy is declared only for refc/markAndSweep, not --mm:orc")
  never("DeepCopy", not defined(gcRefc) and not defined(gcMarkAndSweep),
        "deepCopy needs --deepcopy:on outside refc (observed: the compile stops: deepcopy support has to be enabled), a flag a test file cannot set")
  never("GetTypeInfoV2", not declared(getDynamicTypeInfo),
        "getDynamicTypeInfo lives in system/cyclebreaker, which system does not export")
  never("BuildOS", not declared(buildOS),
        "buildOS is declared by system/nimscript only, not for native code")
  never("BuildCPU", not declared(buildCPU),
        "buildCPU is declared by system/nimscript only, not for native code")
  never("nextafter", not declared(nextafter),
        "Nim 2.2 std/math has no nextafter to call")
