## RFC-0016 K8b (INT-56, §10 "Families from the axes", §12 item 4): the
## program fragment that exercises each exact row of an admission axis.
##
## A fragment is Nim source over the SUT's inputs `a, b: int8` and their
## widenings `t = int(a)`, `u = int(b)`: optional top-level declarations
## (`top`), statements (`pre`) and an `int` expression (`expr`) the SUT adds
## to its accumulator. `N_` in the text becomes a name unique to the program
## and the row (top-level declarations), `V_` one unique to the row inside the
## SUT (locals). A fragment that can raise (`raises`) is one whose row is an
## operation's defined failure (a defect); a program holding one gets no
## reordering relation, since which raise comes first is then observable.
##
## A row with no fragment is not exercised, and the axis figure
## (`tests/s0016_k8b_axes.nim`) counts it as such: the table here is the
## generator's reach, the axis table (`cells(axis)`) is the denominator.
## Every key here must be a modelled row of its axis (checked by
## `tsymex_0016_k8b_axes`), so a row that leaves `exact` fails here too.
import nelli/smt/admission

type
  AxisScope* = range[axTypeClass .. axDefinedness]
    ## The admission axes other than construct (K8a-gen's shapes).
  Snippet* = object
    key*: string
    top*, pre*, expr*: string
    raises*: bool
    cfg*: string
      ## The build axis only: the compile switch the row is (a line of its
      ## suite's `.nim.cfg` or `.nims`, `s0016_k8b_axes.buildSuites`). A build
      ## row is a property of the whole binary, so its fragment runs only in a
      ## suite compiled under that switch; "" is the default build.
    post*: string
      ## Statements run after the predicate (past the label): an opaque
      ## foreign call there leaves the verdict's tail undefined
      ## (`ubTailUnverified`), where one before it declines the run
      ## (`feOpaqueCallUnmodelled`).
    undefined*: string
      ## RFC-0016 INT-69: the `UbKind` the row's modelled answer carries (a
      ## `{.noinit.}` read, an opaque foreign body), "" for a defined row. A
      ## program holding one is judged as `pinUndefined` judges a cell: its
      ## `sxSat` is untrusted only by that kind, and its witness hits
      ## natively (`s8cu_helpers.pinJudge`'s `undefined`).

func sn(key, expr: string; pre = ""; top = ""; raises = false;
        cfg = ""; undefined = ""; post = ""): Snippet =
  Snippet(key: key, expr: expr, pre: pre, top: top, raises: raises, cfg: cfg,
          undefined: undefined, post: post)

const magicSnippets = @[
  sn("AbsI", "abs(t)"),
  sn("AddF64", "int(float(t) + float(u))"),
  sn("AddI", "t + u"),
  sn("AddU", "int(uint8(t + 128) + uint8(u + 128))"),
  sn("Addr", "V_p[]", "var V_x = t\n  let V_p = addr V_x"),
  sn("And", "ord(t > 0 and u > 0)"),
  sn("AppendSeqElem", "V_s.len + V_s[1]", "var V_s = @[t]\n  V_s.add u"),
  sn("AppendStrCh", "V_s.len", "var V_s = \"ab\"\n  V_s.add chr(t + 128)"),
  sn("AppendStrStr", "V_s.len", "var V_s = \"ab\"\n  V_s.add $t"),
  sn("ArrGet", "[t, u, 3][1]"),
  sn("ArrPut", "V_r[0] + V_r[1]", "var V_r = [t, 0]\n  V_r[1] = u"),
  sn("ArrToSeq", "@[t, u].len + @[t, u][0]"),
  sn("Asgn", "V_x", "var V_x = 0\n  V_x = u"),
  sn("AshrI", "ashr(t, 2)"),
  sn("BitandI", "t and u"),
  sn("BitnotI", "not t"),
  sn("BitorI", "t or u"),
  sn("BitxorI", "t xor u"),
  sn("BoolToStr", "len($(t > u))"),
  sn("Card", "card(V_s)", "var V_s: set[int8]\n  V_s.incl a\n  V_s.incl b"),
  sn("CharToStr", "len($chr(t + 128))"),
  sn("Chr", "ord(chr(t + 128))"),
  sn("ConStrStr", "len(\"ab\" & $t)"),
  sn("Dec", "V_x", "var V_x = t\n  dec V_x"),
  sn("Default", "default(int) + t"),
  sn("DivF64", "int(float(t) / 4.0)"),
  sn("DivI", "t div 3"),
  sn("DivU", "int(uint8(t + 128) div 3'u8)"),
  sn("EqB", "ord((t > 0) == (u > 0))"),
  sn("EqCh", "ord(chr(t + 128) == 'A')"),
  sn("EqEnum", "ord(N_E(t and 1) == N_E(u and 1))",
     top = "type N_E = enum N_e0, N_e1"),
  sn("EqF64", "ord(float(t) == float(u))"),
  sn("EqI", "ord(t == u)"),
  sn("EqRef", "ord(V_r == V_q)", "let V_r = N_R(x: t)\n  let V_q = V_r",
     top = "type N_R = ref object\n  x: int"),
  sn("EqSet", "ord({a} == {b})"),
  sn("EqStr", "ord($t == $u)"),
  sn("Excl", "card(V_s)", "var V_s = {a, b}\n  V_s.excl a"),
  sn("High", "high(int8) + t"),
  sn("InSet", "ord(a in {int8(1) .. int8(9)})"),
  sn("Inc", "V_x", "var V_x = t\n  inc V_x, 2"),
  sn("Incl", "card(V_s)", "var V_s = {a}\n  V_s.incl b"),
  sn("Int64ToStr", "len($int64(t))"),
  sn("IntToStr", "len($t)"),
  sn("IsNil", "ord(isNil(V_r))",
     "var V_r: N_R = nil\n  if t > 0: V_r = N_R(x: t)",
     top = "type N_R = ref object\n  x: int"),
  sn("LeB", "ord((t > 0) <= (u > 0))"),
  sn("LeCh", "ord(chr(t + 128) <= chr(u + 128))"),
  sn("LeEnum", "ord(N_E(t and 1) <= N_E(u and 1))",
     top = "type N_E = enum N_e0, N_e1"),
  sn("LeF64", "ord(float(t) <= float(u))"),
  sn("LeI", "ord(t <= u)"),
  sn("LeSet", "ord({a} <= {a, b})"),
  sn("LeStr", "ord($t <= $u)"),
  sn("LeU", "ord(uint8(t + 128) <= uint8(u + 128))"),
  sn("LengthArray", "len([t, u, 1])"),
  sn("LengthSeq", "V_s.len", "let V_s = @[t, u]"),
  sn("LengthStr", "len($t)"),
  sn("Low", "low(int8) + t"),
  sn("LtB", "ord((t > 0) < (u > 0))"),
  sn("LtCh", "ord(chr(t + 128) < chr(u + 128))"),
  sn("LtEnum", "ord(N_E(t and 1) < N_E(u and 1))",
     top = "type N_E = enum N_e0, N_e1"),
  sn("LtF64", "ord(float(t) < float(u))"),
  sn("LtI", "ord(t < u)"),
  sn("LtSet", "ord({a} < {a, b})"),
  sn("LtStr", "ord($t < $u)"),
  sn("LtU", "ord(uint8(t + 128) < uint8(u + 128))"),
  sn("MaxI", "max(t, u)"),
  sn("MinI", "min(t, u)"),
  sn("MinusSet", "card({a, b} - {a})"),
  sn("ModI", "t mod 3"),
  sn("ModU", "int(uint8(t + 128) mod 3'u8)"),
  sn("MulF64", "int(float(t) * 1.5)"),
  sn("MulI", "t * u"),
  sn("MulSet", "card({a, b} * {a})"),
  sn("MulU", "int(uint8(t + 128) * 3'u8)"),
  sn("New", "V_r.x + t", "var V_r: N_R\n  new(V_r)",
     top = "type N_R = ref object\n  x: int"),
  sn("NewSeq", "V_s.len + V_s[1]", "var V_s = newSeq[int](3)\n  V_s[1] = t"),
  sn("NewString", "ord(V_s[1])", "var V_s = newString(2)\n  V_s[1] = chr(t + 128)"),
  sn("Not", "ord(not (t > u))"),
  sn("Or", "ord(t > 0 or u > 0)"),
  sn("Ord", "ord(a)"),
  sn("PlusSet", "card({a} + {b})"),
  sn("Pred", "pred(t)"),
  sn("ShlI", "t shl 2"),
  sn("ShrI", "t shr 2"),
  sn("SizeOf", "sizeof(int16) + t"),
  sn("SubF64", "int(float(t) - float(u))"),
  sn("SubI", "t - u"),
  sn("SubU", "int(uint8(t + 128) - uint8(u + 128))"),
  sn("Succ", "succ(t)"),
  sn("Swap", "V_x - V_y", "var V_x = t\n  var V_y = u\n  swap(V_x, V_y)"),
  sn("UnaryMinusF64", "int(-float(t))"),
  sn("UnaryMinusI", "-t"),
  sn("UnaryMinusI64", "int(-int64(t))"),
  sn("UnaryPlusF64", "int(+float(t))"),
  sn("UnaryPlusI", "+t"),
  sn("Xor", "ord((t > 0) xor (u > 0))"),
  sn("ZeroDefault", "V_x + t", "var V_x: int"),
  sn("Defined", "(when defined(nelliNoSuchDefine): 1 else: 0) + t"),
  sn("Compiles", "(when compiles(t + u): 1 else: 0) + t"),
  sn("Declared", "(when declared(V_none): 1 else: 0) + t"),
  sn("TypeOf", "(when typeof(t) is int: 1 else: 0) + t"),
  sn("Is", "(when int8 is SomeInteger: 1 else: 0) + t"),
  sn("IsMainModule", "ord(isMainModule) + t"),
  sn("CompileOption", "ord(compileOption(\"boundChecks\")) + t"),
  # spelled in two pieces: the K2a census counts `hostOS` as a platform arm of
  # the test, and this is SUT text the walker folds to a constant, not an arm
  sn("HostOS", "len(host" & "OS) + t"),
  sn("HostCPU", "len(hostCPU) + t"),
  sn("CpuEndian", "ord(cpuEndian) + t"),
  sn("AppType", "len(appType) + t"),
  sn("AstToStr", "len(astToStr(t + u)) + t"),
  sn("StrToStr", "len($\"ab\") + t"),
  sn("NewSeqOfCap", "V_s.len", "var V_s = newSeqOfCap[int](4)\n  V_s.add t"),
  sn("NewStringOfCap", "V_s.len", "var V_s = newStringOfCap(4)\n  V_s.add 'x'"),
  sn("SetLengthSeq", "V_s.len + V_s[0]", "var V_s = @[t]\n  V_s.setLen(3)"),
  sn("SetLengthStr", "V_s.len", "var V_s = $t\n  V_s.setLen(1)"),
  sn("LengthOpenArray", "N_len([t, u])",
     top = "proc N_len(xs: openArray[int]): int = xs.len + xs[0]"),
  sn("OpenArrayToSeq", "N_toS([t, u])",
     top = "proc N_toS(xs: openArray[int]): int =\n  let s = @xs\n  s.len + s[1]"),
  sn("Slice", "V_s.len + ord(V_s[0])", "let V_s = ($t & \"ab\")[0 .. 1]"),
  # the row is `..` in a for or slice head; as a value it declines by design
  sn("DotDot", "V_x", "var V_x = 0\n  for V_i in 0 .. (t and 3): V_x += V_i"),
  sn("Move", "V_y.len + V_y[0]", "var V_x = @[t]\n  let V_y = move(V_x)"),
  sn("WasMoved", "V_x + t", "var V_x = u\n  wasMoved(V_x)"),
  sn("EnsureMove", "V_y.len", "var V_x = @[t]\n  let V_y = ensureMove(V_x)"),
  sn("EnumToStr", "len($N_E(t and 1))", top = "type N_E = enum N_e0, N_e1x"),
  sn("Of", "ord(V_r of N_D)",
     "let V_r: N_B = (if t > 0: N_D(x: t) else: N_B(x: t))",
     top = "type\n  N_B = ref object of RootObj\n    x: int\n" &
           "  N_D = ref object of N_B"),
  sn("FieldPairs", "V_n", "var V_n = 0\n  for k, v in fieldPairs((x: t, y: u)): V_n += v"),
  sn("Fields", "V_n", "var V_n = 0\n  for v in fields((x: t, y: u)): V_n += v"),
  sn("OffsetOf", "offsetOf(N_O, y) + t", top = "type N_O = object\n  x: int8\n  y: int"),
  sn("AlignOf", "alignof(int16) + t"),
  sn("EqCString", "ord(V_c == cstring(\"ab\"))", "let V_c = cstring(if t > 0: \"ab\" else: \"cd\")"),
  sn("EqProc", "ord(V_p == N_f)", "let V_p = (if t > 0: N_f else: N_g)",
     top = "proc N_f(x: int): int = x\nproc N_g(x: int): int = -x"),
  # a shrink: a grow leaves elements unwritten and declines by design
  sn("SetLengthSeqUninit", "V_s.len + V_s[0]",
     "var V_s = @[t, u, 1]\n  V_s.setLenUninit(1)"),
  # a plain value type (a seq's `=dup` declines: the row is the plain copy)
  sn("Dup", "V_y", "var V_x = t\n  let V_y = `=dup`(V_x)\n  V_x = u"),
  # a side effect on a path no input reaches (t, u <= 127), so the native
  # runs neither print nor stop
  sn("Echo", "t", "if t > 126 and u > 126 and t < 0: echo \"k8b\""),
  sn("Exit", "t", "if t > 126 and t < 0: quit(3)"),
  sn("DeclaredInScope", "(when declaredInScope(V_none): 1 else: 0) + t"),
  sn("CompileOptionArg", "ord(compileOption(\"gc\", \"orc\")) + t"),
  # the suite's own main file (`std/compilesettings`, imported by the magic
  # suites): generated code has no source path to resolve a relative one by
  sn("Slurp", "ord(N_s.len > 0) + t",
     top = "const N_s = staticRead(querySetting(projectFull))"),
  sn("StaticExec", "ord(N_s.len > 0) + t",
     top = "const N_s = staticExec(\"echo k8b\")"),
  sn("RunnableExamples", "N_f(t)",
     top = "proc N_f(x: int): int =\n  runnableExamples: discard\n  x + 1"),
  sn("InstantiationInfo", "ord(N_w() > 0) + t",
     top = "template N_w(): int = instantiationInfo().line"),
  sn("CompileDate", "len(CompileDate) + t"),
  sn("CompileTime", "len(CompileTime) + t"),
  # `std/typetraits` (imported by the magic suites): folded by semcheck
  sn("TypeTrait", "ord(supportsCopyMem(N_O)) + tupleLen((int, int8)) + t",
     top = "type N_O = object\n  x: int"),
]

const stdlibSnippets = @[
  sn("math.abs", "abs(t)"),
  sn("math.ceil", "int(ceil(float(t) / 2.0))"),
  sn("math.ceilDiv", "ceilDiv(t + 128, 3)"),
  sn("math.classify", "ord(classify(float(t)))"),
  sn("math.copySign", "int(copySign(2.0, float(t)))"),
  sn("math.euclDiv", "euclDiv(t, 3)"),
  sn("math.euclMod", "euclMod(t, 3)"),
  sn("math.floor", "int(floor(float(t) / 2.0))"),
  sn("math.floorDiv", "floorDiv(t, 3)"),
  sn("math.floorMod", "floorMod(t, 3)"),
  sn("math.isNaN", "ord(isNaN(float(t)))"),
  sn("math.isPowerOfTwo", "ord(isPowerOfTwo(t))"),
  sn("math.max", "int(max(float(t), float(u)))"),
  sn("math.min", "int(min(float(t), float(u)))"),
  sn("math.nextPowerOfTwo", "nextPowerOfTwo(t + 128)"),
  sn("math.round", "int(round(float(t) / 4.0))"),
  sn("math.sgn", "sgn(t)"),
  sn("math.signbit", "ord(signbit(float(t)))"),
  sn("math.sqrt", "int(sqrt(float(t + 128)))"),
  # the lowering's names for a float width change (`convertFloatWidth`):
  # float64 -> float32 narrows, float32 -> float64 widens
  sn("math.toFloat32", "int(float32(float(t) * 0.5))"),
  sn("math.toFloat64", "int(float64(float32(t)) * 0.5)"),
  sn("math.trunc", "int(trunc(float(t) / 3.0))"),
  sn("system.%%", "t %% 5"),
  sn("system.*%", "t *% u"),
  sn("system.+%", "t +% u"),
  sn("system.-%", "t -% u"),
  sn("system./%", "t /% 3"),
  sn("system.<%", "ord(t <% u)"),
  sn("system.<=%", "ord(t <=% u)"),
]

const definedSnippets = @[
  sn("add/signedNarrow", "int(a + b)", raises = true),
  sn("add/signedWide", "t * 72057594037927935 + u", raises = true),
  sn("sub/signedNarrow", "int(a - b)", raises = true),
  sn("sub/signedWide", "t * 72057594037927935 - u", raises = true),
  sn("mul/signedNarrow", "int(a * b)", raises = true),
  sn("mul/signedWide", "t * 72057594037927935 * u", raises = true),
  sn("div/zeroDivisorSigned", "t div u", raises = true),
  sn("mod/zeroDivisorSigned", "t mod u", raises = true),
  sn("div/zeroDivisorUnsigned", "int(uint8(t + 128) div uint8(u + 128))",
     raises = true),
  sn("mod/zeroDivisorUnsigned", "int(uint8(t + 128) mod uint8(u + 128))",
     raises = true),
  sn("div/lowByMinusOneNarrow", "(if b == 0: 0 else: int(a div b))",
     raises = true),
  sn("mod/lowByMinusOneNarrow", "(if b == 0: 0 else: int(a mod b))",
     raises = true),
  sn("div/lowByMinusOneWide",
     "(if u == 0: 0 else: (if t == -128: low(int) else: t) div u)",
     raises = true),
  sn("mod/lowByMinusOneWide",
     "(if u == 0: 0 else: (if t == -128: low(int) else: t) mod u)",
     raises = true),
  sn("convert/floatToInt", "int(float(t) * 1.5)"),
  # `(NI8)((NI64)f)`: the in-range side, inside both int64 and int8
  sn("convert/floatToIntVia", "int(int8(float(t) * 0.5))"),
  # a `{.noinit.}` local read before a write: the read rides the witness
  # (`ubIndeterminateRead`), so a path holding it is never a trusted verdict
  sn("read/uninitialised", "V_x * 0 + t", "var V_x {.noinit.}: int",
     undefined = "ubIndeterminateRead"),
  # an opaque (foreign) body: undefined under the whole-run gate. The
  # foreign value is any value to the walk, so the predicate does not rest
  # on it: a witness the model gives hits natively (INT-69)
  sn("call/opaqueBody", "t", post = "discard N_abs(cint(t))",
     top = "proc N_abs(x: cint): cint {.importc: \"abs\", header: \"<stdlib.h>\".}",
     undefined = "ubTailUnverified"),
  sn("index/unchecked", "V_s[u and 3]", "let V_s = @[t, 1, 2]", raises = true),
  sn("field/inactiveBranch", "V_v.n",
     "var V_v = N_V(k: true, n: t)\n  if u > 100: V_v = N_V(k: false, m: u)",
     top = "type N_V = object\n  case k: bool\n  of true: n: int\n  of false: m: int",
     raises = true),
  sn("conv/objDowncast", "N_D(V_r).x",
     "let V_r: N_B = (if t > 0: N_D(x: t) else: N_B(x: u))",
     top = "type\n  N_B = ref object of RootObj\n    x: int\n" &
           "  N_D = ref object of N_B",
     raises = true),
]

const typeClassSnippets = @[
  sn("alias", "N_f(t)", top = "type N_A = int\nproc N_f(x: N_A): int = x + 1"),
  sn("array", "N_f([t, u])", top = "proc N_f(x: array[2, int]): int = x[0] - x[1]"),
  # the by-value formal site, in the pin's shape (tsymex_0016_k2c_typeclass_c
  # `bvPtr`: a global `ptr` handed to a `pointer` formal the callee never reads)
  sn("pointer", "N_f(N_g) + ord(N_g == nil) + t", "N_g = nil",
     top = "var N_g: ptr int\nproc N_f(p: pointer): int =\n  N_g = nil\n  3"),
  sn("array/enumIndex", "N_f([t, u])",
     top = "type N_E = enum N_e0, N_e1\nproc N_f(x: array[N_E, int]): int = x[N_e1] - x[N_e0]"),
  sn("bool", "N_f(t > u)", top = "proc N_f(x: bool): int = (if x: 3 else: 5)"),
  sn("char", "N_f(chr(t + 128))", top = "proc N_f(x: char): int = ord(x) - 1"),
  sn("distinct", "N_f(N_D(t))",
     top = "type N_D = distinct int\nproc N_f(x: N_D): int = int(x) * 2"),
  sn("enum", "N_f(N_E(t and 1))",
     top = "type N_E = enum N_e0, N_e1\nproc N_f(x: N_E): int = ord(x) + 4"),
  sn("float", "N_f(float(t))", top = "proc N_f(x: float): int = int(x / 2.0)"),
  sn("float32", "N_f(float32(t))", top = "proc N_f(x: float32): int = int(x * 2'f32)"),
  sn("float64", "N_f(float64(t))", top = "proc N_f(x: float64): int = int(x * 3.0)"),
  sn("genericInst", "N_f(N_G[int](v: t))",
     top = "type N_G[T] = object\n  v: T\nproc N_f(x: N_G[int]): int = x.v + 1"),
  sn("int", "N_f(t)", top = "proc N_f(x: int): int = x - 2"),
  sn("int8", "N_f(a)", top = "proc N_f(x: int8): int = int(x) + 2"),
  sn("int16", "N_f(int16(t))", top = "proc N_f(x: int16): int = int(x * 3)"),
  sn("int32", "N_f(int32(t))", top = "proc N_f(x: int32): int = int(x * 5)"),
  sn("int64", "N_f(int64(t))", top = "proc N_f(x: int64): int = int(x * 7)"),
  sn("uint", "N_f(uint(t + 128))", top = "proc N_f(x: uint): int = int(x div 2)"),
  sn("uint8", "N_f(uint8(t + 128))", top = "proc N_f(x: uint8): int = int(x + 1)"),
  sn("uint16", "N_f(uint16(t + 128))", top = "proc N_f(x: uint16): int = int(x * 3)"),
  sn("uint32", "N_f(uint32(t + 128))", top = "proc N_f(x: uint32): int = int(x * 5)"),
  sn("uint64", "N_f(uint64(t + 128))", top = "proc N_f(x: uint64): int = int(x div 3)"),
  sn("object", "N_f(N_O(x: t, y: u))",
     top = "type N_O = object\n  x, y: int\nproc N_f(o: N_O): int = o.x - o.y"),
  sn("openArray", "N_f([t, u, 1])",
     top = "proc N_f(xs: openArray[int]): int = xs[0] + xs.len"),
  sn("proc", "N_f(N_h, t)",
     top = "proc N_h(x: int): int = x * 2\n" &
           "proc N_f(p: proc (x: int): int {.nimcall.}; v: int): int = p(v)"),
  sn("ptr", "N_f(addr V_x)", "var V_x = t",
     top = "proc N_f(p: ptr int): int = p[] + 1"),
  sn("range", "N_f(range[0 .. 255](t + 128))",
     top = "proc N_f(x: range[0 .. 255]): int = int(x) - 1"),
  sn("ref", "N_f(N_R(x: t))",
     top = "type N_R = ref object\n  x: int\nproc N_f(r: N_R): int = r.x * 2"),
  sn("sequence", "N_f(@[t, u])", top = "proc N_f(s: seq[int]): int = s[1] + s.len"),
  sn("set", "N_f({a, b})", top = "proc N_f(s: set[int8]): int = card(s)"),
  sn("string", "N_f($t)", top = "proc N_f(s: string): int = s.len"),
  sn("tuple", "N_f((t, u))", top = "proc N_f(x: (int, int)): int = x[0] * x[1]"),
  sn("var", "V_x", "var V_x = t\n  N_f(V_x)", top = "proc N_f(x: var int) = x = x + 3"),
  # the row is the by-value formal site only (a cstring parameter of the
  # SUT, a `len` of one or a conversion to one declines): the shape
  # tsymex_0016_k2c_typeclass_c pins, a global built from literals and handed
  # to a callee that compares it
  sn("cstring", "N_f(N_g)", "N_g = (if t > 3: \"abc\" else: \"x\")",
     top = "var N_g: cstring\n" &
           "proc N_f(c: cstring): int = (if c == \"abc\": 3 else: 1)"),
  sn("variant/omittedField/array", "V_v.n + V_v.w[1]",
     "let V_v = N_V(k: true, n: t)",
     top = "type N_V = object\n  case k: bool\n  of true:\n    n: int\n" &
           "    w: array[2, int]\n  of false: m: int"),
  sn("variant/omittedField/distinct", "V_v.n + int(V_v.w)",
     "let V_v = N_V(k: true, n: t)",
     top = "type\n  N_D = distinct int\n  N_V = object\n    case k: bool\n" &
           "    of true:\n      n: int\n      w: N_D\n    of false: m: int"),
  sn("variant/omittedField/tuple", "V_v.n + V_v.w[1]",
     "let V_v = N_V(k: true, n: t)",
     top = "type N_V = object\n  case k: bool\n  of true:\n    n: int\n" &
           "    w: (int, int)\n  of false: m: int"),
]

func fieldDefault(kind, ty, read: string; top = ""): Snippet =
  sn("fieldDefault/" & kind, "V_o.n + " & read, "let V_o = N_O(n: t)",
     top = top & "type N_O = object\n  n: int\n  w: " & ty)

func letCursor(kind, ty, init, read: string; top = ""): Snippet =
  sn("letCursor/" & kind, read, "var V_x: " & ty & " = " & init &
     "\n  let V_c = V_x", top = top)

const typeOpSnippets = @[
  fieldDefault("array", "array[2, int]", "V_o.w[1]"),
  fieldDefault("bitSet", "set[int8]", "card(V_o.w)"),
  fieldDefault("bool", "bool", "ord(V_o.w)"),
  fieldDefault("distinct", "N_D", "int(V_o.w)", "type N_D = distinct int\n"),
  fieldDefault("float32", "float32", "int(V_o.w)"),
  fieldDefault("float64", "float64", "int(V_o.w)"),
  fieldDefault("int", "int", "V_o.w"),
  fieldDefault("ptr", "ptr int", "ord(V_o.w == nil)"),
  fieldDefault("ref", "ref int", "ord(V_o.w == nil)"),
  fieldDefault("seq", "seq[int]", "V_o.w.len"),
  fieldDefault("set", "set[char]", "card(V_o.w)"),
  fieldDefault("string", "string", "V_o.w.len"),
  fieldDefault("tuple", "(int, int)", "V_o.w[1]"),
  fieldDefault("variant", "N_V", "V_o.w.m",
     "type N_V = object\n  case k: bool\n  of false: m: int\n  of true: z: int\n"),
  letCursor("array", "array[2, int]", "[t, u]", "V_c[0] - V_c[1]"),
  letCursor("bitSet", "set[int8]", "{a, b}", "card(V_c)"),
  letCursor("bool", "bool", "t > u", "ord(V_c)"),
  letCursor("distinct", "N_D", "N_D(t)", "int(V_c)", "type N_D = distinct int"),
  letCursor("float32", "float32", "float32(t)", "int(V_c)"),
  letCursor("float64", "float64", "float64(t)", "int(V_c)"),
  letCursor("int", "int", "t", "V_c"),
  letCursor("ptr", "ptr int", "nil", "ord(V_c == nil) + t"),
  letCursor("ref", "N_R", "N_R(x: t)", "V_c.x", "type N_R = ref object\n  x: int"),
  letCursor("seq", "seq[int]", "@[t, u]", "V_c[1] + V_c.len"),
  letCursor("set", "set[char]", "{chr(t + 128)}", "card(V_c)"),
  letCursor("string", "string", "$t", "V_c.len"),
  letCursor("tuple", "(int, int)", "(t, u)", "V_c[0] + V_c[1]"),
  letCursor("variant", "N_V", "N_V(k: false, m: t)", "V_c.m",
     "type N_V = object\n  case k: bool\n  of false: m: int\n  of true: z: int"),
  fieldDefault("table", "Table[int, int]", "V_o.w.len"),
  fieldDefault("multiVariant", "N_M", "V_o.w.m + V_o.w.p",
     "type N_M = object\n  case k: bool\n  of false: m: int\n  of true: z: int\n" &
     "  case j: bool\n  of false: p: int\n  of true: q: int\n"),
  sn("letCursor/table", "V_c.len + V_c[t]",
     "var V_x = initTable[int, int]()\n  V_x[t] = u\n  let V_c = V_x"),
  letCursor("multiVariant", "N_M", "N_M(k: false, m: t, j: true, q: u)",
     "V_c.m + V_c.q", "type N_M = object\n  case k: bool\n  of false: m: int\n  of true: z: int\n" &
     "  case j: bool\n  of false: p: int\n  of true: q: int\n"),
  # a placeholder sort's handle is copied: a closure local is the `__closure`
  # sort (a `pointer` holds a `ptr`'s address, not a placeholder, INT-65)
  sn("letCursor/uninterp", "V_c(u)",
     "let V_f = proc (x: int): int = x + t\n  let V_c = V_f"),
]

func routinePragma(p: string; prag = ""): Snippet =
  let pr = if prag.len > 0: prag else: p
  sn("routine/" & p, "N_f(t)",
     top = "proc N_f(x: int): int {." & pr & ".} = x * 2 + 1")

func pushedPragma(p, prag: string): Snippet =
  ## A routine pragma Nim takes only through `push` (a check or message
  ## switch): pushed around the routine.
  sn("routine/" & p, "N_f(t)",
     top = "{.push " & prag & ".}\nproc N_f(x: int): int = x * 2 + 1\n{.pop.}")

func typePragma(p, decl, read: string): Snippet =
  sn("type/" & p, read, top = decl)

func procTypePragma(p: string; impl = "-"; prag = ""): Snippet =
  ## A proc type carrying the pragma, a routine bound to a local of it and
  ## called; `impl` is the routine's own pragma ("-": the same one).
  let pr = if prag.len > 0: prag else: p
  let im = if impl == "-": pr else: impl
  sn("type/" & p, "(let p: N_P = N_h; p(t))",
     top = "type N_P = proc (x: int): int {." & pr & ".}\n" &
           "proc N_h(x: int): int" & (if im.len > 0: " {." & im & ".}" else: "") &
           " = x + 1")

func localPragma(key, name, decl, read: string): Snippet =
  ## A pragma word Nim rejects in the row's place reaches it only as a custom
  ## pragma of that name: declared in the SUT, so it shadows the word for
  ## this fragment alone.
  sn(key, read, "template " & name & "() {.pragma.}\n  " & decl)

const pragmaSnippets = @[
  routinePragma("inline"), routinePragma("noinline"), routinePragma("nimcall"),
  routinePragma("cdecl"), routinePragma("stdcall"), routinePragma("fastcall"),
  routinePragma("safecall"), routinePragma("syscall"), routinePragma("noconv"),
  routinePragma("gcsafe"), routinePragma("noSideEffect"),
  routinePragma("raises", "raises: []"), routinePragma("tags", "tags: []"),
  routinePragma("forbids", "forbids: []"),
  routinePragma("used"), routinePragma("deprecated"),
  routinePragma("discardable"), routinePragma("exportc", "exportc: \"N_f\""),
  pushedPragma("boundChecks", "boundChecks: on"),
  pushedPragma("overflowChecks", "overflowChecks: on"),
  pushedPragma("rangeChecks", "rangeChecks: on"),
  pushedPragma("checks", "checks: on"),
  routinePragma("stackTrace", "stackTrace: on"),
  routinePragma("lineTrace", "lineTrace: on"),
  pushedPragma("hints", "hints: off"),
  pushedPragma("warnings", "warnings: off"),
  pushedPragma("optimization", "optimization: speed"),
  sn("routine/closure", "V_f(u)",
     "proc V_f(x: int): int {.closure.} = x * 2 + t"),
  routinePragma("locks", "locks: 0"),
  routinePragma("noinit"),
  sn("routine/borrow", "int(N_D(t) + N_D(u))",
     top = "type N_D = distinct int\nproc `+`(x, y: N_D): N_D {.borrow.}"),
  sn("routine/compileTime", "N_c + t",
     top = "proc N_f(x: int): int {.compileTime.} = x * 2\nconst N_c = N_f(3)"),
  sn("routine/base", "N_m(V_r)", "let V_r = N_B(x: t)",
     top = "type N_B = ref object of RootObj\n  x: int\n" &
           "method N_m(b: N_B): int {.base.} = b.x + 1"),
  typePragma("pure", "type N_E {.pure.} = enum e0, e1", "ord(N_E(t and 1))"),
  typePragma("acyclic", "type N_R {.acyclic.} = ref object\n  x: int",
             "N_R(x: t).x"),
  typePragma("final", "type N_O {.final.} = object of RootObj\n  x: int",
             "N_O(x: t).x"),
  typePragma("inheritable", "type N_O {.inheritable.} = object\n  x: int",
             "N_O(x: t).x"),
  typePragma("requiresInit", "type N_O {.requiresInit.} = object\n  x: int",
             "N_O(x: t).x"),
  typePragma("size", "type N_E {.size: 4.} = enum N_e0, N_e1",
             "ord(N_E(t and 1)) + sizeof(N_E)"),
  typePragma("shallow", "type N_O {.shallow.} = object\n  s: seq[int]",
             "N_O(s: @[t]).s[0]"),
  typePragma("deprecated", "type N_O {.deprecated.} = object\n  x: int",
             "N_O(x: t).x"),
  typePragma("exportc", "type N_O {.exportc: \"N_O\".} = object\n  x: int",
             "N_O(x: t).x"),
  typePragma("align", "type N_O = object\n  x {.align: 16.}: int", "N_O(x: t).x"),
  typePragma("nimcall", "type N_P = proc (x: int): int {.nimcall.}\n" &
             "proc N_h(x: int): int = x + 1",
             "(let p: N_P = N_h; p(t))"),
  sn("field/cursor", "V_o.c.x", "let V_r = N_R(x: t)\n  let V_o = N_O(c: V_r)",
     top = "type\n  N_R = ref object\n    x: int\n  N_O = object\n    c {.cursor.}: N_R"),
  sn("field/deprecated", "N_O(x: t).x",
     top = "type N_O = object\n  x {.deprecated.}: int"),
  sn("field/exportc", "N_O(x: t).x",
     top = "type N_O = object\n  x {.exportc: \"xx\".}: int"),
  sn("field/requiresInit", "N_O(x: t).x",
     top = "type N_O = object\n  x {.requiresInit.}: int"),
  sn("field/used", "N_O(x: t).x", top = "type N_O = object\n  x {.used.}: int"),
  sn("local/used", "V_x", "let V_x {.used.} = t"),
  sn("local/noinit", "V_x", "var V_x {.noinit.}: int\n  V_x = t"),
  # --- the rows outside the first table ---------------------------------------
  sn("local/global", "V_g", "var V_g {.global.} = 0\n  V_g = t"),
  # template hygiene: the `let` is the SUT's local once the template expands
  sn("local/inject", "N_t(t)",
     top = "template N_t(v: int): int =\n  let N_y {.inject.} = v\n  N_y + 1"),
  sn("local/gensym", "N_t(t)",
     top = "template N_t(v: int): int =\n  let N_y {.gensym.} = v\n  N_y + 1"),
  sn("param/inject", "N_f(t)", top = "proc N_f(x {.inject.}: int): int = x * 2 + 1"),
  # Nim rejects `used` on a formal; the name reaches one only as a custom
  # pragma, declared in the SUT so no other row sees it
  localPragma("param/used", "used",
              "proc V_f(x {.used.}: int): int = x * 2 + 1", "V_f(t)"),
  routinePragma("sideEffect"), routinePragma("procvar"),
  routinePragma("compilerproc"), routinePragma("core"),
  routinePragma("nonReloadable"), routinePragma("enforceNoRaises"),
  routinePragma("systemRaisesDefect"), routinePragma("quirky"),
  routinePragma("nosinks"), routinePragma("thread"),
  routinePragma("requires", "requires: x > -1000"),
  routinePragma("ensures", "ensures: result > -10000"),
  routinePragma("extern", "extern: \"N_fx\""),
  sn("routine/effectsOf", "N_f(t, N_h)",
     top = "proc N_h(y: int): int = y + 1\n" &
           "proc N_f(x: int; p: proc (y: int): int {.nimcall.}): int " &
           "{.effectsOf: p.} = p(x) * 2"),
  sn("routine/dirty", "N_f(t)",
     top = "template N_f(x: int): int {.dirty.} = x * 2 + 1"),
  sn("routine/callsite", "N_f(t)",
     top = "template N_f(x: int): int {.callsite.} = x * 2 + 1"),
  pushedPragma("assertions", "assertions: on"),
  pushedPragma("floatChecks", "floatChecks: on"),
  pushedPragma("nanChecks", "nanChecks: on"),
  pushedPragma("infChecks", "infChecks: on"),
  pushedPragma("fieldChecks", "fieldChecks: on"),
  pushedPragma("objChecks", "objChecks: on"),
  pushedPragma("nilChecks", "nilChecks: on"),
  pushedPragma("profiler", "profiler: off"),
  pushedPragma("debugger", "debugger: off"),
  sn("routine/magic", "N_plus(t, u)",
     top = "proc N_plus(x, y: int): int {.magic: \"AddI\", noSideEffect.}"),
  # a foreign routine is the opaque-call arm (INT-68): its value is any
  # value to the walk and the run carries `ubTailUnverified`, so the
  # predicate does not rest on it (the `call/opaqueBody` row's shape)
  sn("routine/importc", "t", post = "discard N_abs(cint(t))",
     top = "proc N_abs(x: cint): cint {.importc: \"abs\", header: \"<stdlib.h>\".}",
     undefined = "ubTailUnverified"),
  sn("routine/header", "t", post = "discard N_ll(clonglong(t))",
     top = "proc N_ll(x: clonglong): clonglong {.importc: \"llabs\", " &
           "header: \"<stdlib.h>\".}", undefined = "ubTailUnverified"),
  # `labs` is declared by the `<stdlib.h>` the `abs` beside it includes
  sn("routine/nodecl", "t",
     post = "discard N_l(clong(t))\n  discard N_abs(cint(u))",
     undefined = "ubTailUnverified",
     top = "proc N_abs(x: cint): cint {.importc: \"abs\", header: \"<stdlib.h>\".}\n" &
           "proc N_l(x: clong): clong {.importc: \"labs\", nodecl.}"),
  sn("routine/dynlib", "t", post = "discard N_abs(cint(t))",
     top = "proc N_abs(x: cint): cint {.importc: \"abs\", " &
           "dynlib: \"(msvcrt.dll|libc.so.6)\".}", undefined = "ubTailUnverified"),
  # a call on a path no input reaches (t <= 127)
  sn("routine/noreturn", "t", "if t > 126 and t < 0: N_die()",
     top = "proc N_die() {.noreturn.} = quit(3)"),
  # a call to it does not compile: the program declares it and reaches none
  sn("routine/error", "t", top = "proc N_f(x: int): int {.error.}"),
  # names the walk meets as stdlib's pragma aliases and macro pragmas: a
  # custom pragma of the same name (`s0016_k8b_pragmas`)
  routinePragma("benign"), routinePragma("rtl"), routinePragma("rtlFunc"),
  routinePragma("inl"), routinePragma("compilerRtl"),
  routinePragma("noWeirdTarget"), routinePragma("noNimJs"),
  routinePragma("nimhcr"), routinePragma("hcrInline"),
  routinePragma("multisync"), routinePragma("since"), routinePragma("async"),
  routinePragma("parseRaises"), routinePragma("parseFormatRaises"),
  routinePragma("auditDelete"), routinePragma("evalonce"),
  routinePragma("myShallow"), routinePragma("epollPacked"),
  routinePragma("outParamsAt"), routinePragma("importIconv"),
  routinePragma("lcrypto"), routinePragma("boehmGC"), routinePragma("gcMark"),
  routinePragma("errorNoReturn"), routinePragma("nimbaseH"),
  routinePragma("operator"), routinePragma("tlsEmulation"),
  routinePragma("exportJs"),
  # pragma words Nim rejects on a routine: a custom pragma declared in the SUT
  localPragma("routine/fatal", "fatal",
              "proc V_f(x: int): int {.fatal.} = x * 2 + 1", "V_f(t)"),
  localPragma("routine/executeOnReload", "executeOnReload",
              "proc V_f(x: int): int {.executeOnReload.} = x * 2 + 1", "V_f(t)"),
  localPragma("routine/sendable", "sendable",
              "proc V_f(x: int): int {.sendable.} = x * 2 + 1", "V_f(t)"),
  # the type list: a proc type's effect and calling-convention pragmas
  procTypePragma("gcsafe"), procTypePragma("noSideEffect"),
  procTypePragma("cdecl"), procTypePragma("stdcall"),
  procTypePragma("fastcall"), procTypePragma("safecall"),
  procTypePragma("syscall"), procTypePragma("noconv"),
  procTypePragma("inline"), procTypePragma("closure", ""),
  procTypePragma("benign", ""), procTypePragma("raises", "", "raises: []"),
  procTypePragma("tags", "", "tags: []"),
  procTypePragma("forbids", "", "forbids: []"),
  procTypePragma("locks", "", "locks: 0"),
  # Nim rejects `effectsOf` on a proc type it declares; a routine's own type
  # carries it to the local it is bound to
  sn("type/effectsOf", "V_p(t, N_g)", "let V_p = N_h",
     top = "proc N_g(y: int): int = y + 1\n" &
           "proc N_h(x: int; p: proc (y: int): int {.nimcall.}): int " &
           "{.effectsOf: p.} = p(x)"),
  # `nosinks` and `dynlib` are rejected on a type; a custom pragma of the same
  # name is local to `s0016_k8b_pragmas` (an exported one would shadow the
  # routine pragma `dynlib`), which declares the types (a type section in a
  # routine declines, `feUnsupportedStmtKind`)
  sn("type/nosinks", "V_p(t)", "let V_p: K8bNoSinksP = N_h",
     top = "proc N_h(x: int): int = x + 1"),
  typePragma("sendable", "type N_O {.sendable.} = object\n  x: int", "N_O(x: t).x"),
  typePragma("myShallow", "type N_O {.myShallow.} = object\n  x: int",
             "N_O(x: t).x"),
  typePragma("extern", "type N_O {.extern: \"N_Ox\".} = object\n  x: int",
             "N_O(x: t).x"),
  typePragma("borrow", "type\n  N_O = object\n    x: int\n  N_D {.borrow: `.`.} = distinct N_O",
             "N_D(N_O(x: t)).x"),
  sn("type/dynlib", "K8bDynO(x: t).x"),
  # a foreign scalar: `system.cint`'s form
  typePragma("importc", "type N_I {.importc: \"int\", nodecl.} = int32",
             "int(N_I(t) + 1)"),
  typePragma("nodecl", "type N_I {.importc: \"long long\", nodecl.} = int64",
             "int(N_I(t) - 1)"),
  typePragma("header", "type N_I {.importc: \"int32_t\", header: \"<stdint.h>\".} = int32",
             "int(N_I(t) * 2)"),
  typePragma("nimbaseH", "type N_I {.importc: \"NI\", nimbaseH.} = int",
             "int(N_I(t) + 1)"),
  typePragma("incompleteStruct",
             "type N_S {.importc: \"div_t\", header: \"<stdlib.h>\", " &
             "incompleteStruct.} = object\n  quot, rem: cint",
             "int(N_S(quot: cint(t)).quot)"),
  typePragma("completeStruct",
             "type N_S {.importc: \"div_t\", header: \"<stdlib.h>\", " &
             "completeStruct.} = object\n  quot, rem: cint",
             "int(N_S(quot: cint(t)).quot)"),
  # rows only a backend some legs lack can carry: each runs in its own suite
  # (`ownRows`)
  sn("routine/importcpp", "int(N_abs(cint(t)))",
     top = "proc N_abs(x: cint): cint {.importcpp: \"abs(@)\", header: \"<cstdlib>\".}"),
  routinePragma("exportcpp", "exportcpp: \"N_fx\""),
  typePragma("importcpp", "type N_I {.importcpp: \"int\", nodecl.} = int32",
             "int(N_I(t) + 1)"),
  sn("routine/importjs", "int(N_abs(cint(t)))",
     top = "proc N_abs(x: cint): cint {.importjs: \"Math.abs(#)\".}"),
  typePragma("importjs", "type N_I {.importjs: \"Number\".} = int32",
             "int(N_I(t) + 1)"),
  sn("routine/importObjC", "int(N_abs(cint(t)))",
     top = "proc N_abs(x: cint): cint {.importObjC: \"abs\", nodecl.}"),
]

# The build axis (K5b's cells, `buildprofile.buildCells`, and the verified
# libpcre builds, `pcre_engine.pcreLibs`). Each fragment is ordinary code whose
# verdict the switch could move: the heap under a memory model or allocator,
# a caught raise under setjmp exceptions, arithmetic under `release` and
# `fwrapv`, and the in-range side of each disabled check (narrowing, an
# index, a subtype conversion, a field of the active branch).
const
  pcreFrag = sn("", "ord(V_s.match(re\"[a-c]\"))",
                "var V_s = \"x\"\n  V_s[0] = chr(t + 128)")
  refTop = "type N_R = ref object\n  x: int"

func pcreSnippet(key: string): Snippet =
  ## A regex call: the row is the libpcre the binary loaded, so the build
  ## suite runs it on every leg and keeps the record of the host's row only.
  result = pcreFrag
  result.key = key

const buildSnippets = @[
  sn("mm=arc", "V_r.x + t", "let V_r = N_R(x: t)\n  let V_q = V_r\n  V_q.x = u",
     top = refTop, cfg = "--mm:arc"),
  sn("mm=atomicArc", "V_a.x - V_b.x",
     "var V_a, V_b: N_R\n  new(V_a)\n  new(V_b)\n  V_a.x = t\n  V_b.x = u",
     top = refTop, cfg = "--mm:atomicArc"),
  sn("useMalloc", "V_s[1] + V_s.len", "var V_s = @[t, u]\n  V_s.add 3",
     cfg = "-d:useMalloc"),
  sn("exceptions/setjmp", "V_x + t",
     "var V_x = 0\n  try:\n    if t > 3: raise newException(ValueError, \"e\")\n" &
     "    V_x = 1\n  except ValueError:\n    V_x = 2",
     cfg = "switch(\"exceptions\", \"setjmp\")"),
  sn("release", "t * u - 3", cfg = "-d:release"),
  sn("fwrapv", "t * 7 + u", cfg = "-d:nelliFwrapv"),
  sn("rangeChecks=off", "int(int8(t + u))", cfg = "--rangeChecks:off"),
  sn("boundChecks=off", "V_s[t and 1]", "let V_s = @[t, u]",
     cfg = "--boundChecks:off"),
  sn("objChecks=off", "N_D(V_b).y + V_b.x", "let V_b: N_B = N_D(x: t, y: u)",
     top = "type\n  N_B = ref object of RootObj\n    x: int\n" &
           "  N_D = ref object of N_B\n    y: int",
     cfg = "--objChecks:off"),
  sn("fieldChecks=off", "(if V_v.k: V_v.x else: V_v.y)",
     "let V_v = (if t > 0: N_V(k: true, x: t) else: N_V(k: false, y: u))",
     top = "type N_V = object\n  case k: bool\n  of true: x: int\n  of false: y: int",
     cfg = "--fieldChecks:off"),
  pcreSnippet("8.45 2021-06-15|interp"),
  pcreSnippet("8.37 2015-04-28|jit"),
  pcreSnippet("8.37 2015-04-28|interp"),
]

# The read-only axis (`readonlyaxes.readOnlyAxis`): each modelled shape a K6
# route proves read-only, in the K6 corpus's own form. `lent/`: the body of a
# `for` over a global seq (`mayWriteRoot`); `hookcopy/`, `hookstore/`: a user
# `=copy` that is the plain copy (`routeHookCopies`, `routeStoresThroughDeref`);
# `ptrformal/`: a callee's `ptr` formal (`ptrUsesStayLocal`); `viewwhole/`: a
# callee given a `var` element and the `Table` it lives in (`bindsViewWhole`).
func lentShape(key, body: string; top = ""): Snippet =
  sn(key, "V_s", "N_gs = @[t, u]\n  var V_s = 0\n  for V_x in N_gs:\n" & body,
     top = "var N_gs: seq[int]" & (if top.len > 0: "\n" & top else: ""))

func hookShape(key, hook: string): Snippet =
  sn(key, "V_y.v", "var V_x = N_C(v: t)\n  var V_y = V_x\n  V_x.v = u",
     top = "type N_C = object\n  v: int\nproc N_pure(x, y: int): int = x + y\n" &
           "proc `=copy`(a: var N_C; b: N_C) =\n" & hook)

func viewShape(key, hold: string): Snippet =
  sn(key, "V_r",
     "var V_t = initTable[string, int]()\n  V_t[\"a\"] = t\n  var V_r = 0\n" &
     "  for V_k, V_v in V_t.mpairs:\n    V_r = N_hold(V_v, V_t, V_k)",
     top = "proc N_hold(v: var int; t: Table[string, int]; k: string): int =\n" &
           hold)

const readOnlySnippets = @[
  lentShape("lent/walked-pure", "    V_s = V_s + N_pure(V_x, 1)",
            "proc N_pure(x, y: int): int = x + y"),
  lentShape("lent/local-work",
            "    var V_w = V_x\n    if V_w < 0: V_w = -V_w\n    V_s = V_s + V_w"),
  lentShape("lent/global-read", "    V_s = V_s + V_x + N_gs.len"),
  lentShape("lent/pragma-block", "    doAssert V_x < 1000\n    V_s = V_s + V_x"),
  hookShape("hookcopy/plain", "  a.v = b.v"),
  hookShape("hookcopy/local-work",
            "  var w = b.v + 1\n  if w > 3: w = w - 1\n  a.v = b.v\n  discard w"),
  hookShape("hookcopy/walked-pure", "  discard N_pure(b.v, 1)\n  a.v = b.v"),
  hookShape("hookstore/plain", "  a.v = b.v"),
  hookShape("hookstore/local-work",
            "  var w = N_pure(b.v, 1)\n  if w > 3: w = w - 1\n  a.v = b.v\n  discard w"),
  sn("ptrformal/local", "V_x", "var V_x = 1\n  N_set(addr V_x, addr V_x, t)",
     top = "proc N_set(p, q: ptr int; v: int) =\n  p[] = v\n  q[] = 3"),
  sn("ptrformal/global-store", "V_x",
     "var V_x = 1\n  N_keep(addr V_x)\n  N_gq[] = t",
     top = "var N_gq: ptr int\nproc N_keep(p: ptr int) = N_gq = p"),
  viewShape("viewwhole/tuple-copy",
            "  let c = (a: t, b: 1)\n  v = 77\n  c.a[k]"),
  viewShape("viewwhole/scalar-read",
            "  let c = t.getOrDefault(\"zz\")\n  v = 77\n  t[k] + c"),
]

const axisSnippets*: array[AxisScope, seq[Snippet]] = [
  axTypeClass: typeClassSnippets,
  axTypeOp: typeOpSnippets,
  axPragma: pragmaSnippets,
  axMagic: magicSnippets,
  axStdlibBody: stdlibSnippets,
  axBuild: buildSnippets,
  axReadOnly: readOnlySnippets,
  axDefinedness: definedSnippets]

# --- the blocked rows ------------------------------------------------------------
#
# A row whose fragment an OPEN worklist defect breaks (the walk hangs, declines
# a decidable query, or costs more than a suite can carry) is left out of the
# axis stream until the defect closes: a packed program holding it cannot
# pass, and it would take its neighbours' rows down with it. A blocked row is
# NOT exercised: the axis figure counts it against the axis like any row with
# no fragment. Each entry names its worklist row, and `tsymex_0016_k8b_axes`
# fails (`s0016_k8b_axes.blockedProblems`) once that row leaves `open`, so a
# fixed defect's rows must be readmitted (the entry deleted) the day it lands.

type Blocked* = object
  axis*: AxisScope
  key*: string    ## the axis row (fragment key)
  row*: string    ## the open worklist row that breaks it
  why*: string    ## what the fragment does under that defect

func bk(axis: AxisScope; key, row, why: string): Blocked =
  Blocked(axis: axis, key: key, row: row, why: why)

const
  blockedRows*: seq[Blocked] = @[]
    ## Empty. INT-57 (walker 428) readmitted its twelve (magic `IntToStr`,
    ## `Int64ToStr`, `BoolToStr`, `EqStr`, `LeStr`, `LtStr`, `LengthStr`,
    ## `ConStrStr`, `AppendStrStr`; typeclass `string`; typeop
    ## `letCursor/string`, `fieldDefault/string`); readmitting them moved
    ## `Slice` onto a target its fragment cannot reach, INT-74, which
    ## walker 431 readmitted. A new entry is `bk(axis, key, row, why)`.

func isBlocked*(axis: AxisScope; key: string): bool =
  for b in blockedRows:
    if b.axis == axis and b.key == key: return true

# --- the rows with a suite of their own -------------------------------------------
#
# A row only some legs can decide (a backend's foreign-code pragma, a table the
# toolchain writes) is left out of the axis stream and runs in a suite of its
# own (one of the axis's `axisFiles`), which applies on the legs that can build
# and decide it and writes one `skipped` record on the others, naming the leg
# that exercises it (`s0016_k8b_suite.ownAxisBatch`). Unlike a blocked row it
# is exercised wherever its suite applies.

type OwnRow* = object
  axis*: AxisScope
  key*: string
  suite*: string  ## the axis suite that runs it

func own(axis: AxisScope; key, suite: string): OwnRow =
  OwnRow(axis: axis, key: key, suite: suite)

const
  pragmaCppSuite* = "tsymex_0016_k8b_axes_pragma_cpp.nim"
  pragmaDispatchSuite* = "tsymex_0016_k8b_axes_pragma_dispatch.nim"
  pragmaForeignSuite* = "tsymex_0016_k8b_axes_pragma_foreign.nim"
  ownRows*: seq[OwnRow] = @[
    own(axPragma, "routine/importcpp", pragmaCppSuite),
    own(axPragma, "routine/exportcpp", pragmaCppSuite),
    own(axPragma, "type/importcpp", pragmaCppSuite),
    own(axPragma, "routine/base", pragmaDispatchSuite),
    own(axPragma, "routine/importjs", pragmaForeignSuite),
    own(axPragma, "type/importjs", pragmaForeignSuite),
    own(axPragma, "routine/importObjC", pragmaForeignSuite),
  ]

func ownSuite*(axis: AxisScope; key: string): string =
  ## The suite of its own the row runs in, or "" (the axis stream).
  for o in ownRows:
    if o.axis == axis and o.key == key: return o.suite
  ""

func inStream*(axis: AxisScope; key: string): bool =
  ## The row is packed by the axis stream: not blocked, no suite of its own.
  not isBlocked(axis, key) and ownSuite(axis, key).len == 0

func ownKeys*(axis: AxisScope; suite: string): seq[string] =
  ## The rows `suite` runs on its own, in table order.
  for s in axisSnippets[axis]:
    if ownSuite(axis, s.key) == suite: result.add s.key

func streamSnippets*(axis: AxisScope): seq[Snippet] =
  ## The axis's fragments the stream packs: every one not blocked and with no
  ## suite of its own.
  for s in axisSnippets[axis]:
    if inStream(axis, s.key): result.add s

func streamRows*(axis: AxisScope): int = streamSnippets(axis).len

func blockedReport*(axis: AxisScope): seq[string] =
  ## A suite's report of the rows it leaves out (they count as unexercised).
  for b in blockedRows:
    if b.axis == axis:
      result.add "k8b blocked (not exercised) " & scopePrefix[axis] & ":" &
        b.key & " until " & b.row

func snippetOf*(axis: AxisScope; key: string): Snippet =
  for s in axisSnippets[axis]:
    if s.key == key: return s
  raise newException(KeyError, "no fragment for " & scopePrefix[axis] & ":" & key)
