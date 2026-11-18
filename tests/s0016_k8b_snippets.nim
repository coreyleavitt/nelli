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

func sn(key, expr: string; pre = ""; top = ""; raises = false): Snippet =
  Snippet(key: key, expr: expr, pre: pre, top: top, raises: raises)

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
  # tsymex_0016_k2c_typeclass pins, a global built from literals and handed
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
]

const axisSnippets*: array[AxisScope, seq[Snippet]] = [
  axTypeClass: typeClassSnippets,
  axTypeOp: typeOpSnippets,
  axPragma: pragmaSnippets,
  axMagic: magicSnippets,
  axStdlibBody: stdlibSnippets,
  axBuild: @[],         # build rows are exercised by build-profile legs
  axReadOnly: @[],
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
  int74Why = "a slice of a concatenation over `$t`, indexed (`($t & \"ab\")[0 .. 1][0]`), beside the accumulator: the sequence solver does not decide the target's unsat query (15.5M units in 60 s); under the pin settings the stall backstop ends it at 600 s, `sxUnknown`"
  blockedRows*: seq[Blocked] = @[
    ## INT-57 (walker 428) readmitted its twelve (magic `IntToStr`,
    ## `Int64ToStr`, `BoolToStr`, `EqStr`, `LeStr`, `LtStr`, `LengthStr`,
    ## `ConStrStr`, `AppendStrStr`; typeclass `string`; typeop
    ## `letCursor/string`, `fieldDefault/string`). Readmitting them moved
    ## `Slice` onto a target its fragment cannot reach, which INT-74 is.
    bk(axMagic, "Slice", "INT-74", int74Why),
  ]

func isBlocked*(axis: AxisScope; key: string): bool =
  for b in blockedRows:
    if b.axis == axis and b.key == key: return true

func streamSnippets*(axis: AxisScope): seq[Snippet] =
  ## The axis's fragments the stream packs: every one not blocked.
  for s in axisSnippets[axis]:
    if not isBlocked(axis, s.key): result.add s

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
