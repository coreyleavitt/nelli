## RFC-0016 W3-z (M1): the `never` magic rows of the std/macros NimNode API
## and std/macrocache. A SUT's typed body cannot carry a NimNode, so the
## walker never reads these; each is `pinNever` with the native fact that the
## routine works at compile time (the VM evaluates it into a `const`, or a
## `typed` macro probes it and hands back a literal).
import std/[unittest, macros, macrocache]
import nelli/smt/admission
import nelli/smt/magic_rows
import ./s8cu_helpers

proc m1Fn(x: int): int = x
proc m1Gen[T](x: T): T = x

# --- evaluated by the VM in a const initialiser ------------------------------

const
  cStrToIdent = ident("abc").eqIdent("abc")
  cEqIdent = eqIdent(ident("aBc"), "a_bC") and not eqIdent(ident("abc"), "abd")
  cEqNode = (block:
    let a = newLit(1)
    a == a)
  cNLen = newCall(ident"f", newLit(1)).len == 2
  cNChild = (block:
    let n = newCall(ident"f", newLit(7))
    n[1].intVal == 7)
  cNSetChild = (block:
    let n = newCall(ident"f", newLit(7))
    n[1] = newLit(9)
    n[1].intVal == 9)
  cNAdd = (block:
    let n = newCall(ident"f")
    n.add newLit(1)
    n.len == 2)
  cNAddMultiple = (block:
    let n = newCall(ident"f")
    n.add [newLit(1), newLit(2)]
    n.len == 3)
  cNDel = (block:
    let n = newCall(ident"f", newLit(1), newLit(2))
    n.del(1)
    n.len == 2 and n[1].intVal == 2)
  cNKind = newLit(1).kind == nnkIntLit and newLit("s").kind == nnkStrLit
  cNIntVal = newLit(41).intVal == 41
  cNFloatVal = newLit(2.5).floatVal == 2.5
  cNStrVal = newLit("abc").strVal == "abc" and $newLit("abc") == "abc"
  cNIdent = ident("abc").ident == ident("abc").ident and $ident("abc") == "abc"
  cNSetIntVal = (block:
    let n = newLit(1)
    n.intVal = 5
    n.intVal == 5)
  cNSetFloatVal = (block:
    let n = newLit(1.5)
    n.floatVal = 2.5
    n.floatVal == 2.5)
  cNSetStrVal = (block:
    let n = newLit("a")
    n.strVal = "b"
    n.strVal == "b")
  cNSetIdent = (block:
    let n = ident("a")
    n.ident = ident("b").ident
    $n == "b")
  cNNewNimNode = newNimNode(nnkCall).kind == nnkCall
  cNCopyNimNode = (block:
    let n = newCall(ident"f", newLit(1))
    let c = copyNimNode(n)
    c.kind == nnkCall and c.len == 0)
  cNCopyNimTree = (block:
    let n = newCall(ident"f", newLit(1))
    let c = copyNimTree(n)
    c.len == 2 and c[1].intVal == 1)
  cNLineInfo = (block:
    let a = newLit(1)
    let b = newLit(2)
    b.copyLineInfo(a)
    let la = lineInfoObj(a)
    let lb = lineInfoObj(b)
    la.filename == lb.filename and la.line == lb.line and
      la.column == lb.column)
  cNodeId = (block:
    let n = newLit(1)
    nodeID(n) == nodeID(n))
  cParseExpr = parseExpr("1 + 2").kind == nnkInfix
  cParseStmt = parseStmt("let a = 1").kind in {nnkStmtList, nnkLetSection}
  cNHint = (block:
    hint("m1 probe hint")
    true)
  cNWarning = (block:
    warning("m1 probe warning")
    true)
  cNError = not compiles(static do: error("m1 probe"))

# --- std/macrocache, evaluated by the VM -------------------------------------

const
  m1Ctr = CacheCounter("m1.ctr")
  m1Seq = CacheSeq("m1.seq")
  m1Tab = CacheTable("m1.tab")

const
  cNccInc = (block:
    m1Ctr.inc(2)
    true)
  cNccValue = m1Ctr.value == 2
  cNcsAdd = (block:
    m1Seq.add newLit(10)
    true)
  cNcsIncl = (block:
    m1Seq.incl newLit(10)
    m1Seq.incl newLit(11)
    true)
  cNcsAt = m1Seq[0].intVal == 10
  cNcsLen = m1Seq.len >= 2
  cNctPut = (block:
    m1Tab["k"] = newLit(5)
    true)
  cNctGet = m1Tab["k"].intVal == 5
  cNctLen = m1Tab.len == 1
  cNctIter = (block:
    var n = 0
    for k, v in m1Tab:
      if k == "k" and v.intVal == 5: inc n
    n == 1)

# --- probed inside a typed macro ----------------------------------------------

template m1Templ(x: int): untyped = x + 1

macro probeTyped(f: typed; inst: typed; v: typed): untyped =
  ## One bool per row, in a fixed order the consts below index.
  var r: seq[bool]
  let impl = f.getImpl
  r.add impl.kind == nnkProcDef                              # 0 GetImpl
  r.add f.getImplTransformed.kind == nnkProcDef              # 1 GetImplTransf
  r.add f.symKind == nskProc                                 # 2 NSymKind
  r.add f.strVal == "m1Fn" and $f == "m1Fn"                  # 3 NStrVal (sym)
  r.add f.owner.symKind == nskModule                         # 4 SymOwner
  r.add v.getType.kind == nnkSym and v.typeKind == ntyInt    # 5 NGetType
  r.add v.getTypeInst.kind == nnkSym                         # 6 getTypeInst
  r.add bindSym("m1Fn").kind in {nnkSym, nnkClosedSymChoice, nnkOpenSymChoice}
                                                              # 7 NBindSym
  r.add isInstantiationOf(inst[0], bindSym("m1Gen"))         # 8 SymIsInst
  r.add genSym(nskLet, "t").kind == nnkSym                   # 9 NGenSym
  r.add f.signatureHash.len > 0                              # 10 NSigHash
  r.add getSize(v) == 8                                      # 11 NSizeOf
  r.add callsite().kind == nnkCall                           # 12 NCallSite
  r.add (quote do: 1 + 2).kind == nnkInfix                   # 13 QuoteAst
  r.add f.symbol == f.symbol                                 # 14 NSymbol
  r.add sameType(v, v)                                       # 15 SameNodeType
  r.add (block:                                              # 16 NSetSymbol
    let c = copyNimNode(f)
    c.symbol = f.symbol
    c.symKind == nskProc)
  r.add (getAst(m1Templ(3))).kind != nnkNone                 # 17 ExpandToAst
  result = newLit(r)

const m1Typed = probeTyped(m1Fn, m1Gen(3), 5)

proc isNeverRow(row: string): bool =
  for c in magicAxis.cells:
    if c.cell.key == row: return not c.admitted and c.intent == iNever

template never(row: static string; holds: bool; native: string) =
  test row:
    check isNeverRow(row)
    pinNever(cellKey(axMagic, row), holds, native)

suite "M1: std/macros, evaluated by the VM":
  never("StrToIdent", cStrToIdent, "ident(\"abc\") builds an identifier node")
  never("EqIdent", cEqIdent, "eqIdent compares identifiers style-insensitively")
  never("EqNimrodNode", cEqNode, "== on NimNode compares node identity")
  never("NLen", cNLen, "a call node's len counts its children")
  never("NChild", cNChild, "[] reads a child node")
  never("NSetChild", cNSetChild, "[]= replaces a child node")
  never("NAdd", cNAdd, "add appends a child")
  never("NAddMultiple", cNAddMultiple, "add appends several children")
  never("NDel", cNDel, "del removes a child")
  never("NKind", cNKind, "kind reads the node kind")
  never("NIntVal", cNIntVal, "intVal reads an integer literal")
  never("NFloatVal", cNFloatVal, "floatVal reads a float literal")
  never("NStrVal", cNStrVal and m1Typed[3],
        "strVal and $ read a string literal and a symbol name")
  never("NIdent", cNIdent, "an identifier node renders its name")
  never("NSetIntVal", cNSetIntVal, "intVal= rewrites an integer literal")
  never("NSetFloatVal", cNSetFloatVal, "floatVal= rewrites a float literal")
  never("NSetStrVal", cNSetStrVal, "strVal= rewrites a string literal")
  never("NSetIdent", cNSetIdent, "an identifier node can be renamed")
  never("NNewNimNode", cNNewNimNode, "newNimNode builds an empty node of a kind")
  never("NCopyNimNode", cNCopyNimNode, "copyNimNode copies the node without children")
  never("NCopyNimTree", cNCopyNimTree, "copyNimTree copies the whole tree")
  never("NLineInfo", cNLineInfo, "line info is settable and readable")
  never("NodeId", cNodeId, "nodeID is stable for a node")
  never("ParseExprToAst", cParseExpr, "parseExpr turns text into an expression tree")
  never("ParseStmtToAst", cParseStmt, "parseStmt turns text into a statement tree")
  never("NHint", cNHint, "hint emits a compile-time hint")
  never("NWarning", cNWarning, "warning emits a compile-time warning")
  never("NError", cNError, "error aborts the compile: a failing compiles() probe")

suite "M1: std/macros, probed in a typed macro":
  never("GetImpl", m1Typed[0], "getImpl returns the proc definition")
  never("GetImplTransf", m1Typed[1], "getImplTransformed returns the transformed definition")
  never("NSymKind", m1Typed[2], "symKind of a proc symbol is nskProc")
  never("SymOwner", m1Typed[4], "a top-level proc's owner is its module")
  never("NGetType", m1Typed[5] and m1Typed[6], "getType and typeKind describe an int")
  never("NBindSym", m1Typed[7], "bindSym resolves a name to a symbol")
  never("SymIsInstantiationOf", m1Typed[8], "an instantiation of a generic proc knows its origin")
  never("NGenSym", m1Typed[9], "genSym makes a fresh symbol")
  never("NSigHash", m1Typed[10], "signatureHash of a symbol is non-empty")
  never("NSizeOf", m1Typed[11], "getSize reads an int's size")
  never("NCallSite", m1Typed[12], "callsite returns the macro call")
  never("QuoteAst", m1Typed[13], "quote builds a tree")
  never("NSymbol", m1Typed[14], "symbol reads a symbol node")
  never("SameNodeType", m1Typed[15], "sameType compares typed nodes")
  never("NSetSymbol", m1Typed[16], "symbol= rewrites a symbol node")
  never("ExpandToAst", m1Typed[17], "getAst expands a template into a tree")

suite "M1: std/macrocache":
  never("NccInc", cNccInc, "CacheCounter.inc bumps the counter")
  never("NccValue", cNccValue, "CacheCounter.value reads it")
  never("NcsAdd", cNcsAdd, "CacheSeq.add appends")
  never("NcsIncl", cNcsIncl, "CacheSeq.incl adds if absent")
  never("NcsAt", cNcsAt, "CacheSeq[] reads an entry")
  never("NcsLen", cNcsLen, "CacheSeq.len counts entries")
  never("NctPut", cNctPut, "CacheTable[]= stores an entry")
  never("NctGet", cNctGet, "CacheTable[] reads an entry")
  never("NctLen", cNctLen, "CacheTable.len counts entries")
  never("NctHasNext", cNctIter, "iterating a CacheTable walks it with hasNext")
  never("NctNext", cNctIter, "iterating a CacheTable walks it with next")
