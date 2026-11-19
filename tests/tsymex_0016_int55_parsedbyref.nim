## RFC-0016 INT-55: a heap lvalue passed to a `var` formal, in a routine a
## macro emitted through `parseStmt`. The walker marks such a base by
## reference (`markByRef`, RFC-0005 S8ba) and used to give the mark the base
## node's file name; a node `parseStmt` built carries a pseudo path (no file
## on disk), and the compile-time VM's `setFile` expands the name with
## `expandFilename`, whose OSError escapes the VM and stops the compiler
## (`Error: unhandled exception: No such file or directory [OSError]`). K8b's
## `faExnMemory` family found it through its `twRoute` relation (every write
## routed through a `var` parameter) on a field, element or ref-field base.
import std/[unittest, macros, sequtils]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

macro emitParsed(): untyped =
  parseStmt("""
type I55Obj = object
  f: int
type I55Ref = ref object
  f: int
proc i55Set(x: var int; v: int) = x = v
proc i55Field(a: int8) =
  var o = I55Obj(f: 1)
  i55Set(o.f, int(a) * 3)
  if o.f == 21: symexTarget("hit")
proc i55Elem(a: int8) =
  var s = @[0, 1, 0]
  i55Set(s[1], int(a) + 5)
  if s[1] == 4: symexTarget("hit")
proc i55RefField(a: int8) =
  let o = I55Ref(f: 1)
  i55Set(o.f, int(a))
  if o.f == 300: symexTarget("hit")
""")

emitParsed()

suite "INT-55: a by-reference base in a parsed routine":
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "an object field through a var formal compiles and is exact (sat)":
    let r = pinExact(i55Field, cellKey(faExnMemory, "k8b/mem/objField"),
                     tLabel("hit"), all)
    check r.status == sxSat

  test "a seq element through a var formal compiles and is exact (sat)":
    let r = pinExact(i55Elem, cellKey(faExnMemory, "k8b/mem/seqElem"),
                     tLabel("hit"), all)
    check r.status == sxSat

  test "a ref-object field through a var formal compiles and is exact (unsat)":
    let r = pinExact(i55RefField, cellKey(faExnMemory, "k8b/mem/refField"),
                     tLabel("hit"), all)
    check r.status == sxUnsat
