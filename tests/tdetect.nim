import std/[unittest, macros, options, tables, sets]
import proptest/derive/detect

# #104 — testable seam for derive's recursive-type detection.
#
# Tests drive the detection helpers via `getTypeImpl` on real declared
# types — exactly the shape the `arbitrary(T)` macro consumes. A thin
# compile-time wrapper macro classifies the type and emits the verdict
# as a runtime literal the unittest framework can check.

# Types under test. Self-referencing patterns the detector must handle.
type
  DirectRef = ref object
    next: DirectRef
  Bar = object
    value: int                ## non-self, not even a forward ref
  WithSeq = ref object
    children: seq[WithSeq]
  WithOption = ref object
    opt: Option[WithOption]
  WithHashSet = ref object
    pals: HashSet[int]        ## HashSet of *non-self*; should be drNone for self
  WithTableV = ref object
    nm: Table[string, WithTableV]
  # Mutual recursion
  MutA = ref object
    bs: seq[MutB]
  MutB = ref object
    a: MutA

# isSelfType — operates directly on an ident/sym so we can hit it without
# the macro wrapper.

suite "isSelfType":
  test "ident matching the name returns true":
    static:
      doAssert isSelfType(ident"Foo", "Foo")
      doAssert not isSelfType(ident"Foo", "Bar")
      doAssert not isSelfType(newLit(42), "Foo")  # non-ident: false
    check true

# Compile-time bridges. Each macro takes a real type, walks its
# `getTypeImpl` (or a specific field's type), and emits the classification
# verdict as a runtime RecursionKind literal.

macro classifyField(typeName: static[string],
                    parentType: typedesc, fieldName: static[string]):
                    RecursionKind =
  ## Find the named field in `parentType`'s `getTypeImpl`, classify its
  ## type against `typeName`. This is exactly how `derive.nim`'s
  ## `fieldValueExpr` consumes the detector.
  # `typedesc` macro parameters require `.getTypeInst[1]` to extract the
  # underlying type-AST (matches the idiom in derive.nim's `arbitrary`).
  let typeSym = parentType.getTypeInst[1]
  var impl = typeSym.getTypeImpl
  if impl.kind == nnkRefTy:
    # Unwrap one level of ref-of-object.
    var inner = impl[0]
    if inner.kind == nnkSym: inner = inner.getTypeImpl
    impl = inner
  doAssert impl.kind == nnkObjectTy,
    "parent isn't a ref object or object: " & $impl.kind
  let recList = impl[2]
  for fd in recList:
    if fd.kind == nnkIdentDefs:
      for i in 0 ..< fd.len - 2:
        if $fd[i] == fieldName:
          return newLit(classifyRecursion(fd[fd.len - 2], typeName))
  error("classifyField: no field named " & fieldName)

suite "classifyRecursion via getTypeImpl on real types":
  test "drDirect — bare ref-self field":
    check classifyField("DirectRef", DirectRef, "next") == drDirect

  test "drViaSeq — seq[Self]":
    check classifyField("WithSeq", WithSeq, "children") == drViaSeq

  test "drViaOption — Option[Self]":
    check classifyField("WithOption", WithOption, "opt") == drViaOption

  test "drViaTable — Table[_, Self]":
    check classifyField("WithTableV", WithTableV, "nm") == drViaTable

  test "drNone — field type doesn't reference self":
    check classifyField("WithHashSet", WithHashSet, "pals") == drNone

  test "drMutual — A's field references B which transitively reaches A":
    check classifyField("MutA", MutA, "bs") == drMutual
