## Phase 5 — stdlib model registry catalogues what the parser handles.
import std/unittest
import nelli/symex

suite "symex Phase 5 — stdlib model registry":
  test "seq.len recognised":
    let m = getStdlibModelFor("len", itSeq)
    check m.kind == smkSeqLen

  test "Table.[] recognised":
    let m = getStdlibModelFor("[]", itTable)
    check m.kind == smkTableIndex

  test "Table.contains recognised":
    let m = getStdlibModelFor("contains", itTable)
    check m.kind == smkTableContains

  test "HashSet.contains recognised":
    let m = getStdlibModelFor("contains", itSet)
    check m.kind == smkSetContains

  test "unsupported callee returns unregistered":
    let m = getStdlibModelFor("foo", itInt)
    check m.kind == smkUnregistered
