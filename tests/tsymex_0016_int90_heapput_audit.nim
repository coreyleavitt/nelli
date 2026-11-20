## RFC-0016 INT-90: every write of a path's heaps goes through `heapPut`.
##
## A cross-sort fact (`crossSortLink`) relates two view sorts' heaps of one
## path at one statement. It is true of every native state only while every
## change of either heap so far was reflected in both: spliced into every
## other view sort's heap (`crossSortPropagate`), or, failing that, the path
## is desynced (`crossSortDesyncKey`) and emits no further fact. The walker
## has dozens of heap-writing sites (a deref write, an `addr` cell's store, a
## case object's field and arm stores, a pointer target's guarded store, a
## `new`'s zero-init, an opaque call's havoc, ...); before this audit only
## two of them took part (the deref write spliced, the `addr` cell store
## desynced), and the rest were sound only because the types they write
## happened to be no views. That is a coincidence a later change can break
## without any test noticing.
##
## So the decision is made in ONE place, by heap key rather than by site:
## `heapPut(p, key, arr, how)` (heap_model.nim, `heapPutIn`) is the only
## indexed write of a path's heaps, and a write of kind `hwStore` into the
## leaf heap of a view sort that shares the `pointer` space with another
## (`crossSortSharedLeaf`) desyncs the path. A site cannot opt out by holding
## a type its author did not think of as a view. This suite pins that shape:
##
##   1. no indexed assignment to anything named `heaps` in `src/nelli/smt/`
##      other than `heapPutIn`'s one line, and no other Table mutator on it
##      (`del`, `mgetOrPut`, `[]=`, ...);
##   2. `hwSpliced` (the one changing write that skips the desync; an
##      `hwInput`/`hwCarry` that changes a held term is an `hwStore`) is
##      named only by the enum, `crossSortPropagate` (its own splices into
##      the other sorts) and `spliceCellStore` (the leaf a splice covered: a
##      deref write's, a `new`'s zero);
##   3. a whole-table replacement of a path's heaps (`.heaps = `) is one of
##      the pinned three -- the fork copy and the two joins, each of which
##      carries the joined paths' `allocCounters`, the desync key with them;
##   4. a `Path` built with given heaps (`heaps: `) is one of the pinned two,
##      each given the counters that go with them.
##
## Which previously unsynced store paths can reach a view's leaf heap. A
## view's leaves (`viewLeaves`) are the heap of a fixed-width integer or
## float sort (its id) or the `<O>__<f>` field heaps of a flat object of
## those, never a key with an `@` (`crossSortLeafShaped`, enforced in
## `viewLeaves` itself). So:
##   * a case object's field, arm and overlap stores (`variantCellStore`,
##     `multiVariantCellStore`, `outOfArmFieldStore`, the arm-field write,
##     the discriminator store's carried fields, `refVariantWholeStore`,
##     `ptrOverlapWrite`), its union image (`imageStore`) and active-member
##     heaps (`storeActive`), and a pointer's selector (`ptrSelOwnAtAlloc`):
##     every key is `<id>__@...`, so none is a leaf, by construction;
##   * a seq or table field family's element store through a pointer
##     (`ptrTargetWrite`'s aggregate and `seqIdx`/`tabKey` arms): its heap's
##     value is a seq or a table, no view scalar, so no `viewLeaves` names it;
##   * a pointer target's guarded store into a SCALAR field family
##     (`ptrTargetWrite`, `t.famKey`) CAN be a view's leaf: a `ptr int` that
##     may address `a.x` of a `ptr Two` view. Reproducer: `famStore` in
##     `tsymex_0016_int90_crosssortheap` (a false `sxUnsat` before);
##   * a `new`'s zero-init of a scalar or flat-object pointee writes the
##     keys a view of that type reads, but at a fresh address: in a native
##     state no other pointer holds it, so no fact made before the `new`
##     names it, and every later access of it at another sort relates to the
##     zero (no wrong verdict to reproduce). It is spliced now
##     (`spliceCellStore`), so it is no exception to the rule either;
##   * an opaque call's havoc already desynced (`heapEpochPrefix`); it is an
##     `hwStore` now as well.
import std/[unittest, os, strutils, algorithm]
import audit_scan_utils

proc smtSources(): seq[tuple[name, code: string]] =
  ## Every `.nim` under `src/nelli/smt/`, comment- and string-blind.
  for f in walkDirRec(smtSrcDir):
    if f.endsWith(".nim"):
      result.add (f.relativePath(smtSrcDir), codeOf(readFile(f)))

proc enclosingDecl(lines: seq[string]; i: int): string =
  ## The top-level declaration line (column 0) line `i` lies in.
  for j in countdown(i, 0):
    let l = lines[j]
    if l.len > 0 and l[0] in {'a'..'z', 'A'..'Z'}:
      for kw in ["proc ", "func ", "template ", "iterator ", "macro ",
                 "type ", "method ", "converter "]:
        if l.startsWith(kw):
          var n = l[kw.len .. ^1]
          var k = 0
          while k < n.len and isIdentChar(n[k]): inc k
          return kw.strip & " " & n[0 ..< k]
  ""

proc indexedAssigns(line, name: string): int =
  ## The `name[...] = ` (not `==`) assignments on `line`, `name` a whole
  ## identifier (a field access `x.name[` counts).
  var at = 0
  while true:
    let i = line.find(name & "[", at)
    if i < 0: return
    at = i + 1
    if i > 0 and isIdentChar(line[i - 1]): continue
    var j = i + name.len + 1
    var d = 1
    while j < line.len and d > 0:
      if line[j] == '[': inc d
      elif line[j] == ']': dec d
      inc j
    while j < line.len and line[j] == ' ': inc j
    if j < line.len and line[j] == '=' and
       (j + 1 >= line.len or line[j + 1] != '='):
      inc result

suite "INT-90: one choke point for a path's heap writes":
  let srcs = smtSources()

  test "the scan sees the walker and the heap algebra":
    var names: seq[string]
    for s in srcs: names.add s.name
    check "runtime.nim" in names
    check "runtime_heap.nim" in names
    check "heap_model.nim" in names

  test "the only indexed write of a heaps table is heapPutIn's":
    var hits: seq[string]
    for s in srcs:
      let lines = s.code.splitLines
      for i, l in lines:
        if indexedAssigns(l, "heaps") > 0:
          hits.add s.name & ":" & $(i + 1) & " in " & enclosingDecl(lines, i)
    checkpoint $hits
    check hits.len == 1
    check hits.len == 1 and hits[0].startsWith("heap_model.nim:") and
          hits[0].endsWith(" in proc heapPutIn")

  test "no other Table mutator touches a heaps table":
    for s in srcs:
      let lines = s.code.splitLines
      for i, l in lines:
        for m in ["heaps.del(", "heaps.mgetOrPut(", "heaps.`[]=`(",
                  "heaps.clear(", "heaps.take(", "heaps.pop(",
                  "heaps.add(", "heaps.withValue(", "[]=`(p.heaps",
                  "addr p.heaps", "heaps.mpairs", "heaps.mvalues"]:
          checkpoint s.name & ":" & $(i + 1) & " " & m
          check m notin l

  test "hwSpliced is named only where a splice is made":
    var where: seq[string]
    for s in srcs:
      let lines = s.code.splitLines
      for i, l in lines:
        var at = 0
        while true:
          let k = l.find("hwSpliced", at)
          if k < 0: break
          at = k + 1
          if k > 0 and isIdentChar(l[k - 1]): continue
          if k + 9 < l.len and isIdentChar(l[k + 9]): continue
          where.add s.name & " " & enclosingDecl(lines, i)
    checkpoint $where
    check where == @["heap_model.nim type HeapWrite",
                     "runtime_heap.nim proc crossSortPropagate",
                     "runtime_heap.nim proc spliceCellStore"]

  test "a whole heaps table is replaced only by the fork copy and the joins":
    var where: seq[string]
    for s in srcs:
      let lines = s.code.splitLines
      for i, l in lines:
        let k = l.find(".heaps = ")
        if k >= 0:
          where.add s.name & " " & enclosingDecl(lines, i)
    checkpoint $where
    where.sort()   # the scan's file order is the directory's
    check where == @[# RFC-0016 INT-34 B6b: the joins are `walk_expr`'s
                     "walk_expr.nim proc drainClosureExitHeap",
                     "walk_expr.nim proc mergeJoinPaths",
                     # RFC-0016 INT-34 B3: the fork copy is `walk_path`'s
                     "walk_path.nim proc deepCopyHeapState"]
    # each carries the paths' counters with the heaps (the desync key)
    for s in srcs:
      if s.name notin ["runtime.nim", "walk_path.nim", "walk_expr.nim"]:
        continue
      let lines = s.code.splitLines
      for i, l in lines:
        if ".heaps = " notin l: continue
        var j = i
        var body = ""
        while j < lines.len and j < i + 40:
          body.add lines[j] & "\n"
          inc j
        checkpoint enclosingDecl(lines, i)
        check "allocCounters" in body or "joinHeapMeta" in body or
              "exitAlloc" in body

  test "a path built with given heaps is given their counters too":
    var where: seq[string]
    for s in srcs:
      let lines = s.code.splitLines
      for i, l in lines:
        let k = l.find("heaps: ")
        if k < 0 or (k > 0 and isIdentChar(l[k - 1])): continue
        # a declaration of the field or a parameter, not a construction
        if "Table[" in l: continue
        where.add s.name & " " & enclosingDecl(lines, i)
        var body = ""
        for j in i ..< min(i + 6, lines.len): body.add lines[j] & "\n"
        checkpoint enclosingDecl(lines, i)
        check "allocCounters: " in body
    checkpoint $where
    where.sort()   # the scan's file order is the directory's
    check where == @["runtime.nim proc applyClosureGround",
                     # RFC-0016 INT-34 B3: the fork primitive is `walk_path`'s
                     "walk_path.nim template forkPathTaintPrimitive"]

  test "heapPut is the template over heapPutIn, defined once":
    var defs = 0
    for s in srcs:
      for l in s.code.splitLines:
        if l.startsWith("template heapPut*(") or
           l.startsWith("proc heapPutIn*("):
          inc defs
    check defs == 2
