## RFC-0016 INT-64: a `Table` built by `toTable` over a literal of pairs
## (`{k: v}.toTable`, `std/tables`). `{t: u}.toTable[t] == 7` is sat
## (`b = 7`), as it is for the same table built by `initTable` and `[]=`
## (the control, exact).
##
## Red at 7746d32a: the walk declined `feUnsupportedStmtKind` ("for-loop
## over `items` with 2 loop variable(s)"): `toTable`'s body is `for key,
## val in items(pairs)`, and a multi-variable `items` loop over tuples was
## not lowered. Walker 422 binds each element to a fresh name and each
## variable to its field.
##
## K8b's read-only axis suite found it (INT-56): both `viewwhole` rows and typeop
## `letCursor/table` declined over a `toTable` table, so those fragments
## build theirs with `initTable` and `[]=`.
import std/[unittest, strutils, sequtils, tables]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc i64Init(a, b: int8) =
  let t = int(a)
  let u = int(b)
  var x = initTable[int, int]()
  x[t] = u
  if x[t] == 7: symexTarget("hit")

proc i64ToTable(a, b: int8) =
  let t = int(a)
  let u = int(b)
  let x = {t: u}.toTable
  if x[t] == 7: symexTarget("hit")

proc i64ToTableLen(a, b: int8) =
  let t = int(a)
  let x = {1: t, 2: 3}.toTable
  if x.len + x[1] == 9: symexTarget("hit")

proc i64Unsat(a, b: int8) =
  let t = int(a)
  let u = int(b)
  let x = {t: u, t + 1: 3}.toTable
  if x[t] == 300: symexTarget("hit")

proc i64SeqUnpack(a, b: int8) =
  ## The loop form `toTable` walks, over a seq of tuples directly.
  let s = @[(int(a), 2), (int(b), 5)]
  var acc = 0
  for k, v in items(s): acc = acc + k * v
  if acc == 31: symexTarget("hit")

proc i64ArrUnpack(a, b: int8) =
  var acc = 0
  for k, v in items([(int(a), 3), (4, int(b))]): acc = acc + k - v
  if acc == 10: symexTarget("hit")

suite "INT-64: a `toTable` table is exact":
  test "walker 422: the version floor":
    check parseInt(symexWalkerVersion) >= 422
  let all = exhaustive(toSeq(low(int8) .. high(int8)))
  test "control: a table built by `initTable` and `[]=` is exact (sat)":
    let r = symexFind(i64Init, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
  test "`{t: u}.toTable[t] == 7` is exact (sat)":
    let r = pinExact(i64ToTable, cellKey(axTypeOp, "letCursor/table"),
                     tLabel("hit"), all)
    check r.status == sxSat
  test "`{1: t, 2: 3}.toTable`: `len + x[1] == 9` is exact (sat)":
    let r = symexFind(i64ToTableLen, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
  test "an unsat target over a `toTable` table is exact (unsat)":
    let r = pinExact(i64Unsat, cellKey(axTypeOp, "letCursor/table"),
                     tLabel("hit"), all)
    check r.status == sxUnsat
  test "`for k, v in items(s)` over a seq of tuples is exact (sat)":
    let r = symexFind(i64SeqUnpack, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
  test "`for k, v in items([...])` over an array of tuples is exact (sat)":
    let r = symexFind(i64ArrUnpack, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " trusted=" & $r.trusted & " errors " & $r.errors
    check r.trusted
    check r.status == sxSat
