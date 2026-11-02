## RFC-0005 (soundness channels) slice S8bi -- S8bb's remainder, part A:
## the soundness and crash items S8bb reported and did not fix.
##
## Item 1: every node that can raise counts as a raise site in
## `rhsHasInlineDefectFork`. A call through a closure, a `map`/`filter`
## over a closure, a borrowed arithmetic operator and a regex call were
## carriers only (their operands could raise, they could not), so in a
## `while` guard -- where `parseAtomicOperand` hoists nothing and the
## predicate is the only protection -- D1c's flat fast path lowered them
## whether or not the short circuit reached them: `b >= 0 and f(b)` forked
## `f`'s raise for `b < 0`, a false `sxSat`.
##
## Item 2: each raise carries only the facts of what was evaluated before
## it. A closure call's exit facts (its body did not raise) were appended
## to every raise of the expression, also those evaluated before the call:
## in `while ord(s[i]) + f(x) > 0` the `IndexDefect` was forked only with
## `x <= 5`, a false `sxUnsat`. And an operand left inline (`s[i]`) was
## evaluated after a later operand's hoisted `let`s.
##
## Item 3: `newSeq[T](n)`, `newSeq(s, n)`, `newSeqOfCap[T](n)` and
## `newSeqUninit[T](n)` aborted the compile ("node has no type").
##
## Item 4: `k in {..}` / `k notin {..}` over a set literal was
## `feUnsupportedExprKind` (nnkCurly).
##
## Item 5: every recursive Z3 definition carries a decreasing fuel bound
## (Z3 unfolds one without spending `rlimit`); a source scan pins it.
import std/[unittest, strutils, re, sequtils, os, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc onlyLengthDecline(errs: seq[SymexErrorInfo]): bool =
  ## RFC-0005 batch 5. Every error is S8bc's length decline
  ## (`parseNewSeqLen`): a length above 2^20 is not modelled, scoped.
  if errs.len == 0: return false
  for e in errs:
    if e.kind != feUnsupportedOp or "length above 1048576" notin e.msg:
      return false
  true

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

# ---- item 1: raise sites behind a while guard's short circuit ---------------

type M = distinct int
proc `div`(a, b: M): M {.borrow.}
proc `==`(a, b: M): bool {.borrow.}

proc wClosureRaise(b: int) =
  let f = proc (x: int): bool =
    if x < 0: raise newException(ValueError, "neg")
    x > 3
  try:
    while b >= 0 and f(b): break
  except ValueError:
    symexTarget("bi_w_closure_raise")

proc wClosureReached(b: int) =
  # The control: past the short circuit the raise is reachable.
  let f = proc (x: int): bool =
    if x < 0: raise newException(ValueError, "neg")
    x > 3
  try:
    while b <= 0 and f(b): break
  except ValueError:
    symexTarget("bi_w_closure_reached")

proc wClosureDiv(b: int) =
  let f = proc (x: int): int = 10 div x
  try:
    while b == 0 or f(b) > 1: break
  except DivByZeroDefect:
    symexTarget("bi_w_closure_div")

proc wHof(b: int) =
  try:
    while b == 0 or @[1, 2].map(proc (x: int): int = x div b).len > 1: break
  except DivByZeroDefect:
    symexTarget("bi_w_hof")

proc wBorrow(b: M) =
  try:
    while b == M(0) or (M(10) div b) == M(5): break
  except DivByZeroDefect:
    symexTarget("bi_w_borrow")

proc wUnknownRegex(s: string) =
  # `(*UTF8)` leaves the pattern's validity undecided (a decline); behind
  # the short circuit Nim never runs it when `s.len <= 3`.
  var k = 0
  while s.len > 3 and s.match(re"(*UTF8)a"):
    inc k
    break
  if s.len == 1 and k == 0:
    symexTarget("bi_w_unknown_regex")

proc wValueRegex(s: string; p: string) =
  var k = 0
  try:
    while s.len > 3 and s.match(re(p)):
      inc k
      break
  except RegexError: discard
  if s.len == 1 and k == 0:
    symexTarget("bi_w_value_regex")

proc wRejectedThenDiv(s: string; b: int) =
  # The rejected pattern raises before the division is evaluated.
  try:
    while s.match(re"(ab") or 10 div b > 1: break
  except DivByZeroDefect:
    symexTarget("bi_w_rejected_then_div")
  except RegexError: discard

proc ifUnknownRegex(s: string) =
  if s.len > 3 and s.match(re"(*UTF8)a"):
    discard
  elif s.len == 1:
    symexTarget("bi_if_unknown_regex")

# ---- item 2: facts of later evaluations stay off earlier raises -------------

proc exitGuardIdx(s: string; i, x: int) =
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while ord(s[i]) + f(x) > 0: break
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_guard_idx")
  except ValueError: discard

proc exitGuardDiv(i, x: int) =
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while 10 div i + f(x) > 0: break
  except DivByZeroDefect:
    if x > 5: symexTarget("bi_exit_guard_div")
  except ValueError, OverflowDefect: discard

proc exitGuardSurvivor(i, x: int) =
  # The closure's own exit fact (its division did not trap) on an earlier
  # raise.
  let f = proc (k: int): int = 10 div k
  try:
    while 10 div i + f(x) > 0: break
  except DivByZeroDefect:
    if i == 0 and x == 0: symexTarget("bi_exit_guard_surv")
  except OverflowDefect: discard

proc exitGuardAfter(s: string; i, x: int) =
  # The control: a raise AFTER the call does carry its exit facts.
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while f(x) + ord(s[i]) > 0: break
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_guard_after")
  except ValueError: discard

proc exitGuardBetween(s: string; i, j, x: int) =
  # Two inline raises around the call: the first lacks the call's facts,
  # the second has them.
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    while ord(s[i]) + f(x) + 10 div j > 0: break
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_between_idx")
  except DivByZeroDefect:
    if x > 5: symexTarget("bi_exit_between_div")
  except ValueError, OverflowDefect: discard

proc atomicIdxOrder(s: string; i, x: int) =
  # `s[i]` stays inline (CR-17(a)) while `chr(f(x))` is hoisted.
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    if s[i] == chr(f(x)): discard
  except IndexDefect:
    if x > 5: symexTarget("bi_atomic_idx_order")
  except ValueError, RangeDefect: discard

proc exitIfGuard(s: string; i, x: int) =
  let f = proc (k: int): int =
    if k > 5: raise newException(ValueError, "big")
    k
  try:
    if s[i] == 'a' and f(x) > 0: discard
  except IndexDefect:
    if x > 5: symexTarget("bi_exit_if_guard")
  except ValueError: discard

# ---- item 3: newSeq and friends ---------------------------------------------

proc nsLen(n: int) =
  let xs = newSeq[int](n)
  if xs.len == 3 and xs[1] == 0 and xs[2] == 0:
    symexTarget("bi_ns_len")

proc nsNonZero(n: int) =
  if n < 0: return
  let xs = newSeq[int](n)
  if xs.len > 2 and xs[2] != 0:
    symexTarget("bi_ns_nonzero")

proc nsNeg(n: int) =
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n == -4: symexTarget("bi_ns_neg")

proc nsNonNegRaise(n: int) =
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n >= 0: symexTarget("bi_ns_nonneg_raise")

proc nsIndex(n, i: int) =
  let xs = newSeq[int](n)
  try:
    discard xs[i]
  except IndexDefect:
    if n == 2 and i == 2: symexTarget("bi_ns_index")

proc nsStr(n: int) =
  var xs = newSeq[string](n)
  if n == 2:
    xs[1] = "q"
    if xs[0] == "" and xs[1] == "q": symexTarget("bi_ns_str")

proc nsVar(n: int) =
  var xs: seq[int]
  newSeq(xs, n)
  if xs.len == 4 and xs[3] == 0: symexTarget("bi_ns_var")

proc nsVarNeg(n: int) =
  var xs = @[1]
  try:
    newSeq(xs, n)
  except RangeDefect:
    if xs.len == 1 and n < 0: symexTarget("bi_ns_var_neg")

proc nsOfCap(n: int) =
  var xs = newSeqOfCap[int](n)
  xs.add 7
  if n == 50 and xs.len == 1 and xs[0] == 7: symexTarget("bi_ns_ofcap")

proc nsOfCapLen(n: int) =
  if n < 0: return
  let xs = newSeqOfCap[int](n)
  if xs.len != 0: symexTarget("bi_ns_ofcap_len")

proc nsOfCapNeg(n: int) =
  try:
    discard newSeqOfCap[int](n)
  except RangeDefect:
    symexTarget("bi_ns_ofcap_neg")

proc nsUninit(n: int) =
  let xs = newSeqUninit[int](n)
  if xs.len == 5: symexTarget("bi_ns_uninit")

proc nsTuple(n: int) =
  let xs = newSeq[(int, int)](n)
  if xs.len == 1: symexTarget("bi_ns_tuple")

# RFC-0005 batch 5: the unified lowering (S8bc's leaf split) backs a tuple
# element, and a length above 2^20 declines on its own path (S8bc's
# `parseNewSeqLen`). The bounded forms below are the S8bi pins with that
# path excluded, which stay decided.

proc nsTupleZero(n: int) =
  let xs = newSeq[(int, int)](n)
  if xs.len == 2 and xs[1][0] == 0 and xs[1][1] == 0:
    symexTarget("bi_ns_tuple_zero")

proc nsTupleNonZero(n: int) =
  if n < 0 or n > 1000: return
  let xs = newSeq[(int, int)](n)
  if xs.len > 1 and xs[1][1] != 0: symexTarget("bi_ns_tuple_nonzero")

proc nsNonZeroB(n: int) =
  if n < 0 or n > 1000: return
  let xs = newSeq[int](n)
  if xs.len > 2 and xs[2] != 0:
    symexTarget("bi_ns_nonzero_b")

proc nsNonNegRaiseB(n: int) =
  if n > 1000: return
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n >= 0: symexTarget("bi_ns_nonneg_raise_b")

proc nsOfCapLenB(n: int) =
  if n < 0 or n > 1000: return
  let xs = newSeqOfCap[int](n)
  if xs.len != 0: symexTarget("bi_ns_ofcap_len_b")

# RFC-0005 batch 5: a size argument is evaluated once. In a `while` guard
# `parseAtomicOperand` hoists nothing, and `parseExpr` leaves a closure
# call inline: the length guard's two branches and the length itself each
# applied `f` (and `initTable`'s size guard, twice, anywhere).

proc nsGuardOnce(x: int) =
  if x < 0 or x > 1000: return
  var cnt = 0
  let f = proc (k: int): int =
    inc cnt
    k
  var it = 0
  while newSeq[int](f(x)).len > 2 and it < 1:
    inc it
  if cnt > 2: symexTarget("bi_ns_guard_once")

proc nsGuardTwo(x: int) =
  if x < 0 or x > 1000: return
  var cnt = 0
  let f = proc (k: int): int =
    inc cnt
    k
  var it = 0
  while newSeq[int](f(x)).len > 2 and it < 1:
    inc it
  if cnt == 2: symexTarget("bi_ns_guard_two")

proc initSizeOnce(x: int) =
  if x < 0 or x > 1000: return
  var cnt = 0
  let f = proc (k: int): int =
    inc cnt
    k
  let t = initTable[int, int](f(x))
  if cnt != 1 or t.len != 0: symexTarget("bi_init_size_once")

proc nsShortCircuitB(n: int) =
  var k = 0
  try:
    while n >= 0 and n <= 1000 and newSeq[int](n).len > 2:
      inc k
      break
  except RangeDefect:
    symexTarget("bi_ns_short_circuit_b")

proc nsShortCircuit(n: int) =
  # A raise site under a while guard's short circuit (item 1's predicate).
  var k = 0
  try:
    while n >= 0 and newSeq[int](n).len > 2:
      inc k
      break
  except RangeDefect:
    symexTarget("bi_ns_short_circuit")

# ---- item 4: set literals ---------------------------------------------------

type E = enum eA, eB, eC, eD
const Ident = {'a'..'z', '_'}

proc setNotin(c: char) =
  if c notin {'a'..'z', '_'} and (c == 'y' or c == '_'):
    symexTarget("bi_set_notin")

proc setNotinSat(c: char) =
  if c notin {'a'..'z', '_'} and (c == '{' or c == 'a'):
    symexTarget("bi_set_notin_sat")

proc setNotinNone(c: char) =
  if c notin {'\0'..'\255'}:
    symexTarget("bi_set_notin_none")

proc setInInt(x: int) =
  if x in {1, 3, 5..7} and x > 5:
    symexTarget("bi_set_in_int")

proc setInIntOut(x: int) =
  if x in {1, 3} and (x < 0 or x > 255):
    symexTarget("bi_set_in_int_out")

proc setInEnum(e: E) =
  if e in {eA, eC..eD} and e != eA and e != eD:
    symexTarget("bi_set_in_enum")

proc setInEnumNo(e: E) =
  if e in {eA, eC..eD} and e == eB:
    symexTarget("bi_set_in_enum_no")

proc setConst(c: char) =
  if c in Ident and c notin {'b'..'z'} and c != '_':
    symexTarget("bi_set_const")

proc setU8(u: uint8) =
  if u in {1'u8, 200'u8} and u > 100'u8:
    symexTarget("bi_set_u8")

proc setBool(b: bool) =
  if b in {true}:
    symexTarget("bi_set_bool")

const NoChars: set[char] = {}

proc setEmpty(c: char) =
  if c in NoChars:
    symexTarget("bi_set_empty")

proc setKeyIdx(s: string; i: int) =
  # A raising key is read once, before membership.
  try:
    if s[i] in {'a', 'b'}:
      symexTarget("bi_set_key_idx")
  except IndexDefect:
    discard

proc setWhile(s: string) =
  var i = 0
  while i < s.len and s[i] notin {'0'..'9'}:
    inc i
  if s.len == 3 and i == 2:
    symexTarget("bi_set_while")

proc setValue(c: char) =
  let ss: set[char] = {'a', 'b'}
  if c in ss:
    symexTarget("bi_set_value")

# ---- item 5: recursive definitions carry fuel -------------------------------

proc stripComments(src: string): string =
  ## Drop `#` comments (outside string and char literals) so the scan sees
  ## code only.
  var inStr = false
  var i = 0
  while i < src.len:
    let c = src[i]
    if inStr:
      result.add c
      if c == '\\' and i + 1 < src.len:
        result.add src[i + 1]
        inc i
      elif c == '"':
        inStr = false
    elif c == '"':
      inStr = true
      result.add c
    elif c == '\'' and i + 2 < src.len and src[i + 2] == '\'':
      result.add src[i .. i + 2]
      i += 2
    elif c == '#':
      while i < src.len and src[i] != '\n': inc i
      continue
    else:
      result.add c
    inc i

proc matchParen(s: string; open: int): int =
  ## The index of the `)` closing the `(` at `open`, or -1.
  var depth = 0
  for k in open ..< s.len:
    if s[k] == '(': inc depth
    elif s[k] == ')':
      dec depth
      if depth == 0: return k
  -1

proc splitTopArgs(s: string): seq[string] =
  var depth = 0
  var cur = ""
  for c in s:
    if c in {'(', '['}: inc depth
    elif c in {')', ']'}: dec depth
    if c == ',' and depth == 0:
      result.add cur.strip
      cur = ""
    else:
      cur.add c
  if cur.strip.len > 0: result.add cur.strip

proc recFuelViolations(code: string; file: string): seq[string] =
  ## Every `defineRecFun[` call: a `fuel: Z3Int` parameter, a
  ## `fuel <= mkInt(0)` base case, and every recursive `self(..)` call
  ## passing `fuel - mkInt(1)` (directly or as `f1`, bound to it) last.
  ## The raw API (`Z3_mk_rec_func_decl` / `Z3_add_rec_def`) and SMT-LIB
  ## `define-fun-rec` are not to be used around it.
  for raw in ["Z3_mk_rec_func_decl", "Z3_add_rec_def", "define-fun-rec"]:
    if raw in code:
      result.add file & ": raw recursive definition `" & raw & "`"
  var at = code.find("defineRecFun[")
  while at >= 0:
    let open = code.find('(', code.find(']', at))
    let close = matchParen(code, open)
    if open < 0 or close < 0:
      result.add file & ": unparsable defineRecFun call"
      break
    let call = code[open .. close]
    let line = code[0 ..< at].count('\n') + 1
    let where = file & ":" & $line
    let lam = call.find("proc")
    let pOpen = call.find('(', lam)
    let pClose = matchParen(call, pOpen)
    if lam < 0 or pClose < 0:
      result.add where & ": no lambda body"
    else:
      let params = call[pOpen .. pClose]
      if "fuel: Z3Int" notin params:
        result.add where & ": no `fuel: Z3Int` parameter"
      let body = call[pClose + 1 .. ^1]
      if "fuel <= mkInt(0)" notin body:
        result.add where & ": no `fuel <= mkInt(0)` base case"
      let f1Bound = "f1 = fuel - mkInt(1)" in body
      var selfAt = body.find("self(")
      var calls = 0
      while selfAt >= 0:
        inc calls
        let sOpen = selfAt + "self".len
        let sClose = matchParen(body, sOpen)
        let args = splitTopArgs(body[sOpen + 1 ..< sClose])
        let last = if args.len > 0: args[^1] else: ""
        if not (last == "fuel - mkInt(1)" or (last == "f1" and f1Bound)):
          result.add where & ": recursive call `self(" &
                     body[sOpen + 1 ..< sClose] & ")` does not pass " &
                     "`fuel - mkInt(1)` last"
        selfAt = body.find("self(", sClose)
      if calls == 0:
        result.add where & ": no recursive `self(..)` call found"
    at = code.find("defineRecFun[", close)

const srcRoot = currentSourcePath.parentDir() / ".." / "src"

suite "S8bi: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 210

suite "S8bi (1): raise sites behind a while guard's short circuit":
  test "a closure's raise is not forked when the short circuit skips it":
    check verdict(wClosureRaise, "bi_w_closure_raise").status == sxUnsat
  test "control: past the short circuit it is reachable":
    check verdict(wClosureReached, "bi_w_closure_reached").status == sxSat
  test "a closure's division behind `or`":
    check verdict(wClosureDiv, "bi_w_closure_div").status == sxUnsat
  test "a map over a closure behind `or`":
    check verdict(wHof, "bi_w_hof").status == sxUnsat
  test "a borrowed division behind `or`":
    check verdict(wBorrow, "bi_w_borrow").status == sxUnsat
  test "an undecided pattern behind `and` does not taint the skipping path":
    let r = verdict(wUnknownRegex, "bi_w_unknown_regex")
    check r.status == sxSat
  test "a non-literal Regex behind `and` does not taint the skipping path":
    let r = verdict(wValueRegex, "bi_w_value_regex")
    check r.status == sxSat
  test "control: a rejected pattern raises before the division":
    check verdict(wRejectedThenDiv, "bi_w_rejected_then_div").status == sxUnsat
  test "an undecided pattern behind `and` in an if guard":
    check verdict(ifUnknownRegex, "bi_if_unknown_regex").status == sxSat
  test "newSeq's RangeDefect behind `and`":
    # RFC-0005 batch 5: unbounded, the n > 2^20 path declines (S8bc's
    # guard, now on every seq constructor), so the verdict is honest
    # sxUnknown; bounded, the S8bi pin stands.
    let r = verdict(nsShortCircuit, "bi_ns_short_circuit")
    check r.status == sxUnknown
    check onlyLengthDecline(r.errors)
    check verdict(nsShortCircuitB, "bi_ns_short_circuit_b").status == sxUnsat

suite "S8bi (2): a raise carries only what was evaluated before it":
  test "an index raise before a closure call (while guard)":
    check verdict(exitGuardIdx, "bi_exit_guard_idx").status == sxSat
  test "a division raise before a closure call (while guard)":
    check verdict(exitGuardDiv, "bi_exit_guard_div").status == sxSat
  test "the closure's own trap fact is not on an earlier raise":
    check verdict(exitGuardSurvivor, "bi_exit_guard_surv").status == sxSat
  test "control: a raise after the call carries its facts":
    check verdict(exitGuardAfter, "bi_exit_guard_after").status == sxUnsat
  test "a raise before the call lacks its facts; one after has them":
    check verdict(exitGuardBetween, "bi_exit_between_idx").status == sxSat
    check verdict(exitGuardBetween, "bi_exit_between_div").status == sxUnsat
  test "an inline index is evaluated before a hoisted later operand":
    check verdict(atomicIdxOrder, "bi_atomic_idx_order").status == sxSat
  test "control: an if guard's index before the call":
    check verdict(exitIfGuard, "bi_exit_if_guard").status == sxSat

suite "S8bi (3): newSeq, newSeqOfCap, newSeqUninit":
  test "newSeq has length n and zero elements":
    let r = verdict(nsLen, "bi_ns_len")
    check r.status == sxSat
    check onlyLengthDecline(r.errors)   # batch 5: the n > 2^20 path only
  test "a newSeq element is never nonzero":
    let r = verdict(nsNonZero, "bi_ns_nonzero")
    check r.status == sxUnknown   # batch 5: the n > 2^20 path declines
    check onlyLengthDecline(r.errors)
    check verdict(nsNonZeroB, "bi_ns_nonzero_b").status == sxUnsat
  test "a negative length raises RangeDefect":
    check verdict(nsNeg, "bi_ns_neg").status == sxSat
  test "a non-negative length does not raise":
    let r = verdict(nsNonNegRaise, "bi_ns_nonneg_raise")
    check r.status == sxUnknown   # batch 5: the n > 2^20 path declines
    check onlyLengthDecline(r.errors)
    check verdict(nsNonNegRaiseB, "bi_ns_nonneg_raise_b").status == sxUnsat
  test "index n of a newSeq of length n raises IndexDefect":
    check verdict(nsIndex, "bi_ns_index").status == sxSat
  test "newSeq[string] elements are empty":
    check verdict(nsStr, "bi_ns_str").status == sxSat
  test "the statement newSeq(s, n)":
    check verdict(nsVar, "bi_ns_var").status == sxSat
  test "newSeq(s, n) raises before assigning":
    check verdict(nsVarNeg, "bi_ns_var_neg").status == sxSat
  test "newSeqOfCap is empty":
    check verdict(nsOfCap, "bi_ns_ofcap").status == sxSat
    let r = verdict(nsOfCapLen, "bi_ns_ofcap_len")
    check r.status == sxUnknown   # batch 5: the n > 2^20 path declines
    check onlyLengthDecline(r.errors)
    check verdict(nsOfCapLenB, "bi_ns_ofcap_len_b").status == sxUnsat
  test "newSeqOfCap range-checks its capacity":
    check verdict(nsOfCapNeg, "bi_ns_ofcap_neg").status == sxSat
  test "newSeqUninit has length n (RFC-0005 S8bq: no element read, no taint)":
    # S8bi tainted the whole path at the call (`feUnsupportedOpHavoc`);
    # S8bq taints only a read of an unwritten element, and this reads none.
    let r = verdict(nsUninit, "bi_ns_uninit")
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
  test "a tuple element is backed (batch 5: S8bc's leaf split)":
    # S8bi pinned this as an unbacked-element decline; the unified lowering
    # builds one constant array per leaf (S8bc). Native: a newSeq of tuples
    # holds `(0, 0)` at every index.
    check newSeq[(int, int)](2) == @[(0, 0), (0, 0)]
    let r = verdict(nsTuple, "bi_ns_tuple")
    check r.status == sxSat
    check not r.errors.hasKind(seNestedSeqUnsupported)
    check verdict(nsTupleZero, "bi_ns_tuple_zero").status == sxSat
    check verdict(nsTupleNonZero, "bi_ns_tuple_nonzero").status == sxUnsat

suite "batch 5: a size argument is evaluated once":
  test "native: the guard applies f once per test":
    var cnt = 0
    let f = proc (k: int): int =
      inc cnt
      k
    var it = 0
    while newSeq[int](f(5)).len > 2 and it < 1:
      inc it
    check cnt == 2
    var c2 = 0
    let g = proc (k: int): int =
      inc c2
      k
    let t = initTable[int, int](g(5))
    check c2 == 1 and t.len == 0
  test "newSeq's length in a while guard":
    # Before: f applied three times per test, so cnt > 2 was sxSat and the
    # count Nim makes (2, at x = 5) sxUnsat.
    check verdict(nsGuardOnce, "bi_ns_guard_once").status == sxUnsat
    check verdict(nsGuardTwo, "bi_ns_guard_two").status == sxSat
  test "initTable's size":
    check verdict(initSizeOnce, "bi_init_size_once").status == sxUnsat

suite "S8bi (4): set literals in `in` / `notin`":
  test "notin over a char range and a char":
    check verdict(setNotin, "bi_set_notin").status == sxUnsat
    let r = verdict(setNotinSat, "bi_set_notin_sat")
    check r.status == sxSat
    check $r.witness == "('{',)"
  test "notin over every char":
    check verdict(setNotinNone, "bi_set_notin_none").status == sxUnsat
  test "in over ints and an int range":
    let r = verdict(setInInt, "bi_set_in_int")
    check r.status == sxSat
    check r.errors.len == 0
  test "a key outside the set's base range is not a member and does not raise":
    check verdict(setInIntOut, "bi_set_in_int_out").status == sxUnsat
  test "in over enum fields and an enum range":
    check verdict(setInEnum, "bi_set_in_enum").status == sxSat
    check verdict(setInEnumNo, "bi_set_in_enum_no").status == sxUnsat
  test "a const set":
    check verdict(setConst, "bi_set_const").status == sxSat
  test "unsigned elements":
    check verdict(setU8, "bi_set_u8").status == sxSat
  test "bool elements":
    check verdict(setBool, "bi_set_bool").status == sxSat
  test "the empty set":
    check verdict(setEmpty, "bi_set_empty").status == sxUnsat
  test "a raising key":
    check verdict(setKeyIdx, "bi_set_key_idx").status == sxSat
  test "notin in a while guard":
    check verdict(setWhile, "bi_set_while").status == sxSat
  test "a set-typed value (RFC-0005 S8bq: modelled)":
    # S8bi declined it, classified; S8bq models builtin `set[T]` values.
    let r = verdict(setValue, "bi_set_value")
    check r.status == sxSat
    check r.errors.len == 0

suite "S8bi (5): recursive definitions carry fuel":
  test "the scan rejects a definition without fuel":
    let bad = """
  let f = defineRecFun[Z3String, Z3String](ctx, "g",
    proc (self: Z3FuncDecl[(Z3String,), Z3String]; u: Z3String): Z3String =
      ite(len(u) == mkInt(0), u, self(substr(u, mkInt(1), len(u))))))
"""
    check recFuelViolations(bad, "fixture").len >= 3
    let noDecrease = """
  let f = defineRecFun[Z3String, Z3Int, Z3String](ctx, "g",
    proc (self: Z3FuncDecl[(Z3String, Z3Int), Z3String]; u: Z3String;
          fuel: Z3Int): Z3String =
      ite(fuel <= mkInt(0), u, self(u, fuel)))
"""
    check recFuelViolations(noDecrease, "fixture").len == 1
    check recFuelViolations("Z3_add_rec_def(c, f)", "fixture").len == 1
  test "the scan accepts a fueled definition":
    let good = """
  let f = defineRecFun[Z3String, Z3Int, Z3String](ctx, "g",
    proc (self: Z3FuncDecl[(Z3String, Z3Int), Z3String]; u: Z3String;
          fuel: Z3Int): Z3String =
      let f1 = fuel - mkInt(1)
      ite(fuel <= mkInt(0), u, self(substr(u, mkInt(1), len(u)), f1)))
"""
    check recFuelViolations(good, "fixture").len == 0
  test "every recursive definition under src/ carries fuel":
    var violations: seq[string]
    var defs = 0
    for path in walkDirRec(srcRoot):
      if not path.endsWith(".nim"): continue
      let code = stripComments(readFile(path))
      defs += code.count("defineRecFun[")
      violations.add recFuelViolations(code, path.relativePath(srcRoot))
    checkpoint violations.join("\n")
    check violations.len == 0
    check defs >= 4   # the two replace runs, `run` and `rep`
