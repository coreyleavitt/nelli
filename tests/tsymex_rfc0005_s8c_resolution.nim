## RFC-0005 (soundness channels) slice S8c -- silent substitution by
## NAME-resolved builtins (§2.2's class). The DSL parser recognised operators
## (`+ - * < == ...`), `contains`/`in`, `len`, `inc`/`dec`, `+=`, the `items`
## iterator and the rest of its builtin vocabulary by the callee's NAME. A
## user overload of one of those names -- `+` on a `distinct int`, `==` on an
## object, a non-generic `contains`/`len`/`items` that beats the stdlib
## generic, a `converter` -- was modelled as the builtin, so the engine
## claimed `sxSat`/`sxUnsat` about semantics the program does not have, with
## nothing recorded.
##
## S8c resolves the callee by SYMBOL: a builtin model applies only when the
## call's resolved symbol is declared in the compiler's own `lib/` tree. A
## user routine is walked like any other user call (the precise answer, not a
## taint); a user `converter` is walked too, and a user `method` (dynamic
## dispatch) is a recorded callee decline. The second-order shape -- a
## stdlib generic whose instantiated body reaches a user routine -- is pinned
## below as closed by the element fragment.
## Walker 149 -> 150.
import std/[unittest, strutils, sets, hashes]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import ./s8c_foreign_marker   ## a user `symexAssume` that is not the marker

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc dump(errs: seq[SymexErrorInfo]) =
  for e in errs: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)

# =============================================================================
# User overloads. Each is on a type no other code in this module (or a stdlib
# generic this module instantiates) uses, so the overload changes nothing but
# the SUT that exercises it.
# =============================================================================

type
  S8cMoney = distinct int
  S8cCtr = distinct int
  S8cPt = object
    x, y: int
  S8cLine = object
    a: S8cPt
    tag: int
  S8cKey = distinct int

proc `+`(a, b: S8cMoney): S8cMoney = S8cMoney(int(a) + int(b) + 1)
  ## Not the builtin: adds a one-unit fee.
proc `<`(a, b: S8cMoney): bool = int(a) > int(b)
  ## Not the builtin: reversed.
proc `-`(a: S8cMoney): S8cMoney = S8cMoney(int(a) + 5)
  ## Not negation.
proc `+=`(a: var S8cMoney, b: S8cMoney) = a = S8cMoney(int(a) + 2 * int(b))
  ## Not the builtin: doubles the increment.
proc inc(c: var S8cCtr) = c = S8cCtr(int(c) + 2)
  ## Steps by two.
proc `==`(a, b: S8cPt): bool = a.x == b.x
  ## Ignores `y`.
proc contains(s: HashSet[int], x: int): bool = x == 99
  ## Non-generic: beats `sets.contains[A]`. Membership is "is 99".
proc len(s: seq[int16]): int = 7
  ## Non-generic: beats `system.len[T](seq[T])`.
iterator items(s: seq[int8]): int8 = yield 99'i8
  ## Non-generic: beats `system.items[T](seq[T])`. Yields one 99.
proc `==`(a, b: S8cKey): bool = int(a) mod 10 == int(b) mod 10
  ## Keys are equal modulo 10 ...
proc hash(a: S8cKey): Hash = hash(int(a) mod 10)
  ## ... and hash consistently with that.
proc add(s: var seq[int], x: int) = discard (s, x)
  ## Non-generic: beats `system.add[T]`. Appends nothing.
proc find(s: string, code: int): int = 42
  ## A string-receiver routine named like `strutils.find` (int argument:
  ## no stdlib overload takes one). Always 42.
converter s8cToInt(m: S8cMoney): int = int(m) * 2
  ## An implicit conversion (`nnkHiddenCallConv`).

# =============================================================================
# SUTs
# =============================================================================

proc s8cPlus(a, b: S8cMoney) =
  ## Real: 0 + 0 == 1 (the fee). The builtin model said 0.
  if int(a) == 0 and int(b) == 0 and int(a + b) == 1:
    symexTarget("s8c_plus")

proc s8cLess(a, b: S8cMoney) =
  ## Real: `a < b` means int(a) > int(b), so this conjunction is impossible.
  if a < b and int(a) < int(b):
    symexTarget("s8c_less")

proc s8cNeg(a: S8cMoney) =
  ## Real: -a == a + 5, never equal to the builtin negation for a = 0.
  if int(a) == 0 and int(-a) == 5:
    symexTarget("s8c_neg")

proc s8cAugAssign(a, b: S8cMoney) =
  ## Real: m == a + 2b; with b == 1 that is never a + 1.
  if int(a) >= 0 and int(a) < 100 and int(b) == 1:
    var m = a
    m += b
    if int(m) == int(a) + 1:
      symexTarget("s8c_augassign")

proc s8cInc(n: int) =
  ## Real: the user `inc` steps by two, so c == n + 1 is impossible.
  if n >= 0 and n < 100:
    var c = S8cCtr(n)
    inc c
    if int(c) == n + 1:
      symexTarget("s8c_inc")

proc s8cEq(p, q: S8cPt) =
  ## Real: `==` ignores `y`, so equal points with different `y` exist.
  if p == q and p.y != q.y:
    symexTarget("s8c_eq")

proc s8cNe(p, q: S8cPt) =
  ## `!=` is `not (==)` -- it must resolve through the same user `==`.
  if not (p != q) and p.y != q.y:
    symexTarget("s8c_ne")

proc s8cContains(s: HashSet[int], x: int) =
  ## Real: `x in s` is `x == 99`, whatever `s` holds.
  if x in s and x != 99:
    symexTarget("s8c_contains")

proc s8cLen(xs: seq[int16]) =
  ## Real: the user `len` is always 7.
  if xs.len != 7:
    symexTarget("s8c_len")

proc s8cItems(xs: seq[int8]) =
  ## Real: the user `items` yields exactly one 99, whatever `xs` holds.
  var saw = false
  for x in xs:
    if x == 99'i8:
      saw = true
  if saw and system.len(xs) == 0:
    symexTarget("s8c_items")

proc s8cConverter(m: S8cMoney) =
  ## Real: the converter doubles.
  let x: int = m
  if int(m) == 1 and x == 2:
    symexTarget("s8c_converter")

proc s8cAdd(xs: seq[int]) =
  ## Real: the user `add` appends nothing.
  var ys = xs
  ys.add 5
  if system.len(ys) == system.len(xs):
    symexTarget("s8c_add")

proc s8cFind(s: string) =
  ## Real: the user `find` is always 42.
  if s.find(3) != 42:
    symexTarget("s8c_find")

proc s8cFieldEq(l1, l2: S8cLine) =
  ## `system.==` over an object: its instantiated body compares the `a`
  ## field with the USER `==`, so equal lines with different `a.y` exist.
  if l1 == l2 and l1.a.y != l2.a.y:
    symexTarget("s8c_field_eq")

proc s8cSetKey(s: HashSet[S8cKey], k: int) =
  ## `sets.contains[S8cKey]` is stdlib, but its instantiated body hashes and
  ## compares with the USER `hash`/`==` (equality modulo 10), so the two
  ## memberships are the same question: the conjunction is unreachable.
  if S8cKey(k) in s and not (S8cKey(k mod 10) in s):
    symexTarget("s8c_setkey")

proc s8cSeqEq(k: int) =
  ## `system.==[S8cKey](seq)` compares elements with the USER `==`.
  let a = @[S8cKey(k)]
  let b = @[S8cKey(3)]
  if k == 13 and a == b:
    symexTarget("s8c_seqeq")

proc s8cTupEq(k: int) =
  ## `system.==` over a tuple compares the first element with the USER `==`.
  let a = (S8cKey(k), 1)
  let b = (S8cKey(3), 1)
  if k == 13 and a == b:
    symexTarget("s8c_tupeq")

proc s8cBuiltinPlus(a, b: int) =
  ## Control: the builtin `+` stays the builtin model.
  if a == 0 and b == 0 and a + b == 1:
    symexTarget("s8c_builtin_plus")

proc s8cBuiltinStrContains(s: string) =
  ## Control: `strutils.contains` reaches no user routine and keeps its model.
  if "xy" in s and s.len < 2:
    symexTarget("s8c_builtin_strcontains")

# --- strutils.replace: every occurrence, not the first ----------------------
# The `replaceAll` model was reachable only through a user proc of that name
# (no stdlib `replaceAll` exists); the resolved `strutils.replace` was
# modelled FIRST-occurrence. Nim's `replace` replaces every occurrence.

proc s8cReplaceFirst(s: string) =
  ## Real: "foofoo".replace("foo","bar") is "barbar" -- unreachable.
  if s == "foofoo" and s.replace("foo", "bar") == "barfoo":
    symexTarget("s8c_replace_first")

proc s8cReplaceAll(s: string) =
  ## Real: reachable with s == "foofoo".
  if s == "foofoo" and s.replace("foo", "bar") == "barbar":
    symexTarget("s8c_replace_all")

proc s8cReplaceEmptySub(s: string) =
  ## Real: an empty `sub` returns `s` unchanged (strutils: `if subLen == 0:
  ## result = s`) -- unreachable. Z3's first-occurrence `replace` PREPENDS
  ## `by` for an empty pattern.
  if s.replace("", "x") != s:
    symexTarget("s8c_replace_empty_sub")

proc s8cReplaceChar(s: string) =
  ## Real: the char overload replaces every occurrence -- "aa" -> "bb".
  if s == "aa" and s.replace('a', 'b') == "ba":
    symexTarget("s8c_replace_char")

# =============================================================================
# Tests
# =============================================================================

suite "RFC-0005 S8c -- a user overload is walked, not modelled as the builtin":

  test "user `+` on a distinct int: reachable through the fee (was a false sxUnsat)":
    let r = symexFind(s8cPlus, tLabel("s8c_plus"))
    dump(r.errors)
    check r.status == sxSat

  test "user `<` on a distinct int: unreachable (was a false sxSat)":
    let r = symexFind(s8cLess, tLabel("s8c_less"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user prefix `-` on a distinct int: reachable (was a false sxUnsat)":
    let r = symexFind(s8cNeg, tLabel("s8c_neg"))
    dump(r.errors)
    check r.status == sxSat

  test "user `+=` on a distinct int: unreachable (was a false sxSat)":
    let r = symexFind(s8cAugAssign, tLabel("s8c_augassign"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user `inc` on a distinct int: unreachable (pin: already walked pre-S8c)":
    let r = symexFind(s8cInc, tLabel("s8c_inc"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user `==` on an object: reachable (was a false sxUnsat)":
    let r = symexFind(s8cEq, tLabel("s8c_eq"))
    dump(r.errors)
    check r.status == sxSat

  test "`!=` resolves through the user `==` too":
    let r = symexFind(s8cNe, tLabel("s8c_ne"))
    dump(r.errors)
    check r.status == sxSat

  test "user non-generic `contains` beats sets.contains: unreachable (was a false sxSat)":
    let r = symexFind(s8cContains, tLabel("s8c_contains"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user non-generic `len` beats system.len: unreachable (was a false sxSat)":
    let r = symexFind(s8cLen, tLabel("s8c_len"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user non-generic `items` beats system.items: reachable (was a false sxUnsat)":
    let r = symexFind(s8cItems, tLabel("s8c_items"))
    dump(r.errors)
    check r.status != sxUnsat
    check r.status == sxSat

  test "a user `converter` is walked (was declined as an unsupported expression)":
    let r = symexFind(s8cConverter, tLabel("s8c_converter"))
    dump(r.errors)
    check r.status == sxSat

  test "user non-generic `add` beats system.add: reachable (was a false sxUnsat)":
    let r = symexFind(s8cAdd, tLabel("s8c_add"))
    dump(r.errors)
    check r.status == sxSat

  test "user string-receiver `find`: unreachable (was a false sxSat)":
    let r = symexFind(s8cFind, tLabel("s8c_find"))
    dump(r.errors)
    check r.status == sxUnsat

  test "a user proc named `symexAssume` is not the marker: reachable (was a false sxUnsat)":
    let r = symexFind(s8cForeignAssume, tLabel("s8c_foreign_assume"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == 2

suite "RFC-0005 S8c -- strutils.replace is the all-occurrences model":
  test "replace is not first-occurrence (was a false sxSat)":
    let r = symexFind(s8cReplaceFirst, tLabel("s8c_replace_first"))
    dump(r.errors)
    check r.status != sxSat

  test "replace reaches the all-occurrences value":
    let r = symexFind(s8cReplaceAll, tLabel("s8c_replace_all"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == "foofoo"

  test "an empty sub returns s unchanged: clean sxUnsat (was a false sxSat)":
    let r = symexFind(s8cReplaceEmptySub, tLabel("s8c_replace_empty_sub"))
    dump(r.errors)
    check r.status == sxUnsat
    check r.errors.len == 0

  test "the char overload replaces every occurrence (never a false sxSat)":
    let r = symexFind(s8cReplaceChar, tLabel("s8c_replace_char"))
    dump(r.errors)
    check r.status != sxSat

suite "RFC-0005 S8c -- a stdlib generic over a user routine: closed by the element fragment":
  ## The SECOND-order shape: the resolved callee IS the stdlib routine, but
  ## its instantiated body reaches a USER routine (`system.==` over a tuple /
  ## object / seq compares elements with the user's `==`; `sets.contains`
  ## hashes and compares keys with the user's `hash`/`==`). Every builtin
  ## model that depends on element semantics admits only element types whose
  ## `==` cannot be user-overloaded (int64 / string / float -- a same-
  ## signature overload is an ambiguity error); every other element type is
  ## already declined, RECORDED, by the fragment. These pins hold that line:
  ## widening a fragment (say, `HashSet[distinct int]`) without resolving the
  ## element ops turns one of them into a false verdict.

  test "system.== over an object with a user-`==` field: sxUnknown, recorded":
    let r = symexFind(s8cFieldEq, tLabel("s8c_field_eq"))
    dump(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOp)

  test "system.== over a tuple with a user-`==` element: sxUnknown, recorded":
    let r = symexFind(s8cTupEq, tLabel("s8c_tupeq"))
    dump(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOp)

  test "system.== over a seq of a user-`==` element: sxUnknown, recorded":
    let r = symexFind(s8cSeqEq, tLabel("s8c_seqeq"))
    dump(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(seNestedSeqUnsupported)

  test "sets.contains over a key with a user `==`/`hash`: sxUnknown, recorded":
    let r = symexFind(s8cSetKey, tLabel("s8c_setkey"))
    dump(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedWitnessType)

suite "RFC-0005 S8c -- controls: the builtin models still apply to builtins":

  test "builtin `+` on int keeps its model (clean sxUnsat)":
    let r = symexFind(s8cBuiltinPlus, tLabel("s8c_builtin_plus"))
    dump(r.errors)
    check r.status == sxUnsat

  test "strutils.contains keeps its model (clean sxUnsat)":
    let r = symexFind(s8cBuiltinStrContains, tLabel("s8c_builtin_strcontains"))
    dump(r.errors)
    check r.status == sxUnsat

suite "RFC-0005 S8c -- walker version pin":

  test "walker version floor >= 150 (S8c: callee resolution by symbol)":
    check parseInt(symexWalkerVersion) >= 150
