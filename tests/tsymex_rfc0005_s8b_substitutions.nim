## RFC-0005 (soundness channels) slice S8b -- three pre-existing SILENT
## SUBSTITUTIONS (§2.2's class: a site substitutes behaviour without recording
## anything, so the engine claims a verdict it has not earned). Each was a
## false verdict with no error behind it:
##   (a) a call to a bodiless `{.importc.}` proc was registered and walked as
##       an EMPTY body -- its result the zero default -- so a target reachable
##       only through the foreign result was a false `sxUnsat` with zero
##       errors. It is now the opaque effect it is (`feOpaqueCallUnmodelled`,
##       `dcSubstituted`): the call binds a fresh result and taints the path.
##   (b) `parseInt`'s digits continuation excluded every `+`-prefixed string
##       (Z3's `str.to_int` rejects the sign Nim's `rawParseInt` accepts), so
##       a target reachable only via `parseInt("+5")` was a false `sxUnsat`;
##       and an out-of-range literal (`"9223372036854775808"`) parsed to an
##       unbounded Int instead of raising `ValueError`. The model now follows
##       `parseutils.rawParseInt` exactly for every string without a `_`; a
##       `_`-separated string (whose value would need `str.replace_all`, which
##       not every supported Z3 has) continues on a replay-gated fresh value
##       instead of being dropped.
##   (c) `exn_hierarchy.nim` flattened `ArithmeticDefect` out of Nim's tree,
##       so `except ArithmeticDefect` never caught `DivByZeroDefect` /
##       `OverflowDefect` -- a false `sxRaised` (the handler's target was
##       never reached, the defect escaped instead). The table is now audited
##       against the compiler's own `lib/system/exceptions.nim`.
## Walker 148 -> 149.
import std/[unittest, strutils, tables, compilesettings, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/exn_hierarchy

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc dump(errs: seq[SymexErrorInfo]) =
  for e in errs: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)

# =============================================================================
# SUTs -- (a) bodiless importc
# =============================================================================

proc s8bCAbs(x: int32): int32 {.importc: "abs", header: "<stdlib.h>".}
  ## A real libc symbol, so the SUT links (S10's replay contract).

proc s8bCSrand(seed: uint32) {.importc: "srand", header: "<stdlib.h>".}

proc s8bCSrandTransparent(seed: uint32)
  {.importc: "srand", header: "<stdlib.h>", symexTransparent.}

proc s8bCAbsOpaque(x: int32): int32
  {.importc: "abs", header: "<stdlib.h>", symexOpaque.}

proc s8bImportcLive(x: int32) =
  ## Reachable for real (x = 7 or -7). The empty-body walk returned 0.
  if s8bCAbs(x) == 7:
    symexTarget("s8b_importc_live")

proc s8bImportcInert(n: int) =
  ## Statement position, value arguments: the #163 inert opaque rule applies
  ## to a foreign call as to any opaque one -- a no-op, no taint.
  s8bCSrand(1)
  if n == 42:
    symexTarget("s8b_importc_inert")

proc s8bImportcTransparent(n: int) =
  s8bCSrandTransparent(1)
  if n == 42:
    symexTarget("s8b_importc_transparent")

proc s8bImportcOpaque(x: int32) =
  if s8bCAbsOpaque(x) == 7:
    symexTarget("s8b_importc_opaque")

# =============================================================================
# SUTs -- (b) parseInt
# =============================================================================

proc s8bParsePlus(s: string) =
  ## Nim: parseInt("+5") == 5. Reachable only through the `+` sign.
  let n = parseInt(s)
  if n == 5 and s.len == 2 and s[0] == '+':
    symexTarget("s8b_parse_plus")

proc s8bParseNegZero(s: string) =
  ## Nim: parseInt("-0") == 0 (a `-` followed by digits, value 0).
  let n = parseInt(s)
  if n == 0 and s.len == 2:
    symexTarget("s8b_parse_negzero")

proc s8bParseOverflow(s: string) =
  ## Nim raises ValueError ("Parsed integer outside of valid range") for
  ## 2^63; the old model parsed it to an unbounded Int and never raised.
  if s == "9223372036854775808":
    discard parseInt(s)

proc s8bParseLowInt(s: string) =
  ## -2^63 is in range: Nim parses it (the asymmetric bound).
  if s == "-9223372036854775808":
    let n = parseInt(s)
    if n < 0:
      symexTarget("s8b_parse_lowint")

proc s8bParseHighInt(s: string) =
  ## 2^63 - 1 is in range.
  if s == "9223372036854775807":
    let n = parseInt(s)
    if n > 0:
      symexTarget("s8b_parse_highint")

proc s8bParseBareSign(s: string) =
  ## A lone sign has no digits: Nim raises.
  if s == "+":
    discard parseInt(s)

proc s8bParseDoubleSign(s: string) =
  ## Only ONE sign is consumed: "+-5" raises.
  if s == "+-5":
    discard parseInt(s)

proc s8bParseSpace(s: string) =
  ## No whitespace is skipped: " 5" raises.
  if s == " 5":
    discard parseInt(s)

proc s8bParseUnderscoreLive(s: string) =
  ## Nim: parseInt("1_0") == 10. The old digits continuation excluded every
  ## string containing `_`.
  let n = parseInt(s)
  if s == "1_0" and n == 10:
    symexTarget("s8b_parse_underscore")

# =============================================================================
# SUTs -- (c) exception hierarchy
# =============================================================================

proc s8bArithDivCaught(a, b: int) =
  try:
    let q = a div b
    discard q
  except ArithmeticDefect:
    symexTarget("s8b_arith_div_caught")

proc s8bArithOvfCaught(a, b: int) =
  try:
    let c = a + b
    discard c
  except ArithmeticDefect:
    symexTarget("s8b_arith_ovf_caught")

type S8bArithAlias = ArithmeticDefect
  ## A user alias of a stdlib exception type.

proc s8bArithUserAlias(a, b: int) =
  try:
    let q = a div b
    discard q
  except S8bArithAlias:
    symexTarget("s8b_arith_user_alias")

{.push warning[Deprecated]: off.}
proc s8bArithDeprecatedAlias(a, b: int) =
  ## `DivByZeroError` is system's deprecated alias of `DivByZeroDefect`.
  try:
    let q = a div b
    discard q
  except DivByZeroError:
    symexTarget("s8b_arith_deprecated_alias")
{.pop.}

proc s8bArithNoCatchValue(a, b: int) =
  ## ArithmeticDefect is a Defect, not a CatchableError: `except
  ## CatchableError` must NOT catch a DivByZeroDefect.
  try:
    let q = a div b
    discard q
  except CatchableError:
    symexTarget("s8b_arith_catchable")

# =============================================================================
# (a) importc
# =============================================================================

suite "RFC-0005 S8b (a) -- a bodiless importc callee is an opaque effect, not an empty body":

  test "live target through the foreign result: not sxUnsat, and says why":
    let r = symexFind(s8bImportcLive, tLabel("s8b_importc_live"))
    dump(r.errors)
    check r.status != sxUnsat
    check r.status == sxUnknown
    check r.errors.hasKind(feOpaqueCallUnmodelled)

  test "the failure is named: the message carries the importc callee":
    let r = symexFind(s8bImportcLive, tLabel("s8b_importc_live"))
    var named = false
    for e in r.errors:
      if e.kind == feOpaqueCallUnmodelled and "s8bCAbs" in e.msg: named = true
    check named

  test "statement-position inert foreign call stays a no-op (clean sxSat)":
    let r = symexFind(s8bImportcInert, tLabel("s8b_importc_inert"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == 42

  test "{.symexTransparent.} importc keeps working (dropped, clean sxSat)":
    let r = symexFind(s8bImportcTransparent, tLabel("s8b_importc_transparent"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == 42
    check not r.errors.hasKind(feOpaqueCallUnmodelled)

  test "{.symexOpaque.} importc keeps its opaque treatment":
    let r = symexFind(s8bImportcOpaque, tLabel("s8b_importc_opaque"))
    check r.status == sxUnknown
    check r.errors.hasKind(feOpaqueCallUnmodelled)

  test "feOpaqueCallUnmodelled is dcSubstituted (the class the site's substitution earns)":
    check classOf(feOpaqueCallUnmodelled) == dcSubstituted

# =============================================================================
# (b) parseInt
# =============================================================================

suite "RFC-0005 S8b (b) -- parseInt follows parseutils.rawParseInt":

  test "\"+5\" parses to 5: the target is reachable (clean sxSat)":
    let r = symexFind(s8bParsePlus, tLabel("s8b_parse_plus"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == "+5"

  test "\"-0\" parses to 0":
    let r = symexFind(s8bParseNegZero, tLabel("s8b_parse_negzero"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0].len == 2
    check parseInt(r.witness[0]) == 0

  test "2^63 raises ValueError (out of range), a clean sxRaised":
    let r = symexFind(s8bParseOverflow, tRaisedExn("ValueError"))
    dump(r.errors)
    check r.status == sxRaised
    check r.raisedWitness[0] == "9223372036854775808"

  test "-2^63 is in range: parsed, reachable":
    let r = symexFind(s8bParseLowInt, tLabel("s8b_parse_lowint"))
    dump(r.errors)
    check r.status == sxSat

  test "2^63 - 1 is in range: parsed, reachable":
    let r = symexFind(s8bParseHighInt, tLabel("s8b_parse_highint"))
    dump(r.errors)
    check r.status == sxSat

  test "a lone sign raises, clean":
    let r = symexFind(s8bParseBareSign, tRaisedExn("ValueError"))
    check r.status == sxRaised

  test "a double sign raises, clean":
    let r = symexFind(s8bParseDoubleSign, tRaisedExn("ValueError"))
    check r.status == sxRaised

  test "leading whitespace raises, clean":
    let r = symexFind(s8bParseSpace, tRaisedExn("ValueError"))
    check r.status == sxRaised

  test "\"1_0\" continues (replay-gated fresh value): never a false sxUnsat":
    let r = symexFind(s8bParseUnderscoreLive, tLabel("s8b_parse_underscore"))
    dump(r.errors)
    checkpoint "status: " & $r.status
    check r.status != sxUnsat
    check r.errors.hasKind(seParseIntLaxSyntax)

  test "oracle: the real parseInt agrees with every pin above":
    check parseInt("+5") == 5
    check parseInt("-0") == 0
    check parseInt("1_0") == 10
    check parseInt("-9223372036854775808") == low(int)
    check parseInt("9223372036854775807") == high(int)
    for bad in ["9223372036854775808", "+", "-", "+-5", " 5", "", "5 "]:
      expect ValueError:
        discard parseInt(bad)

# =============================================================================
# (c) exception hierarchy
# =============================================================================

suite "RFC-0005 S8b (c) -- except ArithmeticDefect catches its subtypes":

  test "DivByZeroDefect is caught by `except ArithmeticDefect` (was a false sxRaised)":
    let r = symexFind(s8bArithDivCaught, tLabel("s8b_arith_div_caught"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[1] == 0

  test "OverflowDefect is caught by `except ArithmeticDefect`":
    let r = symexFind(s8bArithOvfCaught, tLabel("s8b_arith_ovf_caught"))
    dump(r.errors)
    check r.status == sxSat

  test "a user alias of ArithmeticDefect catches DivByZeroDefect":
    let r = symexFind(s8bArithUserAlias, tLabel("s8b_arith_user_alias"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[1] == 0

  test "system's deprecated alias (DivByZeroError) catches DivByZeroDefect":
    let r = symexFind(s8bArithDeprecatedAlias, tLabel("s8b_arith_deprecated_alias"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[1] == 0

  test "`except CatchableError` does not catch a DivByZeroDefect":
    let r = symexFind(s8bArithNoCatchValue, tLabel("s8b_arith_catchable"))
    check r.status != sxSat

# ---- the audit: the table against the compiler's own source -----------------

const nimLib = querySetting(libPath)
const nimExceptionsSrc = staticRead(nimLib / "system" / "exceptions.nim")
const nimSystemSrc = staticRead(nimLib / "system.nim")

proc nimExceptionParents(): Table[string, string] =
  ## `child -> direct parent` for every `X* = object of Y` / `X* {.….} =
  ## object of Y` declaration in Nim's own system sources.
  for src in [nimSystemSrc, nimExceptionsSrc]:
    for raw in src.splitLines:
      let line = raw.strip
      let at = line.find("= object of ")
      if at < 0: continue
      var lhs = line[0 ..< at].strip
      let brace = lhs.find("{.")
      if brace >= 0: lhs = lhs[0 ..< brace].strip
      if not lhs.endsWith("*"): continue
      let child = lhs[0 ..< lhs.high]
      var parent = line[at + "= object of ".len .. ^1]
      let cut = parent.find({' ', '#'})
      if cut >= 0: parent = parent[0 ..< cut]
      result[child] = parent

proc nimExceptionChains(): Table[string, seq[string]] =
  ## Every type whose ancestry reaches `Exception`, with its full chain
  ## (nearest parent first) -- the shape of `exnTypeTable`.
  let parents = nimExceptionParents()
  for t in parents.keys:
    var chain: seq[string]
    var cur = t
    while cur in parents and cur != "Exception":
      cur = parents[cur]
      chain.add cur
    if t == "Exception" or (chain.len > 0 and chain[^1] == "Exception"):
      result[t] = (if t == "Exception": @[] else: chain)

suite "RFC-0005 S8b (c) -- exnTypeTable audited against Nim's system hierarchy":

  test "the audit parsed a plausible hierarchy (guards the scraper itself)":
    let real = nimExceptionChains()
    check "Exception" in real
    check real.getOrDefault("KeyError") == @["ValueError", "CatchableError", "Exception"]
    check real.getOrDefault("DivByZeroDefect") == @["ArithmeticDefect", "Defect", "Exception"]
    check real.len >= 30

  test "every Nim exception type is in the table, with its REAL chain":
    let real = nimExceptionChains()
    var missing, wrong: seq[string]
    for t, chain in real:
      if t notin exnTypeTable: missing.add t
      elif exnTypeTable[t] != chain:
        wrong.add t & ": table " & $exnTypeTable[t] & " vs nim " & $chain
    checkpoint "missing: " & $missing
    checkpoint "wrong: " & $wrong
    check missing.len == 0
    check wrong.len == 0

  test "every table entry is a real Nim type (one legacy spelling, named)":
    const legacySpellings = ["OutOfMemoryDefect"]
      ## Not a Nim type: the RFC/checklist spelling of `OutOfMemDefect`,
      ## resolved to the same chain so a SUT written against it classifies.
    let real = nimExceptionChains()
    var extra: seq[string]
    for t in exnTypeTable.keys:
      if t notin real and t notin legacySpellings: extra.add t
    checkpoint "extra: " & $extra
    check extra.len == 0
    check exnTypeTable["OutOfMemoryDefect"] == exnTypeTable["OutOfMemDefect"]

  test "isSubtypeOf follows the real tree for the arithmetic family":
    let none = initTable[string, string]()
    check isSubtypeOf("DivByZeroDefect", "ArithmeticDefect", exnTypeTable, none)
    check isSubtypeOf("OverflowDefect", "ArithmeticDefect", exnTypeTable, none)
    check isSubtypeOf("FloatDivByZeroDefect", "FloatingPointDefect", exnTypeTable, none)
    check not isSubtypeOf("FloatDivByZeroDefect", "ArithmeticDefect", exnTypeTable, none)
    check not isSubtypeOf("DivByZeroDefect", "CatchableError", exnTypeTable, none)
    check isDefect(exnTypeTable, "ArithmeticDefect")
    check isDefect(exnTypeTable, "FloatInexactDefect")

# =============================================================================
# walker version floor
# =============================================================================

suite "RFC-0005 S8b -- walker version pin":

  test "walker version floor >= 149 (S8b: three silent substitutions)":
    check parseInt(symexWalkerVersion) >= 149
