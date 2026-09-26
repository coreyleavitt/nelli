## RFC-0005 (soundness channels) slice S8d -- silent substitution by
## NAME-classified type heads (§2.2's class, one level below S8c's callees).
## `classifyType` (`dsl_typebridge.nim`) and the parser's type-dependent arms
## recognised `seq`/`Table`/`HashSet`/`range`/`array`/`sink`/`lent`, the
## builtin scalar spellings (`int8`, `bool`, `Natural`, ...) and the
## `unicode.Rune` intercept by the type's NAME. A user type spelled the same
## way -- a user generic `seq`/`Table`/`HashSet`, a user alias `Natural = int`
## or `int8 = int`, a user `Rune`, a user enum named `bool` -- was modelled as
## the stdlib type, so the engine claimed `sxSat`/`sxUnsat` about semantics
## the program does not have, with nothing recorded.
##
## S8d resolves the type head by SYMBOL (`isStdlibTypeSym`): the stdlib model
## applies only when the head is a compiler builtin or is declared in Nim's
## `lib/` tree. A user type of the same name is classified by its structure
## like any other user type (an enum is an enum), or reaches the existing
## recorded decline for its shape (a user generic instance or plain alias is
## `feUnsupportedParamType`, as every other user generic/alias already is).
## Walker 150 -> 151.
import std/[unittest, strutils, sets, tables, options, unicode]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8d_user_types import s8dSeqLen, s8dTableLen, s8dSetLen, s8dOption,
  s8dNatural, s8dLowInt8, s8dRune, s8dBool

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc dump(errs: seq[SymexErrorInfo]) =
  for e in errs: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)

# =============================================================================
# Controls: the REAL stdlib types keep their models.
# =============================================================================

proc s8dRealSeqLen(s: seq[int]) =
  let n = s.len
  if n == 4:
    symexTarget("s8d_real_seq_len")

proc s8dRealTableLen(t: Table[string, int]) =
  let n = t.len
  if n == 4:
    symexTarget("s8d_real_table_len")

proc s8dRealSetLen(s: HashSet[int]) =
  let n = s.len
  if n == 4:
    symexTarget("s8d_real_set_len")

proc s8dRealNatural(x: Natural) =
  if x < 0:
    symexTarget("s8d_real_natural")

proc s8dRealLowInt8(x: int8) =
  if x < low(int8):
    symexTarget("s8d_real_low_int8")

proc s8dRealRune(r: Rune) =
  if int32(r) < 0:
    symexTarget("s8d_real_rune")

proc s8dRealBool(b: bool) =
  if b and not b:
    symexTarget("s8d_real_bool")

proc s8dRealOption(o: Option[int]) =
  if o.isSome:
    symexTarget("s8d_real_option")

# =============================================================================
# Tests
# =============================================================================

suite "RFC-0005 S8d -- a user type named like a stdlib type head is not the stdlib type":

  test "user generic `seq` (an array[3]): never a symbolic length (was a false sxSat)":
    let r = symexFind(s8dSeqLen, tLabel("s8d_seq_len"))
    dump(r.errors)
    check r.status != sxSat
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "user generic `Table` (an array[3]): not a hash table (was a false sxSat)":
    let r = symexFind(s8dTableLen, tLabel("s8d_table_len"))
    dump(r.errors)
    check r.status != sxSat
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "user generic `HashSet` (an array[3]): not a hash set (was a false sxSat)":
    let r = symexFind(s8dSetLen, tLabel("s8d_set_len"))
    dump(r.errors)
    check r.status != sxSat
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "user generic `Option`: the recorded user-generic decline (pin: no Option model exists)":
    let r = symexFind(s8dOption, tLabel("s8d_option"))
    dump(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "user alias `Natural = int`: not range[0..high(int)] (was a false sxUnsat)":
    let r = symexFind(s8dNatural, tLabel("s8d_natural"))
    dump(r.errors)
    check r.status != sxUnsat
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "user alias `int8 = int`: `low(int8)` is not -128 (was a false sxSat)":
    let r = symexFind(s8dLowInt8, tLabel("s8d_low_int8"))
    dump(r.errors)
    check r.status != sxSat
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedExprKind)

  test "user `Rune = distinct RuneImpl`: not a Unicode scalar (was a false sxUnsat)":
    let r = symexFind(s8dRune, tLabel("s8d_rune"))
    dump(r.errors)
    check r.status != sxUnsat
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "user enum named `bool`: its third member is reachable (was a false sxUnsat)":
    let r = symexFind(s8dBool, tLabel("s8d_bool"))
    dump(r.errors)
    check r.status == sxSat

suite "RFC-0005 S8d -- controls: the stdlib type heads keep their models":

  test "seq[int] length is symbolic":
    let r = symexFind(s8dRealSeqLen, tLabel("s8d_real_seq_len"))
    dump(r.errors)
    check r.status == sxSat

  test "Table[string, int] size is symbolic":
    let r = symexFind(s8dRealTableLen, tLabel("s8d_real_table_len"))
    dump(r.errors)
    check r.status == sxSat

  test "HashSet[int] cardinality is symbolic":
    let r = symexFind(s8dRealSetLen, tLabel("s8d_real_set_len"))
    dump(r.errors)
    check r.status == sxSat

  test "system.Natural excludes negatives (clean sxUnsat)":
    let r = symexFind(s8dRealNatural, tLabel("s8d_real_natural"))
    dump(r.errors)
    check r.status == sxUnsat

  test "system low(int8) folds to -128 (clean sxUnsat)":
    let r = symexFind(s8dRealLowInt8, tLabel("s8d_real_low_int8"))
    dump(r.errors)
    check r.status == sxUnsat

  test "unicode.Rune is pinned to [0, 0x10FFFF] (clean sxUnsat)":
    let r = symexFind(s8dRealRune, tLabel("s8d_real_rune"))
    dump(r.errors)
    check r.status == sxUnsat

  test "system.bool is two-valued (clean sxUnsat)":
    let r = symexFind(s8dRealBool, tLabel("s8d_real_bool"))
    dump(r.errors)
    check r.status == sxUnsat

  test "options.Option stays the recorded decline":
    let r = symexFind(s8dRealOption, tLabel("s8d_real_option"))
    dump(r.errors)
    check r.status == sxUnknown

suite "RFC-0005 S8d -- walker version pin":

  test "walker version floor >= 151 (S8d: type heads resolved by symbol)":
    check parseInt(symexWalkerVersion) >= 151
