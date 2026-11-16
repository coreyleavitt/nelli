## RFC-0016 0.10.0 review D3a. The opaque-body scan's undefined-behaviour
## deposit policy is `smt/ub_deposit.nim`, a pure function of (magic, operand
## width class, definedness profile). This pins its table with literal inputs
## (the behaviour D1 S3, F1 and W3-z P1 fixed, unchanged), and a census that
## the parser keeps only the traversal: it names no `UbKind` member and no
## `arithUb` row lookup.
import std/[unittest, os, strutils, options]
import nelli/smt/admission
import nelli/smt/definedness
import nelli/smt/errorkind
import nelli/smt/ub_deposit

const
  sOv = UbKind(ubSignedOverflow)
  sDz = UbKind(ubSignedDivZero)
  mMin = UbKind(ubIntMinModMinusOne)
  uDz = UbKind(ubUnsignedDivZero)

type Row = tuple[magic: string, narrow: bool,
                 checked, unchecked, fwrapv: set[UbKind]]

const rows: seq[Row] = @[
  # add/sub/mul and the other overflow magics: the signed wide wrap only.
  ("AddI", false, {}, {sOv}, {}),
  ("AddI", true, {}, {}, {}),
  ("SubI", false, {}, {sOv}, {}),
  ("MulI", false, {}, {sOv}, {}),
  ("MulI", true, {}, {}, {}),
  ("UnaryMinusI", false, {}, {sOv}, {}),
  # div: a signed zero divisor is undefined once the checks are off, at any
  # width and under -fwrapv; low(T) div -1 only at 32/64 bits, -fwrapv or not.
  ("DivI", false, {}, {sDz, sOv}, {sDz, sOv}),
  ("DivI", true, {}, {sDz}, {sDz}),
  # mod: low(T) mod -1 has no Nim check, so it is undefined when checked too.
  ("ModI", false, {mMin}, {sDz, sOv, mMin}, {sDz, mMin}),
  ("ModI", true, {}, {sDz}, {sDz}),
  # unsigned division: undefined under every profile, width-independent.
  ("DivU", false, {uDz}, {uDz}, {uDz}),
  ("ModU", true, {uDz}, {uDz}, {uDz}),
  # a magic with no arithmetic deposit.
  ("nextafter", false, {}, {}, {}),
  ("", false, {}, {}, {})]

proc kindsOf(magic: string; narrow: bool; prof: DefProfile): set[UbKind] =
  ## The kinds `arithDeposits` names, read from its rows (the one source of
  ## truth: a deposit is an admitted row undefined under its own profile).
  for d in arithDeposits(magic, narrow, prof):
    check d.row.admitted
    check d.profile == prof
    result.incl ubOf(d.row.payload[prof]).get

suite "D3a: ub_deposit policy table":
  test "kinds per (magic, width, profile)":
    for r in rows:
      checkpoint r.magic & " narrow=" & $r.narrow
      check kindsOf(r.magic, r.narrow, dpChecked) == r.checked
      check kindsOf(r.magic, r.narrow, dpUnchecked) == r.unchecked
      check kindsOf(r.magic, r.narrow, dpFwrapv) == r.fwrapv

suite "D3a: the parser keeps only the traversal":
  test "dsl_parser.nim names no UbKind member and no arithUb lookup":
    let root = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt"
    var code: seq[string]
    for line in readFile(root / "dsl_parser.nim").splitLines:
      let t = line.strip
      if not t.startsWith("#"):
        code.add (if "#" in line: line.split('#')[0] else: line)
    let text = code.join("\n")
    check "arithUb" notin text
    # every UbKind member's name, from the enum itself
    for k in low(UbKind) .. high(UbKind):
      let nm = $k
      checkpoint nm
      check nm.len == 0 or not text.contains(nm)
