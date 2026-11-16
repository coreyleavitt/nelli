## RFC-0016 0.10.0 review D3a. The undefined-behaviour kinds an arithmetic
## magic deposits when it is reached in the body of an opaque routine, as a
## pure function of its inputs: the magic, whether its operand is narrower
## than a C `int`, and the definedness column the routine's owner compiles
## under. The parser's opaque-body scan (`scanOpaqueDefects`) walks the tree
## and gathers those three values; this module is the whole policy, so the
## decision is testable with literal inputs and the traversal names no kind.
##
## Each deposit is the definedness table's admitted `dsArith` row, which
## `noteUndefined` turns into the kind under the profile; the row is returned
## only where that kind is undefined (a Defect or a defined wrap deposits
## nothing here: the Defect answer is the defect scan's, not this one's).
import std/options
import ./admission
import ./definedness
import ./magic_rows

const unsignedDivMagics = ["DivU", "ModU"]
  ## RFC-0016 K10b. The unsigned division magics: no zero-divisor row on the
  ## magic axis (K4a-guard: the C division is undefined, not a Defect), so
  ## under the gate they answer through the definedness axis's
  ## `div/zeroDivisorUnsigned` row.

type ArithDeposit* = object
  ## One deposit: the admitted row and the column it is undefined under.
  row*: Admit[DefRule]
  profile*: DefProfile

func isModMagic(magic: string): bool =
  magic.len >= 3 and magic[0 .. 2] == "Mod"

func arithDeposits*(magic: string; narrow: bool;
                    prof: DefProfile): seq[ArithDeposit] =
  ## The rows `magic` deposits at an operand narrower than `int` (`narrow`:
  ## int8, int16) or not, under `prof`. D1 S3: the class follows the width, as
  ## `wrapDefined` does; a signed zero divisor stays undefined at every width.
  ## Review F1: every kind is the table's answer under `prof`, never a guard
  ## written here (`-fwrapv` defines the signed wrap only).
  template deposit(op: ArithOp; c: OperandClass) =
    let row = admitDefined(op, c, dsArith)
    if ubOf(definedness(op, c, prof)).isSome:
      result.add ArithDeposit(row: row, profile: prof)
  if admitMagic(magic, msDefOverflow).admitted:
    deposit(aoAdd, arithClass(not narrow))
  if admitMagic(magic, msDefDivZero).admitted:
    let op = if isModMagic(magic): aoMod else: aoDiv
    deposit(op, ocZeroDivisorSigned)
    deposit(op, if narrow: ocLowByMinusOneNarrow else: ocLowByMinusOneWide)
  if magic in unsignedDivMagics:
    deposit(aoDiv, ocZeroDivisorUnsigned)
