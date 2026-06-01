## Layer 2 of the predicate DSL (ADR-0002): typedesc → Z3 family.
##
## In Phase 1 the supported Nim types are exactly `int` and `bool`,
## mapping respectively to `Z3BitVec[Phase1IntWidth]` and `Z3Bool`.
## This file is the single point that classifies a Nim type into an
## `IRTypeKind`; the parser and the runtime both consult it.
##
## The bridge runs at macro time: callers pass a typedesc NimNode and
## get back an `IRTypeKind` (or raise a macro-time error). Later
## phases will return a richer family discriminator covering object,
## tuple, array, seq, Table, HashSet, etc.

import std/macros
import std/strutils
import ./types

proc classifyType*(ty: NimNode): IRTypeKind =
  ## Map a typed-AST type node to an IR type kind.
  ## Raises (at macro time) for unsupported types.
  let resolved = ty.getTypeInst
  let s = resolved.repr.strip
  case s
  of "int":  itInt
  of "bool": itBool
  else:
    error("symex (Phase 1): unsupported parameter type `" & s &
          "`; the supported fragment is {int, bool}.", ty)
