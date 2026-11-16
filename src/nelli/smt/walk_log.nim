## RFC-0016 review D3b: the walk-units log, the one owner of its I/O.
##
## The walker counts the units a walk spends and hands them here as data
## (`WalkUnitsLine`); it opens no file and reads no environment variable.
## This module owns the destination (`NELLI_WALK_UNITS_LOG`), the line format
## and the write. Off when the variable is unset.
##
## Append mode and one write per line, so concurrent test processes interleave
## whole lines. This is how `walkRLimit`'s default is measured (the maximum
## over the corpus); `scripts/dt-bounded.sh` forwards the variable into the
## container.

from std/os import getEnv

const walkUnitsLogEnv* = "NELLI_WALK_UNITS_LOG"

type
  WalkUnitsLine* = object
    ## One finished walk. `units` is everything it spent (its Z3 checks and
    ## the walker-side charge, the budget `walkRLimit` bounds). `walkerUnits`
    ## is the part of `units` that is the walker-side charge (`units -
    ## walkerUnits` is the Z3 share); `hasWalkerUnits` is false for the K10b
    ## tail walk's line, which carries no such column.
    units*: int
    target*: string
    status*: string
    walkerUnits*: int
    hasWalkerUnits*: bool

proc walkUnitsLogPath*(): string =
  ## The log file the environment names; empty when logging is off.
  getEnv(walkUnitsLogEnv)

proc renderWalkUnits*(l: WalkUnitsLine): string =
  ## The bytes of one line, newline included.
  result = $l.units & "\t" & l.target & "\t" & l.status
  if l.hasWalkerUnits: result.add "\t" & $l.walkerUnits
  result.add "\n"

proc appendWalkUnits*(l: WalkUnitsLine) =
  ## Appends `l` to the log the environment names. A failed open or write is
  ## dropped: the log is a measurement, never a verdict input.
  let path = walkUnitsLogPath()
  if path.len == 0: return
  try:
    var f: File
    if open(f, path, fmAppend):
      f.write(renderWalkUnits(l))
      f.close()
  except IOError, OSError:
    discard
