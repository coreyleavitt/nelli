## Helper for `tsymex_0016_int31_keyholes.nim` (INT-31, W-18): the SUT is
## the same in each `int31_pv_*` module; only the routine the global proc
## values hold differs (`int31_pv_b`'s ends the process). The SUT's witness
## renders lossily, so even a clean path to the label is settled by a
## replay, which runs the routine.
import nelli
import nelli/symex

type Lossy* = ref object
  x*: int
  junk*: seq[seq[int]]

proc setP() = discard

let fixedP*: proc () {.nimcall.} = setP
var slotP*: proc () {.nimcall.} = setP

proc sutL*(r: Lossy; x: int) =
  if r != nil and x == 42:
    fixedP()
    symexTarget("k")

proc sutV*(r: Lossy; x: int) =
  if r != nil and x == 42:
    slotP()
    symexTarget("k")
