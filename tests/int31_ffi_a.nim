## Helper for `tsymex_0016_int31_keyholes.nim` (INT-31, W-18): the SUT is
## the same in each `int31_ffi_*` module; only the C body behind its
## `importc` callee differs (`int31_ffi_b`'s ends the process). The SUT's
## witness renders lossily (`Lossy.junk` is not a modelled field), so even a
## clean path to the label is settled by a replay, which runs the C body.
import nelli
import nelli/symex

type Lossy* = ref object
  x*: int
  junk*: seq[seq[int]]

{.emit: """#include <stdlib.h>
static void int31Set(void) { (void)0; }""".}
proc setF() {.importc: "int31Set", nodecl, symexTransparent.}

proc sutF*(r: Lossy; x: int) =
  if r != nil and x == 42:
    setF()
    symexTarget("k")
