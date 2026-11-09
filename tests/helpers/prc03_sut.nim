## PRC-02 probe 3. The SUT module imports the override module without exporting
## it, so the test entry cannot see the override that its dispatcher still runs.
import nelli
import nelli/symex
import prc03_types
import prc03_over

var gHidden*: int

proc runHidden(v: int) {.symexOpaque.} =
  let b: Base = Sub()
  gHidden = area(b, v)

proc sutHidden*(v: int) =
  symexAssume(v == 3)
  runHidden(v)
  if gHidden == 4: symexTarget("t")
