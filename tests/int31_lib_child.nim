## Child of `tsymex_0016_int31_libkey.nim` (INT-31, the `lib/` hole). Built
## twice by the suite, each time against its own copy of the toolchain's
## `lib/` (`--lib:`); the copies differ only in `math.ceilDiv`'s body. Run
## against a database directory both builds share, it reports each finding as
## one line: whether it came from the cache, and whether its witness reaches
## the label natively in THIS build.
import std/[math, os]
import nelli
import nelli/symex
import nelli/db

proc sut(x: uint8) =
  if ceilDiv(x, 1'u8) == 41'u8:
    symexTarget("lib")

proc firstInt(f: SymexFinding): int =
  for n in f.witnessChoices:
    if n.kind == ckInteger: return int(n.intVal.toInt64)
  -1

let store = directoryBasedDatabase(paramStr(1))
for f in symexFindAllWitnesses(sut, store):
  let x = firstInt(f)
  let hits = x in 0 .. 255 and ceilDiv(uint8(x), 1'u8) == 41'u8
  echo "FINDING target=", f.targetDesc, " status=", f.status,
    " fromCache=", f.fromCache,
    " unsafe=", f.soundness.witnessUnsafe, " x=", x, " hits=", hits,
    " gaps=", f.gaps, " runTaint=", f.soundness.runTaint
