## RFC-0016 K8a-sink (§10): ONE ROUND of the real reduction oracle. Not a
## suite: `scripts/k8a-sink.sh` compiles and runs it per round (a candidate
## list is compile-time, so a round is one compile) and feeds the result back
## as the next round's `-d:k8aStart`.
##
##   -d:k8aSeed=N -d:k8aProgId=N -d:k8aVariant=name   the finding (round 1)
##   -d:k8aStart=<encodeCase text>                    the previous round's pick
##
## Every candidate of the start case (`candidates`) runs under its own
## variant and, when it has a twin, the original too; `findings` is the
## disagreement test, exactly as the generator's own suite applies it. Output:
##   K8ARED-CASE <encoded case>   the first candidate that still disagrees,
##                                or the start case unchanged
##   K8ARED-CHANGED 0|1
##   K8ARED-PAIR <verdict pair>   of that disagreement (empty if unchanged)
##   K8ARED-SRC-BEGIN .. K8ARED-SRC-END   the case's source
import std/[strutils]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8a_sink

const
  k8aSeed {.intdefine.} = 20261108
  k8aProgId {.intdefine.} = 0
  k8aVariant {.strdefine.} = "orig"
  k8aStart {.strdefine.} = ""

func startCase(): Case =
  if k8aStart.len > 0: return decodeCase(k8aStart)
  result.prog = genPrograms(k8aSeed, k8aProgId + 1)[k8aProgId]
  for t in Twin:
    if twinName(t) == k8aVariant: result.tw = t

const start = startCase()
const cands = candidates(start)

genCases(roundCases(cands), false, "red")

let outs = runBatch_red()
var hit = -1
var pair = ""
for i, c in cands:
  var p = c.prog
  p.id = i
  var mine: seq[GenOutcome]
  for o in outs:
    if o.progId == i: mine.add o
  let fs = findings(@[p], mine, k8aSeed)
  if fs.len > 0 and hit < 0:
    hit = i
    pair = verdictPair(fs[0])
let final = if hit >= 0: cands[hit] else: start
echo "K8ARED-CASE ", encodeCase(final)
echo "K8ARED-CHANGED ", (if hit >= 0: 1 else: 0)
echo "K8ARED-PAIR ", pair
echo "K8ARED-SRC-BEGIN"
var fp = final.prog
fp.id = 0
echo render(fp, "reduced", final.tw)
echo "K8ARED-SRC-END"
