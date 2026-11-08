## RFC-0016 K8a-job (§10): the three-way runner. One row per generated
## program (the original, no twins): the walker's verdict on THIS engine and
## the native result on THIS build. `scripts/k8a-nightly.sh` runs it twice on
## the same seed, once at head and once copied into a checkout of the last
## release tag, and joins the two outputs into the three-way table
## (release / head / native).
##
## PORTABLE ON PURPOSE. It uses only what an engine of the last release also
## has: `symexFind` with its default settings, `symexCaptureBegin/End`, and the
## generator's pure half (`genPrograms`, `render`, `domainElems`). It does not
## use the pin machinery (`pinExactImpl`, cells), which the release lacks. A
## release that cannot compile this file is itself the answer: the script
## records the release column as `compile-stop`.
##
## Output, one line per program, tab separated, after the `K8A3W` tag:
##   seed  prog  shape  type  walker  native
## `walker` is `<status> trusted|untrusted [raised type]`; `native` is `hit
## <input>`, `nohit` or `hit-raise <name>` (the first input that raises).
import std/[macros, sets]
import nelli
import nelli/symex
import ./s0016_k8a_gen

const
  k8aSeed {.intdefine.} = 20261108
  k8aCount {.intdefine.} = 6

macro emitThreeWay(progs: static seq[Prog]): untyped =
  var src = ""
  var runs = ""
  for p in progs:
    let name = procName("tw", p, twNone)
    src.add render(p, name, twNone)
    let dom = domainElems(p)
    runs.add "  block:\n" &
      "    let r = symexFind(" & name & ", tLabel(\"hit\"))\n" &
      "    var native = \"nohit\"\n" &
      "    var raised = \"\"\n" &
      "    for a in " & dom & ":\n" &
      "      for b in " & dom & ":\n" &
      "        symexCaptureBegin()\n" &
      "        var rz = \"\"\n" &
      "        try:\n" &
      "          " & name & "(a, b)\n" &
      "        except Defect as e:\n" &
      "          rz = $e.name\n" &
      "        except CatchableError as e:\n" &
      "          rz = $e.name\n" &
      "        let hs = symexCaptureEnd()\n" &
      "        if \"hit\" in hs and native == \"nohit\":\n" &
      "          native = \"hit (\" & $a & \",\" & $b & \")\"\n" &
      "        if rz.len > 0 and raised.len == 0: raised = rz & \" (\" & $a & \",\" & $b & \")\"\n" &
      "    if native == \"nohit\" and raised.len > 0: native = \"nohit raise \" & raised\n" &
      "    var w = $r.status & (if r.trusted: \" trusted\" else: \" untrusted\")\n" &
      "    if r.status == sxRaised: w.add \" \" & r.raisedTypeId\n" &
      "    echo \"K8A3W\\t\" & $" & $k8aSeed & " & \"\\t" & $p.id & "\\t" &
        ($p.shape)[2 .. ^1] & "\\t" & p.ty & "\\t\" & w & \"\\t\" & native\n"
  src.add "proc runThreeWay*() =\n"
  src.add runs
  src.add "  discard\n"
  parseStmt(src)

const progs = genPrograms(k8aSeed, k8aCount)
emitThreeWay(progs)
runThreeWay()
