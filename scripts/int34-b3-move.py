#!/usr/bin/env python3
"""RFC-0016 INT-34 B3: cut `src/nelli/smt/walk_path.nim` out of `runtime.nim`.

One-shot move tooling, kept for the record (re-running it on the moved tree
finds no span to move and exits). It

  * moves the procedures of region R0 (`scripts/int34-deps.py`) that read no
    `runtime.nim` threadvar: the fork constructors (`forkPath*`,
    `deepCopyHeapState`, `taintInPlace`), the container-cell readers
    (`cellValue`, `tabValAt`, `tabMoreEq`, `containerCardConds`), the literal
    protos (`bvConst`, `intLitProto`, `probeProto`), the `WalkCtx` readers
    (`isFollowConcreteWalk`, `programGlobal`, `unwrittenResultZero`) and the
    rest of R0's helpers, in source order, with the comments above them;
  * leaves R0's threadvars and the procedures that read them
    (`checkedNow`, `seedCallerHeapThreadvars`, `pendingEnvWriteIx`, ...);
  * drops the forward declaration of `noteUbAtFork` and routes its two calls
    through `lowerHooks.noteUbAtFork` (its body reads the run's target, R4);
  * marks every moved routine exported, so `runtime.nim` can call it.

The module header, the imports and the re-export line are written by hand
around what this produces.

usage: scripts/int34-b3-move.py [src/nelli/smt]
"""
import re
import sys

smt = sys.argv[1] if len(sys.argv) > 1 else 'src/nelli/smt'
rt_path = f'{smt}/runtime.nim'
src = open(rt_path).read().split('\n')

# (first line, first line NOT moved): each a line that starts with the text.
SPANS = [
    ("# ---- Phase 15 H1: logical-heap fork deep-copy", "proc noteUbAtFork("),
    ("template forkPathTainted(", "var freshnessCapHints*"),
    ("proc inCellDomain(", "var closureEnvWrites "),
    ("proc opSite(", "# ---- Phase 15 Cluster R (R1): per-walker ref-sort"),
    ("proc uncheckedIndexSite(", "proc depositStrIndexOob("),
    ("proc seedCallerHeapInWalkCtx*(", "proc pendingEnvWriteIx("),
    ("proc unwrittenResultZero(", "var currentVariantHeaps*"),
    ("proc seqElemFits(", "proc lowerHofCall(env"),
    ("# ---- RFC-0005 S8bc (item 3): a seq of a tree element",
     "# ---- IR-expr → SymVal"),
]
# The forward declaration the hook replaces: its line and its doc.
DROP = ("proc noteUbAtFork(", "template forkPathTainted(")


def find(text, after=0):
    for i in range(after, len(src)):
        if src[i].startswith(text):
            return i
    return -1


moved = []
cut = set()
for a, b in SPANS:
    s = find(a)
    if s < 0:
        sys.exit(f"nothing to move: {a!r} not found")
    e = find(b, s + 1)
    if e < 0:
        sys.exit(f"end anchor not found: {b!r}")
    moved.append(src[s:e])
    cut.update(range(s, e))
s = find(DROP[0])
e = find(DROP[1], s + 1)
cut.update(range(s, e))

KW = re.compile(r'^(proc|func|template|iterator) ([A-Za-z_][A-Za-z0-9_]*)([(\[])')
out = []
for block in moved:
    for l in block:
        l = KW.sub(lambda m: f"{m.group(1)} {m.group(2)}*{m.group(3)}", l)
        # the hook takes the child as a `pointer` (`walk_state` cannot name
        # `Path`; see `LowerHooks.noteUbAtFork`)
        l = l.replace(
            '    if newUb != {}: noteUbAtFork(parent.taint, child, newUb)',
            '    if newUb != {}:\n'
            '      lowerHooks.noteUbAtFork(parent.taint, cast[pointer](child), newUb)')
        l = l.replace(
            '  if newUb != {}: noteUbAtFork(priorTaint, p, newUb)   ## RFC-0016 W3-z R1',
            '  if newUb != {}:   ## RFC-0016 W3-z R1\n'
            '    lowerHooks.noteUbAtFork(priorTaint, cast[pointer](p), newUb)')
        out.append(l)
    if out and out[-1] != '':
        out.append('')

rest = [l for i, l in enumerate(src) if i not in cut]
open(rt_path, 'w').write('\n'.join(rest))
open(f'{smt}/walk_path.body', 'w').write('\n'.join(out))
print(f"moved {sum(len(b) for b in moved)} lines in {len(moved)} spans")
