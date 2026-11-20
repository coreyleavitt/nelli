#!/usr/bin/env python3
"""RFC-0016 INT-34 B5: cut `src/nelli/smt/walk_solve.nim` out of `runtime.nim`.

One-shot move tooling, kept for the record (re-running it on the moved tree
finds no span to move and exits). It

  * moves region R2 (`scripts/int34-deps.py`) whole: the witness extraction
    (`extractWitness`, `modelPins`, the heap snapshot and the `ptr*Key`
    helpers), the solver's work accounting and budget threadvars, the query
    facts (`seqRangeFacts`, `divRangeFacts`, `bvOffsetLinks`, ...), the capped
    check (`checkCapped`), `pathRoots`, `trySolve` and `pathInfeasible`;
  * moves the run state of region R0 that R2 reads: `currentVariantHeaps`,
    `currentWinningGlobals`, `heapWitnessNominalRegistry` and
    `currentClosureCallAxioms`;
  * marks every moved top-level name exported (and every name declared
    directly inside a top-level `when defined(...)` block), so `runtime.nim`
    can name it.

The module header, the imports, the reset and release procs and the
re-export lines are written by hand around what this produces.

usage: scripts/int34-b5-move.py [src/nelli/smt]
"""
import re
import sys

smt = sys.argv[1] if len(sys.argv) > 1 else 'src/nelli/smt'
rt_path = f'{smt}/runtime.nim'
src = open(rt_path).read().split('\n')

# (first line, first line NOT moved): each a line that starts with the text.
SPANS = [
    ("var currentVariantHeaps*", "var currentCallerHeaps*"),
    ("var currentClosureCallAxioms*", "var currentClosureCallAxiomStrs*"),
    ("var extractionErrors*", "proc degrade(w: var WalkCtx"),
]


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

KW = re.compile(r'^(\s*)(proc|func|template|iterator|macro|converter) '
                r'([A-Za-z_][A-Za-z0-9_]*)([(\[])')
VC = re.compile(r'^(\s*)(var|const|let) ([A-Za-z_][A-Za-z0-9_]*)([ :=])')
out = []
for block in moved:
    inWhen = False
    for l in block:
        if l and not l[0].isspace() and not l.startswith('#'):
            inWhen = l.startswith('when defined(')
        def ok(m):
            return m.group(1) == '' or (inWhen and m.group(1) == '  ')
        m = KW.match(l)
        if m and ok(m):
            l = KW.sub(lambda m: f"{m.group(1)}{m.group(2)} {m.group(3)}*"
                                 f"{m.group(4)}", l, count=1)
        m = VC.match(l)
        if m and ok(m):
            l = VC.sub(lambda m: f"{m.group(1)}{m.group(2)} {m.group(3)}*"
                                 f"{m.group(4)}", l, count=1)
        out.append(l)
    while out and out[-1] == '':
        out.pop()
    out.append('')

rest = [l for i, l in enumerate(src) if i not in cut]
open(rt_path, 'w').write('\n'.join(rest))
open(f'{smt}/walk_solve.body', 'w').write('\n'.join(out))
print(f"moved {sum(len(b) for b in moved)} lines in {len(moved)} spans")
