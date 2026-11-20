#!/usr/bin/env python3
"""RFC-0016 INT-34 B6a: cut `src/nelli/smt/walk_ctx.nim` out of `runtime.nim`.

One-shot move tooling, kept for the record (re-running it on the moved tree
finds no span to move and exits). It

  * moves region R3 (`scripts/int34-deps.py`) whole: the walk context's
    verbs (`degrade`, `halted`, `exact`, `shouldStop`, the frame push and
    pop, `solveTargetHit`, `decideVerdict`, the pending take and restore),
    the opaque-heap havoc, the outer-binding and cell carry of a call, and
    the call-summary cache keys;
  * moves the run state of region R0 that R3 reads: `heapDepthErrors`,
    `newFieldZeroErrors`, the caller-heap threadvars
    (`currentCallerHeaps`, `currentCallerHeapDepth`,
    `currentCallerAllocCounters`, `currentCallerLiveRefs`), the closure-exit
    ones (`currentClosureExitHeaps`, `currentClosureExitAllocCounters`,
    `currentClosureExitLiveRefs`, `currentClosureDidMutateHeap`,
    `currentClosureExitPc`) and `currentClosureCallErrors`;
  * marks every moved top-level name exported, so `runtime.nim` can name it.

The module header, the imports, the reset and release procs and the
re-export lines are written by hand around what this produces.

usage: scripts/int34-b6a-move.py [src/nelli/smt]
"""
import re
import sys

smt = sys.argv[1] if len(sys.argv) > 1 else 'src/nelli/smt'
rt_path = f'{smt}/runtime.nim'
src = open(rt_path).read().split('\n')

# (first line, first line NOT moved): each a line that starts with the text.
SPANS = [
    ("var heapDepthErrors*", "var ptrFamilyHints*"),
    ("var currentCallerHeaps*", "var lastDrainedClosureExitPc"),
    ("var currentClosureCallErrors*", "## NOTE: `currentWalkCtxPtr` has been"),
    ("proc degrade(w: var WalkCtx", "# ============================================================================\n# Fork-site registry"),
]


def find(text, after=0):
    lines = text.split('\n')
    for i in range(after, len(src)):
        if all(i + k < len(src) and src[i + k].startswith(t)
               for k, t in enumerate(lines)):
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
                r'`?([A-Za-z_][A-Za-z0-9_]*)`?([(\[])')
VC = re.compile(r'^(\s*)(var|const|let) ([A-Za-z_][A-Za-z0-9_]*)([ :=])')
out = []
for block in moved:
    for l in block:
        m = KW.match(l)
        if m and m.group(1) == '':
            l = KW.sub(lambda m: f"{m.group(1)}{m.group(2)} {m.group(3)}*"
                                 f"{m.group(4)}", l, count=1)
        m = VC.match(l)
        if m and m.group(1) == '':
            l = VC.sub(lambda m: f"{m.group(1)}{m.group(2)} {m.group(3)}*"
                                 f"{m.group(4)}", l, count=1)
        out.append(l)
    while out and out[-1] == '':
        out.pop()
    out.append('')

rest = [l for i, l in enumerate(src) if i not in cut]
open(rt_path, 'w').write('\n'.join(rest))
open(f'{smt}/walk_ctx.body', 'w').write('\n'.join(out))
print(f"moved {sum(len(b) for b in moved)} lines in {len(moved)} spans")
