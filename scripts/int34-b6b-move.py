#!/usr/bin/env python3
"""RFC-0016 INT-34 B6b: cut `src/nelli/smt/walk_expr.nim` out of `runtime.nim`.

One-shot move tooling, kept for the record (re-running it on the moved tree
finds no span to move and exits). It

  * moves region R4 (`scripts/int34-deps.py`) whole, less the forward
    declarations it holds for routines that stay in `runtime.nim` (`walk`,
    `evalCondSynced`, `evalReturnSynced`, `anchorViews`, `liveViewMarks`,
    `logInPlace`, `routeRaise`, `noteOpaqueUndefined`) and the
    `compoundStmtKinds` set among them, which only the statement walkers
    read: lowering inside a statement and the drains onto the consuming path
    (`lowerInExpr`, `drainPendingLowerEffects`, the raise forks,
    `crashRaise`, `haltUndefined`, `haltExcludedDefect`, `noteUbAtFork`),
    the depth and recursion bails, the concrete-branch checks, the
    discriminator and return exits, and the path join (`mergeJoinPaths`);
  * moves the run state and the routine of region R0 that R4 reads:
    `boundsUnchecked`, `lastDrainedClosureExitPc`, the caller threadvars a
    closure call is lowered against (`currentCallerUb`, `currentCallerTaint`,
    `currentCallerPc`), `closureBodyCallerPc` and
    `seedCallerHeapThreadvars`, which writes them;
  * routes R4's calls of `routeRaise` (region R7: it walks `finally` bodies)
    through the typed hook `walkExprHooks.routeRaise`;
  * marks every moved top-level name exported, so `runtime.nim` can name it.

The module header, the hook type, the imports, the reset and release procs
and the re-export lines are written by hand around what this produces.

usage: scripts/int34-b6b-move.py [src/nelli/smt]
"""
import re
import sys

smt = sys.argv[1] if len(sys.argv) > 1 else 'src/nelli/smt'
rt_path = f'{smt}/runtime.nim'
src = open(rt_path).read().split('\n')

# (first line, first line NOT moved): each a line that starts with the text
# (a multi-line anchor matches line by line).
SPANS = [
    ("proc boundsUnchecked(", "proc depositStrIndexOob("),
    ("var lastDrainedClosureExitPc", "var currentClosureCallAxiomStrs*"),
    ("# ============================================================================\n# Fork-site registry",
     "proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path]"),
    ("proc raiseSplit(", 'include "runtime_heap.nim"'),
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
CALL = re.compile(r'(?<![A-Za-z0-9_.`])routeRaise\(')
out = []
hooked = 0
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
        if not l.strip().startswith('#'):
            cut_at = l.find(' #')
            code, rest = (l, '') if cut_at < 0 else (l[:cut_at], l[cut_at:])
            code, n = CALL.subn('walkExprHooks.routeRaise(', code)
            hooked += n
            l = code + rest
        out.append(l)
    while out and out[-1] == '':
        out.pop()
    out.append('')

rest = [l for i, l in enumerate(src) if i not in cut]
open(rt_path, 'w').write('\n'.join(rest))
open(f'{smt}/walk_expr.body', 'w').write('\n'.join(out))
print(f"moved {sum(len(b) for b in moved)} lines in {len(moved)} spans; "
      f"{hooked} routeRaise calls hooked")
