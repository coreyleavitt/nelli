#!/usr/bin/env python3
"""RFC-0016 INT-34 B4: cut `src/nelli/smt/lower_expr.nim` out of `runtime.nim`.

One-shot move tooling, kept for the record (re-running it on the moved tree
finds no span to move and exits). It

  * moves region R1 (`scripts/int34-deps.py`) whole: `lower`/`lowerBool`,
    the operator templates, the set, seq and global-read machinery, and the
    C4 literal lowering B0 placed after `lower`;
  * moves the run state of region R0 that R1 reads, with the routines over it
    that R1 calls: `closureEnvWrites`, `loweringReadNames`, the S8ce fault
    injection (`injectedShape`, `injectShapeFault`), `arithFrames`,
    `checkScopes`, `resetArith`, `checkedNow`, `obligationLog` and
    `pendingEnvWriteIx`;
  * drops the forward declaration of `lowerHofCall` (region R7) and routes its
    one call through `lowerExprHooks.lowerHofCall`;
  * marks every moved top-level name exported, so `runtime.nim` can name it.

The module header, the imports, the hooks object, the reset and release procs
and the re-export line are written by hand around what this produces.

usage: scripts/int34-b4-move.py [src/nelli/smt]
"""
import re
import sys

smt = sys.argv[1] if len(sys.argv) > 1 else 'src/nelli/smt'
rt_path = f'{smt}/runtime.nim'
src = open(rt_path).read().split('\n')

# (first line, first line NOT moved): each a line that starts with the text.
SPANS = [
    ("var closureEnvWrites {.threadvar.}", "# ---- RFC-0005 S8m: sort-checked"),
    ("when defined(symexTestInjectWalkerFault):",
     "# ---- Phase 15 Cluster R (R1): per-walker ref-sort"),
    ("proc pendingEnvWriteIx(", "var currentVariantHeaps*"),
    ("# ---- IR-expr → SymVal", "# ---- Path / solve / walk"),
]
# The forward declaration the hook replaces: its line and its doc.
DROP = ("proc lowerHofCall(env", "# ---- IR-expr → SymVal")


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

KW = re.compile(r'^(\s*)(proc|func|template|iterator|macro|converter) '
                r'([A-Za-z_][A-Za-z0-9_]*)([(\[])')
VC = re.compile(r'^(\s*)(var|const|let) ([A-Za-z_][A-Za-z0-9_]*)([ :=])')
out = []
calls = 0
for block in moved:
    for l in block:
        # column 0, or the two declarations of the S8ce `when` block
        m = KW.match(l)
        if m and (m.group(1) == '' or
                  l.startswith('  proc injectShapeFault(')):
            l = KW.sub(lambda m: f"{m.group(1)}{m.group(2)} {m.group(3)}*"
                                 f"{m.group(4)}", l, count=1)
        m = VC.match(l)
        if m and (m.group(1) == '' or
                  l.startswith('  var injectedShape ')):
            l = VC.sub(lambda m: f"{m.group(1)}{m.group(2)} {m.group(3)}*"
                                 f"{m.group(4)}", l, count=1)
        if l.strip() == 'lowerHofCall(env, e)':
            l = l.replace('lowerHofCall(env, e)',
                          'lowerExprHooks.lowerHofCall(env, e)')
            calls += 1
        out.append(l)
    if out and out[-1] != '':
        out.append('')
if calls != 1:
    sys.exit(f"expected one lowerHofCall call, found {calls}")

rest = [l for i, l in enumerate(src) if i not in cut]
open(rt_path, 'w').write('\n'.join(rest))
open(f'{smt}/lower_expr.body', 'w').write('\n'.join(out))
print(f"moved {sum(len(b) for b in moved)} lines in {len(moved)} spans")
