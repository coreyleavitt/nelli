#!/usr/bin/env python3
"""RFC-0016 INT-34 B2: cut `src/nelli/smt/walk_types.nim` out of `runtime.nim`.

One-shot move tooling, kept for the record (re-running it on the moved tree
finds nothing to move and exits). It

  * moves every type section of regions R0..R4 of `runtime.nim` (the regions
    of `scripts/int34-deps.py`, up to `include "runtime_heap.nim"`) into the
    new leaf, in source order;
  * moves the compile-time exit-group field walk (`forEachExitGroup` through
    `collectExitGroupFields`) with the types it walks;
  * marks each moved type, and the fields of each moved type that was private
    to `runtime.nim`, exported, so `runtime.nim` (and the modules later cut
    out of it) can use them. A type `runtime.nim` exported already keeps its
    fields exactly as they were, and so does `RawWitness` (private, but
    reachable through public fields): their private fields stay private and
    `runtime.nim` reads them under `privateAccess`;
  * replaces the forward declarations of the bodies that only needed
    `WalkCtx` in scope (`seedCallerHeapInWalkCtx`, `isFollowConcreteWalk`,
    `isConcolicFollowWalk`, `programGlobal`, `globalHiddenRoute`,
    `unwrittenResultZero`) by the bodies themselves.

The module header, the imports and the re-export line are written by hand
around what this produces.

usage: scripts/int34-b2-move.py [src/nelli/smt]
"""
import re
import sys

smt = sys.argv[1] if len(sys.argv) > 1 else 'src/nelli/smt'
rt_path = f'{smt}/runtime.nim'
src = open(rt_path).read().split('\n')

R6 = next(i for i, l in enumerate(src) if l.startswith('include "runtime_heap.nim"'))

# Types whose field visibility is kept as it was.
KEEP_FIELDS = {'RawWitness', 'RawDiagnostic', 'RawUndefined', 'SatCandidate',
               'CandidateReplay', 'RawResult', 'ConcolicBranchRecord',
               'ConcolicDefinedFact', 'Rfc0005S1CarrierProbe',
               'Rfc0005S1LeakPinProbe', 'TargetSolveCost', 'VerdictDecision'}


def code(line):
    line = re.sub(r'"(\\.|[^"\\])*"', '""', line)
    i = line.find('#')
    return line if i < 0 else line[:i]


def sections():
    """(start, end) half-open line ranges of the type sections before R6."""
    out = []
    i = 0
    while i < R6:
        if re.match(r'^type\b', src[i]):
            s, j = i, i + 1
            while j < len(src) and not (src[j] and src[j][0] not in ' #'):
                j += 1
            e = j
            while e > s + 1 and (not src[e - 1].strip() or src[e - 1].startswith('#')):
                e -= 1
            out.append((s, e))
            i = j
        else:
            i += 1
    return out


HEAD1 = re.compile(r'^type\s+([A-Za-z_]\w*)(\*?)(\s*(\[.*?\])?\s*=)(.*)$')
HEAD2 = re.compile(r'^  ([A-Za-z_]\w*)(\*?)(\s*(\[.*?\])?\s*=)(.*)$')
FIELD = re.compile(r'^(\s+)(case\s+)?([A-Za-z_]\w*\*?(?:\s*\{\.[^}]*\.\})?'
                   r'(?:\s*,\s*[A-Za-z_]\w*\*?(?:\s*\{\.[^}]*\.\})?)*)(\s*:)(.*)$')


def export_names(group):
    def one(m):
        n, star = m.group(1), m.group(2)
        return n + '*' if not star else m.group(0)
    return re.sub(r'([A-Za-z_]\w*)(\*?)(?=\s*(\{\.[^}]*\.\})?\s*(,|$))', one, group)


def transform(lines):
    out = []
    cur, kind, depth = None, None, 0
    for l in lines:
        at_start = depth
        c = code(l)
        depth += c.count('[') + c.count('(') - c.count(']') - c.count(')')
        if at_start > 0:
            out.append(l)
            continue
        m = HEAD1.match(l) or HEAD2.match(l)
        if m:
            cur = m.group(1)
            rhs = m.group(5)
            kind = 'object' if re.search(r'\bobject\b', rhs) else 'other'
            if not m.group(2):
                l = l.replace(cur, cur + '*', 1)
            out.append(l)
            continue
        s = l.strip()
        if (kind == 'object' and cur not in KEEP_FIELDS and s and
                not s.startswith('#') and not s.startswith('of ') and
                not s.startswith('else')):
            f = FIELD.match(l)
            if f:
                l = (f.group(1) + (f.group(2) or '') + export_names(f.group(3)) +
                     f.group(4) + f.group(5))
        out.append(l)
    return out


secs = sections()
if not secs:
    sys.exit('no type section left before R6: already moved')

# The exit-group field walk.
eg_s = next(i for i, l in enumerate(src) if l.startswith('template forEachExitGroup('))
eg_e = next(i for i, l in enumerate(src) if l.startswith('proc exitGroupFieldPaths*('))

moved = []
for s, e in secs:
    moved.append(transform(src[s:e]))

eg = src[eg_s:eg_e]
while eg and not eg[-1].strip():
    eg.pop()
eg_text = '\n'.join(eg)
for n in ['forEachExitGroup', 'isExitGroupType', 'isExitFrameType',
          'collectExitGroupFields']:
    eg_text = re.sub(r'^((?:template|proc) )' + n + r'(?=[\[(])', r'\g<1>' + n + '*',
                     eg_text, flags=re.M)
eg_text = re.sub(r'^  (exitGroupsWalked|exitGroupsUnwalked) =', r'  \1* =',
                 eg_text, flags=re.M)

body = '\n\n'.join('\n'.join(m) for m in moved) + '\n\n' + eg_text + '\n'
open(f'{smt}/walk_types.body.nim', 'w').write(body)

# Drop the moved ranges from runtime.nim (bottom-up so indices stay valid).
cuts = sorted(secs + [(eg_s, eg_e)], reverse=True)
for s, e in cuts:
    del src[s:e]


# The forward-declared bodies.
def routine(name):
    """(start, end) of the LAST column-0 definition of `name` with a body."""
    hits = [i for i, l in enumerate(src)
            if re.match(r'^(proc|func) ' + name + r'\*?\(', l)]
    s = hits[-1]
    e = s + 1
    while e < len(src) and (not src[e] or src[e][0] in ' #' and not src[e].startswith('# ---')):
        e += 1
    while not src[e - 1].strip() or src[e - 1].startswith('#'):
        e -= 1
    return hits[0], s, e


for name in ['seedCallerHeapInWalkCtx', 'isFollowConcreteWalk',
             'isConcolicFollowWalk', 'programGlobal', 'globalHiddenRoute',
             'unwrittenResultZero']:
    fwd, s, e = routine(name)
    assert fwd < s, name
    b = src[s:e]
    del src[s:e]
    # the forward declaration: its header line and its indented doc lines
    fe = fwd + 1
    while fe < len(src) and src[fe].startswith('  '):
        fe += 1
    src[fwd:fe] = b

open(rt_path, 'w').write('\n'.join(src))
print(f'moved {len(secs)} type sections and the exit-group walk; '
      f'walk_types body in {smt}/walk_types.body.nim')
