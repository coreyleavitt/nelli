#!/usr/bin/env python3
"""RFC-0016 INT-34: the upward calls between the regions of runtime.nim.

The cut of `runtime.nim` into layered modules needs every name a region uses
to be defined in that region or a lower one. This scan lists the names a
region uses whose body sits in a HIGHER region: the edges a forward
declaration resolves today and a module boundary would not.

Regions are found by anchor (a line that starts with the given text), so the
scan survives line drift. The scan is textual: comments and string bodies are
stripped per line, a name's body is its last top-level definition, a `.f`
not followed by a call is a field read, and a routine nested in a region
shadows a top-level one of its name there. A plain local that shares a name
with a top-level symbol is still counted.

usage: scripts/int34-deps.py [--all] [--sites] [src/nelli/smt/runtime.nim]
  --all    print every cross-region edge, not only the upward ones
  --sites  print the using line numbers of each name
"""
import re
import sys

# (label, anchor): a region starts at the first line that starts with its
# anchor and ends where the next region starts.
REGIONS = [
    ("R0 types, forkPath", None),
    ("R1 lower", "# ---- IR-expr → SymVal"),
    ("R2 solving", "# ---- Path / solve / walk"),
    # INT-34 B2: the frame types and `WalkCtx` are `walk_types.nim`'s now;
    # R3 starts at the first routine that takes a `WalkCtx`.
    ("R3 frames, WalkCtx", "proc degrade(w: var WalkCtx"),
    ("R4 expression drains", "# Fork-site registry (Phase 15 H1"),
    ("R6 statement arms, walk", 'include "runtime_heap.nim"'),
    ("R7 probes, closure descent", "# ---- Statement exit-taint test hook"),
    ("R8 drivers", "# ---- Public driver"),
    ("R9 witness reads, hooks", "# ---- Raw → typed witness"),
]

KW = re.compile(r'^(proc|func|template|macro|iterator|converter|method)\s+`?'
                r'([A-Za-z_][A-Za-z0-9_]*)')
TLINE = re.compile(r'^  ([A-Za-z_][A-Za-z0-9_]*)\*?\s*(\[.*\])?\s*[=:]')
VLINE = re.compile(r'^(var|let|const|type)\s+([A-Za-z_][A-Za-z0-9_]*)')
IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')
NESTED = re.compile(r'^\s+(?:proc|func|template|iterator)\s+`?([A-Za-z_][A-Za-z0-9_]*)')
FIELD = re.compile(r'\.[A-Za-z_][A-Za-z0-9_]*(?![A-Za-z0-9_(\[])')


def code(line):
    line = re.sub(r'"(\\.|[^"\\])*"', '""', line)
    i = line.find('#')
    return line if i < 0 else line[:i]


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    show_all = '--all' in sys.argv
    sites = '--sites' in sys.argv
    path = args[0] if args else 'src/nelli/smt/runtime.nim'
    src = open(path).read().split('\n')

    starts = [1]
    for label, anchor in REGIONS[1:]:
        hits = [i for i, l in enumerate(src, 1) if l.startswith(anchor)]
        if not hits:
            sys.exit(f"anchor not found for {label}: {anchor!r}")
        starts.append(hits[0])
    if starts != sorted(starts):
        sys.exit(f"anchors out of order: {starts}")
    bounds = [(s, (starts[k + 1] - 1 if k + 1 < len(starts) else len(src)))
              for k, s in enumerate(starts)]

    def region(line):
        for k, (a, b) in enumerate(bounds):
            if a <= line <= b:
                return k
        return -1

    defs = {}
    block = None
    for i, l in enumerate(src, 1):
        if not l or l[0] == '#':
            continue
        m = KW.match(l)
        if m:
            defs.setdefault(m.group(2), []).append(i)
            block = None
            continue
        m = VLINE.match(l)
        if m:
            defs.setdefault(m.group(2), []).append(i)
            block = None
            continue
        if re.match(r'^(type|var|let|const)\s*$', l):
            block = l.strip()
            continue
        if l[0] != ' ':
            block = None
        if block and TLINE.match(l):
            defs.setdefault(TLINE.match(l).group(1), []).append(i)
    body = {n: max(v) for n, v in defs.items()}

    # A routine nested in a region's code shadows a top-level one of the same
    # name there: its calls are local, not edges.
    nested = {}
    for i, l in enumerate(src, 1):
        m = NESTED.match(l)
        if m:
            nested.setdefault(region(i), set()).add(m.group(1))

    edges = {}
    for i, l in enumerate(src, 1):
        if KW.match(l):
            continue   # a declaration line names itself
        r = region(i)
        c = FIELD.sub('', code(l))   # `x.f` is a field read, not a call
        for w in set(IDENT.findall(c)):
            if w not in body or w in nested.get(r, ()):
                continue
            t = region(body[w])
            if t == r or (t < r and not show_all):
                continue
            edges.setdefault((r, t), {}).setdefault(w, []).append(i)

    for k, (a, b) in enumerate(bounds):
        print(f"{REGIONS[k][0]}: {a}-{b}")
    print()
    for (a, b), names in sorted(edges.items()):
        print(f"{REGIONS[a][0].split()[0]} -> {REGIONS[b][0].split()[0]}: "
              f"{len(names)}")
        for n in sorted(names):
            extra = f"  @{','.join(map(str, names[n]))}" if sites else ""
            print(f"  {n} (body {body[n]}){extra}")


if __name__ == '__main__':
    main()
