#!/usr/bin/env -S python3 -I
"""Deterministically shard the fuzzer-msvc walker-test glob.

Usage: shard-walker-tests.py <globs> <nshards>
  <globs>  comma/space separated globs, relative to the repo root.

Assignment: tests are sorted by file name and test i goes to shard i % N.
Stable across runs, and a new test lands on exactly one shard.

Self-check (always run, exit 1 on failure): the union of the shards must equal
the full glob, with no test missing and none duplicated, and the glob must
match at least one file. Emits GitHub outputs when GITHUB_OUTPUT is set:
  shard_ids   JSON list of shard indexes
  shards_json JSON object {"<idx>": ["tests/x.nim", ...]}
  total       number of tests
"""
import glob
import json
import os
import re
import sys


def main() -> int:
    globs = [g for g in re.split(r"[,\s]+", sys.argv[1]) if g]
    n = int(sys.argv[2])
    if n < 1:
        print("nshards must be >= 1", file=sys.stderr)
        return 1
    full = sorted({p for g in globs for p in glob.glob(g) if os.path.isfile(p)},
                  key=lambda p: os.path.basename(p))
    if not full:
        print(f"glob {globs} matched 0 files -- refusing to report a false green",
              file=sys.stderr)
        return 1
    shards = {str(i): [] for i in range(n)}
    for i, p in enumerate(full):
        shards[str(i % n)].append(p)
    flat = [p for s in shards.values() for p in s]
    dups = sorted({p for p in flat if flat.count(p) > 1})
    missing = sorted(set(full) - set(flat))
    extra = sorted(set(flat) - set(full))
    if dups or missing or extra or len(flat) != len(full):
        print(f"SHARD SELF-CHECK FAILED: duplicated={dups} missing={missing} extra={extra}",
              file=sys.stderr)
        return 1
    for k, v in shards.items():
        print(f"shard {k}: {len(v)} tests")
    print(f"self-check OK: {len(flat)} shard slots == {len(full)} globbed tests, "
          "no gaps, no duplicates")
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as f:
            f.write(f"shard_ids={json.dumps(list(shards))}\n")
            f.write(f"shards_json={json.dumps(shards)}\n")
            f.write(f"total={len(full)}\n")
    return 0


sys.exit(main())
