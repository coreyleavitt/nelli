#!/usr/bin/env python3
"""RFC-0016 CI-A3: derive + shard the symex-linux run set.

The Linux twin of scripts/derive-ci-suites.ps1, and the same placement: the
run set is nelli.nimble's `test` task (what `sweep.sh --derive` runs), each
test is weighted by scripts/ci-suite-seconds.tsv (a test the table does not
list counts at the table's median), and the tests go longest first into the
least-loaded shard, with as many shards as keep each near TARGET_SHARD_MIN.
Unlike the Windows script this covers EVERY registered test, not only
tsymex_*: the Linux leg is the one that runs the fuzzer and base suites.

The table was measured on the symex-mingw leg (Windows, one test at a time),
so on Linux it is a relative weight, not a duration; TIME_SCALE converts it
to the Linux wall time at JOBS parallel workers. Retune TIME_SCALE from a
run's per-shard times (the shard summary prints them).

Outputs (to $GITHUB_OUTPUT under Actions, else stdout):
  shards_json  {"0": ["tsymex_a", ...], ...}
  shard_ids    [0, 1, ...]
  regexes_json {"0": "^(tsymex_a|tsymex_b)$", ...}  the sweep.sh -f value
"""
import json
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
TARGET_SHARD_MIN = 25      # wall minutes one shard should take on Linux
JOBS = 4                   # sweep.sh -j on a 4-core ubuntu-24.04 runner
TIME_SCALE = float(os.environ.get("NELLI_LINUX_TIME_SCALE", "0.5"))
MIN_SHARDS = 8
CORPUS_FLOOR = 500


def registered():
    text = open(os.path.join(ROOT, "nelli.nimble")).read()
    m = re.search(r"task test,.*?for f in \[(.*?)\]:", text, re.S)
    if not m:
        sys.exit("derive-linux-shards: no 'task test' suite array in nelli.nimble")
    body = re.sub(r"#[^\r\n]*", "", m.group(1))
    return sorted(set(re.findall(r'"([^"]+)"', body)))


def measured():
    out = {}
    path = os.path.join(ROOT, "scripts", "ci-suite-seconds.tsv")
    for line in open(path):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        out[f[0]] = float(f[1])
    return out


def main():
    names = [n for n in registered() if os.path.exists(os.path.join(ROOT, "tests", n + ".nim"))]
    only = os.environ.get("NELLI_TESTS_REGEX", "")
    floor = CORPUS_FLOOR
    if only:                  # a dispatch narrowing the run: no floor, no MIN_SHARDS
        names = [n for n in names if re.search(only, n)]
        floor = 1
    if len(names) < floor:
        sys.exit("derive-linux-shards: only %d registered tests with a file (floor %d)"
                 % (len(names), floor))
    meas = measured()
    known = sorted(meas[n] for n in names if n in meas)
    default = known[len(known) // 2] if known else 45.0
    est = {n: meas.get(n, default) * TIME_SCALE for n in names}
    total = sum(est.values())
    count = max(1 if only else MIN_SHARDS, -(-int(total) // (60 * TARGET_SHARD_MIN * JOBS)))
    count = min(count, len(names))
    shards = [[] for _ in range(count)]
    loads = [0.0] * count
    for n in sorted(names, key=lambda n: (-est[n], n)):
        i = min(range(count), key=lambda k: (loads[k], k))
        shards[i].append(n)
        loads[i] += est[n]
    shards = [sorted(s) for s in shards]
    assert sum(len(s) for s in shards) == len(names) == len(set(sum(shards, [])))
    print("corpus: %d tests, %.1f weighted core-min, %d untimed at median %.1f s: %d shards"
          % (len(names), total / 60, len([n for n in names if n not in meas]), default, count),
          file=sys.stderr)
    for i, s in enumerate(shards):
        print("  shard %d: %d tests, ~%.1f wall min" % (i, len(s), loads[i] / 60 / JOBS), file=sys.stderr)
    out = {
        "shards_json": json.dumps({str(i): s for i, s in enumerate(shards)}, separators=(",", ":")),
        "shard_ids": json.dumps(list(range(count)), separators=(",", ":")),
        "regexes_json": json.dumps({str(i): "^(" + "|".join(s) + ")$" for i, s in enumerate(shards)},
                                   separators=(",", ":")),
    }
    gh = os.environ.get("GITHUB_OUTPUT")
    if gh:
        with open(gh, "a") as f:
            for k, v in out.items():
                f.write("%s=%s\n" % (k, v))
    else:
        for k, v in out.items():
            print("%s=%s" % (k, v))


main()
