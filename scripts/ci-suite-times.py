#!/usr/bin/env python3
"""Refresh scripts/ci-suite-seconds.tsv from symex-mingw runs.

RFC-0005 S8cm. `scripts/derive-ci-suites.ps1` places the corpus suites into
shards by measured time (longest first, each into the least-loaded shard), and
this table is the measurement: one line per suite, the mean seconds it took to
compile and run on the symex-mingw leg over the runs named on its first line.

Usage:
    scripts/ci-suite-times.py RUN_ID [RUN_ID ...]          # rewrite the table
    scripts/ci-suite-times.py --log FILE [--log FILE ...]  # from saved logs
    scripts/ci-suite-times.py --check                      # report drift only

A run's log is read with `gh run view RUN_ID --log` (one API call per run).
A suite's time is the `suite-seconds <suite> <s>` line the corpus job prints
for it; for a run older than that line, the span from its `==> <suite>` line
to its `<== <suite>` line (run-ci-suite.ps1 prints the first before `nim c`
and the second when the binary exits, so the span is compile plus run).

A suite in the table that no run measured keeps its old value; a suite no
longer registered in nelli.nimble is dropped. Suites with no value at all are
placed at the table's median by the derive step, so the table only needs a
refresh when the shards' measured times drift from the derive step's
prediction (the corpus job prints both).
"""
import datetime
import re
import statistics
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLE = ROOT / "scripts" / "ci-suite-seconds.tsv"
LINE = re.compile(r"^(?P<job>[^\t]+)\t[^\t]*\t\ufeff?(?P<ts>\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\.\d+)Z (?P<msg>.*)$")


def stamp(s):
    return datetime.datetime.strptime(s[:26], "%Y-%m-%dT%H:%M:%S.%f")


def parse(text):
    """{suite: seconds} for one run's log."""
    direct, spans, start = {}, {}, {}
    for raw in text.splitlines():
        m = LINE.match(raw)
        if not m:
            continue
        msg = m.group("msg")
        d = re.match(r"suite-seconds (\S+) ([\d.]+)$", msg)
        if d:
            direct[d.group(1)] = float(d.group(2))
            continue
        s = re.match(r"==> (\S+)$", msg)
        if s:
            start[(m.group("job"), s.group(1))] = stamp(m.group("ts"))
            continue
        e = re.match(r"<== (\S+) rc=", msg)
        if e and (m.group("job"), e.group(1)) in start:
            t0 = start[(m.group("job"), e.group(1))]
            spans[e.group(1)] = (stamp(m.group("ts")) - t0).total_seconds()
    spans.update(direct)
    return spans


def registered():
    text = (ROOT / "nelli.nimble").read_text()
    body = re.search(r"task test,.*?for f in \[(.*?)\]:", text, re.S).group(1)
    body = re.sub(r"#[^\n]*", "", body)
    return set(re.findall(r'"([^"]+)"', body))


def read_table():
    old, header = {}, []
    if TABLE.exists():
        for line in TABLE.read_text().splitlines():
            if line.startswith("#"):
                header.append(line)
            elif line.strip():
                name, sec = line.split("\t")[:2]
                old[name] = float(sec)
    return old, header


def main(argv):
    logs, runs, check = [], [], False
    it = iter(argv)
    for a in it:
        if a == "--log":
            logs.append(Path(next(it)).read_text(errors="replace"))
        elif a == "--check":
            check = True
        else:
            runs.append(a)
    for r in runs:
        logs.append(subprocess.run(["gh", "run", "view", r, "--log"], cwd=ROOT, check=True,
                                   capture_output=True, text=True, errors="replace").stdout)
    old, header = read_table()
    reg = {s for s in registered() if s.startswith("tsymex_")}
    if check:
        missing = sorted(reg - set(old))
        print(f"{len(old)} suites timed, {len(missing)} registered tsymex_* suites untimed")
        for s in missing:
            print("  untimed:", s)
        return 0
    if not logs:
        print(__doc__)
        return 2
    seen = defaultdict(list)
    for text in logs:
        for s, sec in parse(text).items():
            seen[s].append(sec)
    table = {s: v for s, v in old.items() if s in reg}
    for s, v in seen.items():
        if s in reg:
            table[s] = statistics.mean(v)
    what = ", ".join(runs) if runs else f"{len(logs)} saved log(s)"
    lines = [
        "# RFC-0005 S8cm: seconds to compile and run each suite on symex-mingw",
        f"# (mean over runs {what}). Written by scripts/ci-suite-times.py;",
        "# read by scripts/derive-ci-suites.ps1 to place the corpus shards.",
    ]
    lines += [f"{s}\t{table[s]:.1f}" for s in sorted(table)]
    TABLE.write_text("\n".join(lines) + "\n")
    print(f"{len(table)} suites ({len(seen)} measured in these runs) -> {TABLE.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
