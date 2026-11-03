#!/usr/bin/env python3
"""Regenerate the RFC-0005 list of pins that flipped a verdict.

RFC-0005 §4.3 requires every flip to be justified through
`checkUnsatOverTaintOnly` where the helper can express it, and says the list
of flips comes from a tool rather than from memory. This is that tool. It
reads git history only, so it needs no compiler and no baseline sweep.

Usage:
    scripts/rfc0005-flips.py [BASE..TIP]          # print the table
    scripts/rfc0005-flips.py --check [BASE..TIP]  # exit 1 if a to-unsat flip
                                                  # has no recorded check

The default range is 6cbfe8f..HEAD, where 6cbfe8f is main when the RFC's work
began. Merge commits are not scanned: every change they carry is in a parent.

A *flip hunk* is a diff hunk under tests/ that removes a line asserting a
verdict status and adds a line asserting a different one. "Different" means
the set of `sx*`/`sf*` statuses named on removed assertion lines and on added
assertion lines disagree, so a re-indented assertion is not a flip. Comments
are ignored, so a comment that merely quotes an old status is not one either.
It is a same-hunk heuristic and has two known limits:

  * a flip whose old and new assertions land in different hunks is missed;
  * a hunk that replaces one test with another counts as a flip even if
    nothing actually moved, so the list can only over-report within a hunk.

An `sxUnsat` flip is *checked* when either the hunk itself uses the helper or
tests/tsymex_rfc0005_s8cr_flips*.nim carries a matching `flip:` marker comment
(`# flip: <short sha> <file stem>`), or a `not-expressible:` marker with the
same shape and a reason.
"""
import re
import subprocess
import sys
from collections import namedtuple
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_RANGE = "6cbfe8f..HEAD"
STATUS = re.compile(r"\b(sx(?:Sat|Unsat|Unknown|Raised)|sf(?:Sat|Unsat|Unknown|Raised))\b")
ASSERT = re.compile(r"\b(check|require|doAssert|assert|expect)\b|==|!=")
HELPER = "checkUnsatOverTaintOnly"
UNSAT = {"sxUnsat", "sfUnsat"}

Flip = namedtuple("Flip", "sha subject path removed added helper line")


def git(*args):
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True,
        errors="replace").stdout


def statuses(lines):
    found = set()
    for line in lines:
        code = line.split("#", 1)[0]
        if HELPER in code:
            found.add("sxUnsat")  # the helper asserts it
        if ASSERT.search(code):
            found.update(STATUS.findall(code))
    return found


def helper_used(lines):
    return any(HELPER in line.split("#", 1)[0] for line in lines)


def hunks_of(diff):
    """Yield (path, new_start, removed_lines, added_lines) per hunk."""
    path, start, removed, added = None, 0, [], []
    for line in diff.splitlines():
        if line.startswith("diff --git "):
            if path is not None and (removed or added):
                yield path, start, removed, added
            path, start, removed, added = None, 0, [], []
        elif line.startswith("+++ "):
            path = line[6:] if line.startswith("+++ b/") else None
        elif line.startswith("@@"):
            if path is not None and (removed or added):
                yield path, start, removed, added
            match = re.search(r"\+(\d+)", line)
            start, removed, added = int(match.group(1)) if match else 0, [], []
        elif line.startswith("-") and not line.startswith("--- "):
            removed.append(line[1:])
        elif line.startswith("+"):
            added.append(line[1:])
    if path is not None and (removed or added):
        yield path, start, removed, added


def flips_in(rev):
    log = git("log", "--no-merges", "--format=%h%x09%s", rev).splitlines()
    for entry in log:
        sha, subject = entry.split("\t", 1)
        diff = git("show", "--format=", "--no-color", "-U3", sha, "--", "tests")
        for path, start, removed, added in hunks_of(diff):
            if not path.startswith("tests/t") or not path.endswith(".nim"):
                continue
            old, new = statuses(removed), statuses(added)
            if not old or not new or old == new or not (new - old):
                continue
            yield Flip(sha, subject, path, sorted(old), sorted(new),
                       helper_used(added), start)


def markers():
    """Return {(sha, stem): (kind, where)} from the S8cr flip suites."""
    found = {}
    pattern = re.compile(r"#\s*(flip|not-expressible):\s*([0-9a-f]{7,})\s+(\S+)")
    for path in sorted((ROOT / "tests").glob("tsymex_rfc0005_s8cr_flips*.nim")):
        for line in path.read_text().splitlines():
            match = pattern.search(line)
            if match:
                found[(match.group(2)[:7], match.group(3))] = (
                    match.group(1), path.name)
    return found


def stem(path):
    return Path(path).stem


def main(argv):
    check = "--check" in argv
    args = [a for a in argv if not a.startswith("--")]
    rev = args[0] if args else DEFAULT_RANGE
    flips = list(flips_in(rev))
    marks = markers()
    to_unsat = [f for f in flips if set(f.added) & UNSAT and not set(f.removed) & UNSAT]
    other = [f for f in flips if f not in to_unsat]

    print(f"# RFC-0005 verdict flips in {rev}: "
          f"{len(flips)} flip hunks, {len(to_unsat)} to unsat, {len(other)} other")
    print("#\n# to-unsat: sha  file:line  old -> new  how it is justified")
    unjustified = []
    for f in to_unsat:
        key = (f.sha[:7], stem(f.path))
        if f.helper:
            how = "helper in hunk"
        elif key in marks:
            how = f"{marks[key][0]} in {marks[key][1]}"
        else:
            how = "NONE"
            unjustified.append(f)
        print(f"{f.sha}  {f.path}:{f.line}  {','.join(f.removed)} -> "
              f"{','.join(f.added)}  {how}")
    print("#\n# other: sha  file:line  old -> new")
    for f in other:
        print(f"{f.sha}  {f.path}:{f.line}  {','.join(f.removed)} -> {','.join(f.added)}")
    if unjustified:
        print(f"# {len(unjustified)} to-unsat flip hunk(s) have no recorded check",
              file=sys.stderr)
    return 1 if check and unjustified else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
