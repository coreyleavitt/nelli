#!/usr/bin/env bash
# RFC-0016 INT-34: the public surface of `src/nelli/smt/runtime.nim`, as a
# sorted list a module cut can be diffed against (the cut must leave it
# unchanged: same names, same public fields, same enum members).
#
# Each line is one of
#   name <N>              a public name: declared in runtime.nim with `*`, or
#                         re-exported by it (`nim doc`'s Exports section)
#   type <N> <field|member> ...
#                         for each public type, its public fields (object) or
#                         members (enum), from `nim jsondoc` of whichever
#                         module declares it (runtime.nim or a leaf it
#                         re-exports from)
#
# usage: scripts/int34-public-names.sh <out.txt>
#   Runs in the nelli dev image (podman), like scripts/dt.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
out="${1:?usage: int34-public-names.sh <out.txt>}"
img="localhost/nelli-dev:${NELLI_IMAGE:-latest}"
podman run --rm \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work "$img" bash -c '
set -e
# `nim doc` writes the page, then fails to copy nimdoc.css (the image ships
# no doc/): the page is what is read, so its own exit status is not.
nim doc --hints:off --threads:on --outdir:/tmp/hd src/nelli/smt/runtime.nim >/dev/null 2>&1 || true
test -s /tmp/hd/runtime.html
mods="runtime"
[ -f src/nelli/smt/walk_types.nim ] && mods="$mods walk_types"
for m in $mods; do
  nim jsondoc --hints:off --threads:on --outdir:/tmp/jd src/nelli/smt/$m.nim >/dev/null 2>&1
done
python3 - $mods <<"PY"
import html, json, re, sys
names = set()
decl = {}
for m in sys.argv[1:]:
    for e in json.load(open(f"/tmp/jd/{m}.json"))["entries"]:
        if m == "runtime":
            names.add(e["name"])
        if e["type"] == "skType":
            decl[e["name"]] = e["code"]
page = open("/tmp/hd/runtime.html").read()
at = page.find(">Exports</a></h1>")
if at >= 0:
    body = page[at:page.find("</dl>", at)]
    for n in re.findall(r"<span class=\"Identifier\">([^<]+)</span>", body):
        names.add(html.unescape(n))
lines = [f"name {n}" for n in sorted(names)]
for n in sorted(names):
    code = decl.get(n)
    if code is None:
        continue
    parts = []
    head, _, rest = code.partition("\n")
    if re.search(r"=\s*enum\b", head):
        text = re.sub(r"##[^\n]*", "", code.split("enum", 1)[1])
        parts = [p.split("=")[0].strip() for p in re.split(r"[,\n]", text)]
    else:
        for l in rest.split("\n"):
            l = re.sub(r"##.*", "", l).strip()
            l = re.sub(r"^case\s+", "", l)
            m = re.match(r"([A-Za-z_][\w]*\*?(\s*,\s*[A-Za-z_][\w]*\*?)*)\s*:", l)
            if m and not l.startswith("of "):
                parts += [p.strip() for p in m.group(1).split(",")]
    parts = [p for p in parts if p]
    lines.append(f"type {n} " + " ".join(parts))
print("\n".join(lines))
PY
' > "$out"
wc -l < "$out"
