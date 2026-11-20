#!/usr/bin/env bash
# RFC-0016 INT-34: the public surface of a module, as a sorted list a module
# cut can be diffed against (the cut must leave it unchanged: same names, same
# public fields, same enum members).
#
#   (default)   `src/nelli/smt/runtime.nim`, the walker's runtime
#   --symex     `src/nelli/symex.nim`, the `nelli/symex` facade (INT-34 C1)
#
# Each line is one of
#   name <N>              a public name: declared in the module with `*`, or
#                         re-exported by it (`nim doc`'s Exports section)
#   type <N> <field|member> ...
#                         for each public type, its public fields (object) or
#                         members (enum), from `nim jsondoc` of whichever
#                         module declares it (the module or a leaf it
#                         re-exports from, among those listed below)
#
# usage: scripts/int34-public-names.sh [--symex] <out.txt>
#   Runs in the nelli dev image (podman), like scripts/dt.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
mode=runtime
if [ "${1:-}" = "--symex" ]; then mode=symex; shift; fi
out="${1:?usage: int34-public-names.sh [--symex] <out.txt>}"
img="localhost/nelli-dev:${NELLI_IMAGE:-latest}"
podman run --rm \
  -v "$PWD:/work" \
  -v "$HOME/.cache/milpa:/.cache/milpa" \
  -v "$HOME/.cache/milpa:$HOME/.cache/milpa" \
  -w /work "$img" bash -c '
set -e
if [ "$1" = symex ]; then
  top=symex; page=src/nelli/symex.nim
  # the facade and the leaves whose types it re-exports by name
  mods="symex smt/symex_cache"
  [ -f src/nelli/smt/symex_codec.nim ] && mods="$mods smt/symex_codec"
else
  top=runtime; page=src/nelli/smt/runtime.nim
  mods="smt/runtime"
  [ -f src/nelli/smt/walk_types.nim ] && mods="$mods smt/walk_types"
fi
# `nim doc` writes the page, then fails to copy nimdoc.css (the image ships
# no doc/): the page is what is read, so its own exit status is not.
nim doc --hints:off --threads:on --outdir:/tmp/hd "$page" >/dev/null 2>&1 || true
test -s /tmp/hd/$top.html
jsons=""
for m in $mods; do
  nim jsondoc --hints:off --threads:on --outdir:/tmp/jd src/nelli/$m.nim >/dev/null 2>&1
  jsons="$jsons /tmp/jd/$(basename "$m").json"
done
python3 - "$top" $jsons <<"PY"
import html, json, re, sys
top = sys.argv[1]
names = set()
decl = {}
for path in sys.argv[2:]:
    for e in json.load(open(path))["entries"]:
        if path.endswith("/" + top + ".json"):
            names.add(e["name"])
        if e["type"] == "skType":
            decl[e["name"]] = e["code"]
page = open(f"/tmp/hd/{top}.html").read()
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
    elif top == "symex" and re.search(r"=\s*tuple\[", code):
        # the `Cached*` records of the cache (the runtime list predates this
        # arm; no apostrophes here: this body is one single-quoted string)
        text = re.sub(r"##[^\n]*", "", code.split("tuple[", 1)[1])
        parts = re.findall(r"([A-Za-z_]\w*)\s*:", text)
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
' _ "$mode" > "$out"
wc -l < "$out"
