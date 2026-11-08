## RFC-0016 section 8.2: render `docs/rfc-data/0016-worklist.toml` into the work-list
## tables of `docs/rfc/0016-native-parity-hardening.md`, between the
## `<!-- worklist:begin NAME -->` / `<!-- worklist:end NAME -->` markers.
##
##   render_worklist check   exit 1 if the committed RFC differs from the render
##                           (the staleness check; CI's `pins` job). Default.
##   render_worklist write   rewrite the RFC's marked regions in place.
##
## Run it with scripts/check-worklist.sh [check|write] (podman, or the host's
## nim under NELLI_HOST=1). The TOML reader and the renderer are
## tests/worklist_toml.nim, which tests/tsymex_0016_universe.nim (with tests/rfc0016_ids.nim) also uses.
import std/os
import ../tests/worklist_toml

const
  root = currentSourcePath().parentDir() / ".."
  tomlPath = root / "docs" / "rfc-data" / "0016-worklist.toml"
  rfcPath = root / "docs" / "rfc" / "0016-native-parity-hardening.md"

proc main(): int =
  let mode = if paramCount() >= 1: paramStr(1) else: "check"
  if mode notin ["check", "write"]:
    stderr.writeLine "usage: render_worklist [check|write]"
    return 2
  let w = parseWorklist(readFile(tomlPath), "docs/rfc-data/0016-worklist.toml")
  var bad = w.validate()
  let have = readFile(rfcPath)
  let (want, problems) = renderRfc(have, w)
  bad.add problems
  if bad.len > 0:
    for b in bad: stderr.writeLine "worklist: " & b
    return 1
  if want == have:
    echo "worklist: the RFC's tables match the render (" & $w.rows.len &
         " rows, " & $w.tables.len & " tables)"
    return 0
  if mode == "write":
    writeFile(rfcPath, want)
    echo "worklist: rewrote the RFC's tables (" & $w.rows.len & " rows)"
    return 0
  stderr.writeLine "worklist: docs/rfc/0016-native-parity-hardening.md differs " &
    "from the render of docs/rfc-data/0016-worklist.toml (edit the TOML, then " &
    "scripts/check-worklist.sh write):\n" & lineDiff(have, want)
  return 1

quit main()
