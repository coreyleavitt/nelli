## scripts/symex_boundary_report.nim
##
## Phase 9 cycle 11 — module-boundary report for the symex package.
##
## Walks every `import` statement in `src/proptest/symex.nim` and
## `src/proptest/smt/*.nim`, classifies each into one of four
## buckets, and prints a Markdown report. The classification
## tells us what would need to move / be re-routed if symex were
## extracted as a standalone `nim-symex` library.
##
## Run with `nim r --hints:off scripts/symex_boundary_report.nim`
## from the proptest repo root.
##
## Categories:
##   in-package      — within `proptest/smt/**` or `proptest/symex`
##   proptest-shared — proptest internals symex needs (engine,
##                     choice, db, optbox, …). Extraction targets.
##   nim-stdlib      — std/* — free.
##   substrate       — `z3` (nim-z3 package) — already a separate
##                     library; carries over unchanged.

import std/[os, strutils, sequtils, tables, algorithm]

# ---- Sources --------------------------------------------------------------

const repoRoot = currentSourcePath.parentDir.parentDir
const symexRoot = repoRoot / "src" / "proptest"

proc collectSources(): seq[string] =
  result.add symexRoot / "symex.nim"
  for f in walkDir(symexRoot / "smt"):
    if f.kind == pcFile and f.path.endsWith(".nim"):
      result.add f.path

# ---- Import-line lexing ---------------------------------------------------
#
# A pragmatic line-based scan: `import x, y as z`, `import std/[a, b]`,
# and `from x import y` are the three shapes Nim accepts. We extract
# the bare module path(s) without trying to be a full parser.

proc moduleNamesFromImport(line: string): seq[string] =
  ## Returns one or more module path strings from a single `import`
  ## or `from … import …` line. Strips `as` aliases and bracket
  ## expansion (`std/[a, b]` → `std/a`, `std/b`).
  var s = line.strip()
  if s.startsWith("from "):
    let rest = s["from ".len..^1]
    let stop = rest.find(" import ")
    if stop < 0: return @[]
    return @[rest[0..<stop].strip()]
  if not s.startsWith("import "):
    return @[]
  s = s["import ".len..^1]
  # Strip trailing comment.
  let hashIdx = s.find('#')
  if hashIdx >= 0: s = s[0..<hashIdx]
  # Bracket form `prefix/[a, b]`.
  if '[' in s:
    let prefix = s[0..<s.find('[')].strip().strip(chars = {'/'})
    let inside = s[s.find('[')+1..<s.find(']')]
    for m in inside.split(','):
      result.add prefix & "/" & m.strip()
    return
  # Comma-separated `a, b, c as alias`.
  for m in s.split(','):
    var name = m.strip()
    let asIdx = name.find(" as ")
    if asIdx >= 0: name = name[0..<asIdx].strip()
    if name.len > 0:
      result.add name

proc readImports(path: string): seq[string] =
  for line in lines(path):
    let stripped = line.strip()
    if stripped.startsWith("import ") or stripped.startsWith("from "):
      result.add moduleNamesFromImport(line)

# ---- Classification -------------------------------------------------------

type Category = enum
  catInPackage      = "in-package"
  catProptestShared = "proptest-shared"
  catNimStdlib      = "nim-stdlib"
  catSubstrate      = "substrate"

proc resolveRelative(srcAbs, importPath: string): string =
  ## Resolve a relative import against its source file's directory.
  ## Returns an absolute path normalised to forward slashes; non-
  ## relative imports come back unchanged.
  if importPath.startsWith("./") or importPath.startsWith("../"):
    let srcDir = srcAbs.parentDir
    return (srcDir / importPath).normalizedPath
  if importPath.startsWith("/"):
    return importPath
  importPath

proc classify(srcAbs, modulePath: string): Category =
  if modulePath.startsWith("std/"):
    return catNimStdlib
  if modulePath == "z3" or modulePath.startsWith("z3/"):
    return catSubstrate
  let resolved = resolveRelative(srcAbs, modulePath)
  # Anything resolving inside `src/proptest/smt/` is in-package.
  let smtDir = symexRoot / "smt"
  if resolved.startsWith(smtDir) or resolved == symexRoot / "symex.nim" or
     resolved == symexRoot / "smt.nim":
    return catInPackage
  # Resolved path under src/proptest/* (but not smt/) — proptest-shared.
  if resolved.startsWith(symexRoot):
    return catProptestShared
  # Unresolved (absolute Nim-package name) — heuristic on the bare path.
  let normalised = modulePath.strip(chars = {'.', '/'})
  if modulePath.startsWith("proptest/") or normalised in [
      "choice", "db", "rng", "shrinker",
      "strategy", "datasource", "coverage", "optbox", "int128"]:
    return catProptestShared
  catProptestShared

# ---- Report ---------------------------------------------------------------

proc main() =
  var sources = collectSources()
  sort(sources)
  var entries: seq[tuple[srcRel, modulePath: string, cat: Category]]
  for src in sources:
    let srcRel = src.relativePath(repoRoot)
    for m in readImports(src):
      entries.add (srcRel, m, classify(src, m))

  # Group by category for the summary; keep the per-source detail
  # for the appendix.
  var counts: Table[Category, int]
  for e in entries:
    counts[e.cat] = counts.getOrDefault(e.cat) + 1

  echo "# symex module-boundary report"
  echo ""
  echo "Generated by `scripts/symex_boundary_report.nim`. Walks every"
  echo "`import` in `src/proptest/symex.nim` and `src/proptest/smt/*.nim`"
  echo "and classifies each. Used by Phase 9 cycle 12"
  echo "(`extraction-checklist.md`) to drive the standalone-`nim-symex`"
  echo "extraction plan."
  echo ""
  echo "## Summary"
  echo ""
  echo "| Category | Count |"
  echo "|---|---|"
  for c in [catInPackage, catProptestShared, catSubstrate, catNimStdlib]:
    echo "| ", $c, " | ", counts.getOrDefault(c), " |"
  echo ""

  echo "## proptest-shared imports (the extraction targets)"
  echo ""
  echo "These are the imports symex makes into proptest internals"
  echo "outside the `smt/` package. Extracting symex requires"
  echo "re-routing each — see `extraction-checklist.md`."
  echo ""
  echo "| Source | Imports |"
  echo "|---|---|"
  var sharedBySource: Table[string, seq[string]]
  for e in entries:
    if e.cat == catProptestShared:
      sharedBySource.mgetOrPut(e.srcRel, @[]).add e.modulePath
  var keys = toSeq(sharedBySource.keys)
  sort(keys)
  for k in keys:
    var mods = sharedBySource[k]
    sort(mods)
    echo "| `", k, "` | ", mods.join(", "), " |"
  echo ""

  echo "## Full import inventory"
  echo ""
  echo "| Source | Module | Category |"
  echo "|---|---|---|"
  for e in entries:
    echo "| `", e.srcRel, "` | `", e.modulePath, "` | ", $e.cat, " |"

when isMainModule:
  main()
