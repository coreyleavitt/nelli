## Shared scan primitives for the source-level regression-audit test suites
## (the "house scan-and-marker technique" `tsymex_r6_n27_placeholder_read_
## audit.nim`'s header describes). Round-6 mechanical-debt slice: these two
## procs were byte-identical, independently copy-pasted, across five audit
## suites (`tsymex_r6_n27_placeholder_read_audit`, `tsymex_phase15_N2_
## kindgate_audit`, `tsymex_phase15_A2a_atomicir_audit`, `tsymex_phase15_A2a_
## chokepoint_audit`, `tsymex_r6_n36_raise_class_audit`). Extracted here so a
## future fix to either applies once instead of drifting across five copies.
##
## Deliberately NOT a home for every scan helper the audits use: each suite's
## other primitives (`fieldNameAt`, `routineVocabWordLenAt`, `matchesAt`, ...)
## look superficially similar but encode different word-boundary/marker rules
## for that suite's own vocabulary -- forcing them into one shared proc would
## couple suites that should stay independently editable. Only genuinely
## byte-identical pieces belong here.

import std/strutils

proc isCommentLine*(trimmed: string): bool =
  ## Nim `#`/`##` doc and ordinary comments both start with `#` once leading
  ## whitespace is stripped. Prose narrating a scanned token (an audit file's
  ## own header included) must never trip a scanner.
  trimmed.startsWith("#")

proc isIdentChar*(c: char): bool = c.isAlphaNumeric or c == '_'
  ## Word-boundary test shared by every audit's separator-aware identifier
  ## matching (so `.seqLenXyz`/`notSeqLen`-style near-misses never match a
  ## bare target-token scan).

# ---------------------------------------------------------------------------
# The runtime family: the one list every source audit of the walker reads.
# ---------------------------------------------------------------------------

import std/os

const
  smtSrcDir* = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt"

  runtimeFamilyFiles* = [
    # The walker proper, and the file still textually included into it.
    "runtime.nim", "runtime_heap.nim",
    # Includes that became real modules (RFC-0016 D3c-3, -4, -5, -7).
    "runtime_exceptions.nim", "runtime_floats.nim", "runtime_closures.nim",
    "runtime_strings.nim",
    # Leaves that code moved into out of `runtime.nim` (RFC-0016 D3c-1, -2,
    # -6, -7): the shared value types, the run state, the sort-checked Z3
    # term builders, the heap algebra, and the string lowering support.
    "symval.nim", "walk_state.nim", "z3check.nim", "heap_model.nim",
    "string_lower_support.nim"]
    ## Every file that holds, or has held, code that was `runtime.nim`'s. A
    ## source audit that pins "the walker's sites of kind K" counts K over THIS
    ## set, never over a hand-picked subset: a file move then changes which
    ## file a site is in, not the total, and an audit written against the
    ## total does not break. A new leaf cut out of `runtime.nim` is added here,
    ## once, and every audit follows it. `tsymex_0016_d3_include_census`
    ## checks that no `runtime*.nim` and no named leaf is missing from it.

proc runtimeFamilySources*(exclude: openArray[string] = []):
    seq[tuple[label, path: string]] =
  ## (repo-relative label, path) for each family file, in list order, less any
  ## basename in `exclude` (an audit whose scope never covered a file says so
  ## at its own call site, with the reason). Read the files at test RUNTIME
  ## with `readFile` (never `staticRead`: MSVC's C2026 string-literal limit).
  for f in runtimeFamilyFiles:
    if f in exclude: continue
    result.add (label: "src/nelli/smt/" & f, path: smtSrcDir / f)
