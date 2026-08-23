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
