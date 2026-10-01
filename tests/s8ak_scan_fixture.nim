## RFC-0005 S8ak fixture source for `extractTopLevelNames`/
## `extractTopLevelMacroNames` (item 2). Exercised by `staticRead`/
## `parseStmt` only -- this file is never imported or compiled as code, so
## it need only be syntactically PARSEABLE, not semantically valid (nothing
## here is ever typechecked: no type referenced below exists).
##
## Deliberately NOT named `tests/t*.nim`: excluded from `scripts/sweep.sh`'s
## sweep glob and from every CI leg's derived/named-contract corpus, and not
## listed in `nelli.nimble`'s `test` task, so it never runs as a suite of
## its own.

proc
    `s8akSplitKeywordOp`*(a, b: int): int =
  ## RFC-0005 S8ak RED fixture: the `proc` keyword and the routine's own
  ## name sit on DIFFERENT physical lines (probed, confirmed this parses:
  ## `parseStmt` returns a normal `nnkProcDef`). The OLD column-0 scan
  ## requires `line.startsWith("proc ")` on a SINGLE line; a line containing
  ## only `"proc"` (no trailing space -- the name is on the next line) fails
  ## that check outright, so the name is never even searched for on the
  ## continuation line: a genuine false negative, not a parsing nuance.
  a + b

proc `s8akOrdinaryBacktickOp`*(a, b: int): bool =
  ## Already-correct case (single physical line, backtick name): pinned so
  ## the new `parseStmt`-based walker is proven not to regress the one
  ## shape the old scan already got right, not only to fix the
  ## split-keyword gap above.
  a == b

proc s8akMultiLineParams*(
    a: int,
    b: int,
    c: int
  ): int =
  ## A signature whose PARAMETER LIST spans several lines -- already
  ## handled correctly by the old scan too (only the first line matters for
  ## name extraction there), but pinned here since the slice's own brief
  ## names "multi-line ... signatures" as a required case.
  a + b + c

macro
    s8akSplitKeywordMacro*(x: static int): untyped =
  ## Same split-keyword gap as `s8akSplitKeywordOp` above, for
  ## `extractTopLevelMacroNames` specifically -- the production macro-count
  ## pipeline (`realScopeMacroNames`) uses that scan, not the general one.
  newLit(x)
