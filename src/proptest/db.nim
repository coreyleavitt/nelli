## The example database — "remembers your bugs."
##
## Stores the (already-shrunk) choice sequence of each falsified property keyed
## by an opaque test ID. On the next run, the engine's reuse phase replays the
## stored sequences before random generation; if any still falsifies, the test
## reports immediately with the known counterexample — so a regression is
## near-instant to re-catch and shrinking cost is not re-paid.
##
## On-disk layout: `<dbPath>/<safeKey>.bin`, each file holding the binary form
## of one choice sequence (via `toBytes`/`fromBytes`). One stored sequence per
## test id in this MVP; multi-corpus storage is an extension.

import std/[os, strutils]
import ./choice, ./serialize

type
  ExampleDB* = object
    path*: string

proc newExampleDB*(path: string): ExampleDB =
  ## A database rooted at `path` (a directory; created on first save).
  ExampleDB(path: path)

proc safeKey(testId: string): string =
  ## Map a test id to a filename-safe string. Filesystems vary in what they
  ## accept; replace anything outside `[A-Za-z0-9._-]` with `_`.
  result = newStringOfCap(testId.len)
  for c in testId:
    if c.isAlphaAscii or c.isDigit or c in {'.', '_', '-'}:
      result.add c
    else:
      result.add '_'

proc keyPath(db: ExampleDB, testId: string): string =
  db.path / (safeKey(testId) & ".bin")

proc bytesToStr(b: seq[byte]): string =
  result = newString(b.len)
  for i, v in b: result[i] = char(v)

proc strToBytes(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  for i, c in s: result[i] = byte(c)

proc save*(db: ExampleDB, testId: string, choices: seq[ChoiceNode]) =
  ## Persist `choices` under `testId`, overwriting any previous entry.
  createDir(db.path)
  writeFile(db.keyPath(testId), bytesToStr(toBytes(choices)))

proc load*(db: ExampleDB, testId: string): seq[ChoiceNode] =
  ## Read the stored choice sequence for `testId`, or `@[]` if none exists.
  let p = db.keyPath(testId)
  if not fileExists(p): return @[]
  fromBytes(strToBytes(readFile(p)))
