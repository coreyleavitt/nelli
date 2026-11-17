## RFC-0016 H1 INT-26 (WA-1): a `RegexError` reaches `symexFindAllWitnesses`
## through the user exception hierarchy.
##
## `symexFindAllWitnesses` and `symexForAll` used to build their program
## without the user exception hierarchy that `symexFind` passes. 0.9.0 reads an
## exception type it does not know as top (`eeUnknownExnType`), so a named
## `except RegexError` (or `except ValueError`, its parent) was skipped and a
## verdict `symexFind` decided came back `sfUnknown`. W1 pinned a user
## exception type only; `RegexError` needs a PCRE program, which this file
## supplies: a pattern PCRE rejects (`re"a**"`) raises `RegexError` at run
## time, so the handler is reached on every input.
##
## Each row runs the program natively (the label it prints is the oracle) and
## then asks the entry point under test; `symexFind` is asked too, so the
## two entry points are held to the same verdict.
import std/[unittest, sets, re]
import nelli
import nelli/symex
import ./s8cu_helpers

proc rejectedCaught(s: string) =
  try:
    if s.match(re"a**"):
      discard
  except RegexError:
    symexTarget("h1_regex_caught")

proc rejectedCaughtAsParent(s: string) =
  ## `RegexError` is a `ValueError`: the parent's handler takes it.
  try:
    if s.contains(re"[z-a]"):
      discard
  except ValueError:
    symexTarget("h1_regex_parent")

proc rejectedNotReached(s: string) =
  ## The raise is the exit of the `try` body: nothing after it runs.
  try:
    if s.match(re"a**"):
      symexTarget("h1_regex_after")
  except RegexError:
    discard

proc wrongHandler(s: string) =
  ## `RegexError` is not an `IOError`: the handler is not taken, the raise
  ## leaves the routine, and the target after the `try` is not reached.
  try:
    if s.match(re"a**"):
      discard
  except IOError:
    symexTarget("h1_regex_wrong")

proc findingOf(fs: seq[SymexFinding]; label: string): SymexFinding =
  findingFor(fs, tLabel(label))

suite "INT-26: RegexError through symexFindAllWitnesses":

  test "the handler is reached, and is decided, not unknown":
    check "h1_regex_caught" in nativeHits(rejectedCaught("x"))
    let f = findingOf(symexFindAllWitnesses(rejectedCaught,
                                            inMemoryDatabase()),
                      "h1_regex_caught")
    checkpoint $f.status & " " & $f.soundness
    check f.status == sfSat
    check symexFind(rejectedCaught, tLabel("h1_regex_caught")).status == sxSat

  test "the parent type's handler takes it":
    check "h1_regex_parent" in nativeHits(rejectedCaughtAsParent("x"))
    let f = findingOf(symexFindAllWitnesses(rejectedCaughtAsParent,
                                            inMemoryDatabase()),
                      "h1_regex_parent")
    checkpoint $f.status & " " & $f.soundness
    check f.status == sfSat

  test "nothing after the raise is reached":
    check "h1_regex_after" notin nativeHits(rejectedNotReached("x"))
    let f = findingOf(symexFindAllWitnesses(rejectedNotReached,
                                            inMemoryDatabase()),
                      "h1_regex_after")
    checkpoint $f.status & " " & $f.soundness
    check f.status == sfUnsat

  test "an unrelated handler does not take it":
    let f = findingOf(symexFindAllWitnesses(wrongHandler,
                                            inMemoryDatabase()),
                      "h1_regex_wrong")
    checkpoint $f.status & " " & $f.soundness
    check f.status == sfUnsat
