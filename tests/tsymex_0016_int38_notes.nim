## RFC-0016 INT-38 (0005 review R6-07): the `:notes` record is not torn by a
## re-save that fails part-way.
##
## A cold run's hints, diagnostics and undefined-behaviour entries ride one
## record beside its verdict: a head (`:notes`, holding the hints and the
## counts) and one slot per diagnostic or undefined entry. The head was
## written last, so a first save that failed part-way read back empty. But a
## RE-save over an earlier record left that record's head in place while it
## rewrote the slots, so a failure part-way read back the new run's first
## diagnostics beside the old run's last ones, under the old run's hints.
## Now the head is made unreadable before any slot is touched: every load
## after a failed re-save is the whole old record, the whole new one, or
## empty, never a mix.
import std/[unittest, tables, strutils, sequtils]
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime, canonicalize, symex_cache]
from nelli/smt/admission import cellKey, axConstruct
import nelli/engine/types
import ./s8cu_helpers

proc diags(tag: string): seq[FindingDiagnostic] =
  @[FindingDiagnostic(raisedTypeId: "ValueError", raisedMsg: tag & "0"),
    FindingDiagnostic(raisedTypeId: "IOError", raisedMsg: tag & "1"),
    FindingDiagnostic(raisedTypeId: "KeyError", raisedMsg: tag & "2")]

proc undefs(tag: string): seq[FindingUndefined] =
  @[FindingUndefined(kind: "ukA", site: tag & "0"),
    FindingUndefined(kind: "ukB", site: tag & "1")]

proc hints(tag: string): seq[FindingHint] =
  @[FindingHint(kind: seUnsupportedRegex, severity: sevHint,
                msg: tag & "-hint")]

proc tagOf(n: CachedNotes): seq[string] =
  ## The run each part of a loaded record came from.
  for h in n.hints: result.add h.msg.split('-')[0]
  for d in n.diagnostics: result.add d.raisedMsg[0 ..< ^1]
  for u in n.undefined: result.add u.site[0 ..< ^1]

suite "INT-38: the notes record is never torn":

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 413

  test "a re-save that fails part-way reads back whole or not at all":
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    var torn: seq[string]
    var failures = 0
    for failAt in 1 .. 8:
      let db0 = inMemoryDatabase()
      var errors0: seq[string] = @[]
      saveSymexNotesImpl(db0, prog, target, defaultSymexSettings(),
                         hints("old"), diags("old"), undefs("old"), errors0)
      check errors0.len == 0
      var db = db0
      var n = 0
      let inner = db0.saveWithMetaImpl
      let plain = db0.saveImpl
      db.saveWithMetaImpl = proc (t: string; c: seq[ChoiceNode];
                                  m: Table[string, string]; mx: int) =
        inc n
        if n == failAt: raise newException(IOError, "injected")
        inner(t, c, m, mx)
      db.saveImpl = proc (t: string; c: seq[ChoiceNode]; mx: int) =
        inc n
        if n == failAt: raise newException(IOError, "injected")
        plain(t, c, mx)
      var errors: seq[string] = @[]
      saveSymexNotesImpl(db, prog, target, defaultSymexSettings(),
                         hints("new"), diags("new"), undefs("new"), errors)
      if errors.len > 0: inc failures
      var loadErrors: seq[string] = @[]
      let got = loadSymexNotesImpl(db0, prog, target, defaultSymexSettings(),
                                   loadErrors)
      let tags = tagOf(got)
      let whole =
        (tags.len == 0) or
        (tags.len == 6 and (tags.allIt(it == "old") or tags.allIt(it == "new")))
      if not whole: torn.add "failAt=" & $failAt & ": " & $tags
    check failures >= 6        # the injection reached every write
    check torn.len == 0        # was: new diagnostics under old ones' head
    pinNever(cellKey(axConstruct, "cache/record/notes"), torn.len == 0,
      "a notes record re-saved over another and broken part-way reads back " &
      "as the old record, the new one or empty, never a mix")

  test "a whole re-save replaces every part":
    let prog = SymexProgram(body: mkBlock(@[]))
    let target = tAssertionViolation()
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexNotesImpl(db, prog, target, defaultSymexSettings(),
                       hints("old"), diags("old"), undefs("old"), errors)
    saveSymexNotesImpl(db, prog, target, defaultSymexSettings(),
                       hints("new"), diags("new"), undefs("new"), errors)
    check errors.len == 0
    let got = loadSymexNotesImpl(db, prog, target, defaultSymexSettings(),
                                 errors)
    check tagOf(got) == @["new", "new", "new", "new", "new", "new"]
