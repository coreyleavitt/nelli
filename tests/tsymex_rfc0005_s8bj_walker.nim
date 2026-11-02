## RFC-0005 S8bj -- walker verdicts on the regex constructs S8bb left
## undecided or declined, the walker-version floor, and the libpcre engine
## in the cache key.
##
## Each pin is a verdict `std/re` decides concretely (PCRE 8.45's
## interpreter; under a JIT-enabled libpcre the unanchored pins are the
## walker's decline, `sxUnknown`).
import std/[unittest, strutils, re, times]
import pcre
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/pcre_engine

proc jitEngine(): bool =
  var v: cint
  discard pcre.config(pcre.CONFIG_JIT, addr v)
  v == 1

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let t0 = epochTime()
  let r = symexFind(sut, tLabel(label))
  echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t0,
                                                     ffDecimal, 1), " s"
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

proc commitFind(s: string) =
  # `a(*COMMIT)b|.`: an `a` not followed by `b` ends the search.
  if s.len == 2 and s.find(re"a(*COMMIT)b|.") == -1:
    symexTarget("bj_commit_find")

proc skipFind(s: string) =
  # `aa(*SKIP)b|a+` on "aaab": the attempt at 0 reads "aa", fails at `b`
  # and backtracks into the SKIP: the search resumes at 2, never trying
  # `a+` at 0.
  if s == "aaab" and s.find(re"aa(*SKIP)b|a+") != 2:
    symexTarget("bj_skip_find")

proc thenLen(s: string) =
  # THEN jumps to the next alternative of its group: "ab" matches by `ab`.
  if s.len == 2 and s.matchLen(re"(?:a(*THEN)c|ab)") == 2:
    symexTarget("bj_then_len")

proc multiStart(s: string) =
  if s.len == 3 and s[0] == 'b' and s.find(re"(?m)^a") == 2:
    symexTarget("bj_multi_start")

proc utfInvalid(s: string) =
  # An invalid UTF-8 subject: PCRE_ERROR_BADUTF8.
  if s.len == 1 and s.find(re"(*UTF).") == -10:
    symexTarget("bj_utf_invalid")

proc utfNever(s: string) =
  # `.` in UTF mode never matches a lone continuation byte...
  if s.len == 1 and s.matchLen(re"(*UTF).") == 1 and ord(s[0]) >= 0x80:
    symexTarget("bj_utf_never")

proc limitZero(s: string) =
  # LIMIT_MATCH=0: an error as soon as an attempt is made; one byte is
  # below the minimum length (2), so no attempt is made.
  if s.len == 1 and s.matchLen(re"(*LIMIT_MATCH=0)ab") == -8:
    symexTarget("bj_limit_zero")

proc limitZeroHit(s: string) =
  if s.len == 2 and s.matchLen(re"(*LIMIT_MATCH=0)ab") == -8:
    symexTarget("bj_limit_zero_hit")

proc crlfSkip(s: string) =
  # S8bb declined this search (`crlfSkipSeen`); the interpreter's start
  # bits try the LF of "\r\n".
  if s.len == 2 and s.find(re"(*CRLF)[\x09-\x0b]\z") == 1:
    symexTarget("bj_crlf_skip")

proc replaceVerb(s: string) =
  if s == "ab" and s.replace(re"a(*COMMIT)x|.", "-") != "ab":
    symexTarget("bj_replace_commit")

suite "S8bj: walker verdicts":

  test "COMMIT ends the search: sxSat, std/re's witness":
    let r = verdict(commitFind, "bj_commit_find")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 2 and r.witness[0].find(re"a(*COMMIT)b|.") == -1

  test "SKIP's landing: sxUnsat":
    check verdict(skipFind, "bj_skip_find").status == sxUnsat

  test "THEN's catcher: sxSat, std/re's witness":
    let r = verdict(thenLen, "bj_then_len")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].matchLen(re"(?:a(*THEN)c|ab)") == 2

  test "(?m)^ after a newline: sxSat":
    let r = verdict(multiStart, "bj_multi_start")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].find(re"(?m)^a") == 2

  test "UTF: an invalid subject is -10: sxSat":
    let r = verdict(utfInvalid, "bj_utf_invalid")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].find(re"(*UTF).") == -10

  test "UTF: `.` reads whole characters: sxUnsat":
    check verdict(utfNever, "bj_utf_never").status == sxUnsat

  test "LIMIT_MATCH=0: the error iff an attempt is made":
    check verdict(limitZero, "bj_limit_zero").status == sxUnsat
    let r = verdict(limitZeroHit, "bj_limit_zero_hit")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].matchLen(re"(*LIMIT_MATCH=0)ab") == -8

  test "the CRLF start skip: modelled on the interpreter":
    # RFC-0005 S8bt: and on PCRE 8.37's JIT (`pcre_jit.nim`), which the
    # walker now models rather than declining.
    let r = verdict(crlfSkip, "bj_crlf_skip")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].find(re"(*CRLF)[\x09-\x0b]\z") == 1

  test "replace with a verb: sxUnsat":
    check verdict(replaceVerb, "bj_replace_commit").status == sxUnsat

suite "S8bj: versions and the cache key":

  test "the walker version is at least 211":
    check parseInt(symexWalkerVersion) >= 211

  test "the cache key records the libpcre engine":
    # The engine and the library version (`pcre_version()`'s first word).
    let v = $pcre.version()
    check pcreVersion() == v
    check pcreEngineName() ==
      (if jitEngine(): "pcre-jit-" else: "pcre-interp-") & v.split(' ')[0]
    check pcreRunsJit() == jitEngine()
