## Report rendering — text / JSON / JUnit / GitHub annotation.
##
## A deep module by Ousterhout's criterion: 250 LOC of multi-format
## serialization hidden behind `renderReport(r, format)`. The four
## built-in formats cover the CI/tooling matrix; users wanting a custom
## format can write their own renderer against `Report[T]`'s data.

import std/[options, tables, algorithm, strutils]
import ../strategy, ../optbox
import ./types

# `renderDisplayed` is internal — it bridges the strategy's optional
# display proc to the rendered string. Phases call it at Report
# construction time; render layer just reads `Report.displayed`.

proc renderDisplayed*[T](s: Strategy[T], value: Opt[T]): string =
  ## Apply the strategy's optional `display` proc to a value.
  if s.display != nil and value.isSome: s.display(value.get) else: ""

type OutputFormat* = enum
  ofText, ofJson, ofJunit, ofGithubAnnotation

proc displayCounterexample*[T](r: Report[T]): string =
  ## Prefer the custom `displayed` string; fall back to `$value` or a
  ## "strategy raised" marker.
  if r.displayed.len > 0: r.displayed
  elif r.counterexample.isSome: $r.counterexample.get
  else: "<none — strategy raised; see choices>"

proc crashDetailField[T](r: Report[T]): string =
  ## R31: the kind-specific field of `r.crash`, rendered as `key=value`
  ## (empty string when `r.crash` is `none`). Shared by every renderer
  ## below so a future `CrashKind` arm only needs updating here.
  if r.crash.isNone: return ""
  let c = r.crash.get
  case c.kind
  of ckException:    "defect=" & c.defect
  of ckSignal:        "signal=" & $c.signal
  of ckExitCode:      "exitCode=" & $c.exitCode
  of ckWinException:  "code=0x" & toHex(c.code)

proc crashTypeLabel[T](r: Report[T]): string =
  ## R31: a short, attribute/param-safe label identifying the crash —
  ## the exception name for `ckException` (the only kind `forAll` itself
  ## ever populates), or a `<field>:<value>` tag for the external-target
  ## kinds so JUnit's `type=` attribute and the GitHub annotation's
  ## `title=` param stay meaningful if a future caller ever populates
  ## those on a `forAll` report. Empty when `r.crash` is `none`.
  if r.crash.isNone: return ""
  let c = r.crash.get
  case c.kind
  of ckException:    c.defect
  of ckSignal:        "signal:" & $c.signal
  of ckExitCode:      "exitCode:" & $c.exitCode
  of ckWinException:  "winException:0x" & toHex(c.code)

proc repro*[T](r: Report[T]): string =
  ## Multi-line copy-pasteable repro string.
  result = "outcome=" & $r.outcome & "\n"
  result &= "examples=" & $r.examples & "\n"
  result &= "seed=" & $r.seed & "\n"
  if r.dbReplays > 0:
    result &= "db_replays=" & $r.dbReplays & "\n"
  if r.outcome in {otFalsified, otFlaky}:
    result &= "counterexample=" & displayCounterexample(r) & "\n"
    if r.message.len > 0:
      result &= "message=" & r.message & "\n"
    if r.crash.isSome:
      # R31: surface the structured crash identity, not just the free-text
      # `message` it was derived from.
      result &= "crash_kind=" & $r.crash.get.kind & "\n"
      result &= "crash_" & crashDetailField(r) & "\n"
    for (label, value) in r.notes:
      result &= "note[" & label & "]=" & value & "\n"
    if r.choices.len > 0:
      if r.necessity.len == r.choices.len:
        result &= "choices:\n"
        for i in 0 ..< r.choices.len:
          let tag = case r.necessity[i]
                    of nNecessary: "[necessary]"
                    of nFree:      "[free]"
                    of nUnknown:   "[?]"
          result &= "  " & $r.choices[i] & " " & tag & "\n"
      else:
        result &= "choices=" & $r.choices & "\n"
  if r.printEvents and
     (r.events.categorical.len > 0 or r.events.numeric.len > 0):
    result &= "[events]\n"
    var catLabels: seq[string]
    for k in r.events.categorical.keys: catLabels.add k
    catLabels.sort()
    var total = 0
    for k in catLabels: total += r.events.categorical[k]
    for k in catLabels:
      let n = r.events.categorical[k]
      let pct = 100.0 * float(n) / float(max(1, total))
      result &= "  " & k & " = " & $n & " (" & $pct.formatFloat(ffDecimal, 1) & "%)\n"
    var numLabels: seq[string]
    for k in r.events.numeric.keys: numLabels.add k
    numLabels.sort()
    for k in numLabels:
      let s = r.events.numeric[k]
      result &= "  " & k & ": n=" & $s.count &
                " min=" & s.mn.formatFloat(ffDecimal, 3) &
                " mean=" & s.mean.formatFloat(ffDecimal, 3) &
                " p50=" & s.p50.formatFloat(ffDecimal, 3) &
                " p90=" & s.p90.formatFloat(ffDecimal, 3) &
                " p99=" & s.p99.formatFloat(ffDecimal, 3) &
                " max=" & s.mx.formatFloat(ffDecimal, 3) & "\n"

proc xmlEscape(s: string): string =
  result = newStringOfCap(s.len)
  for c in s:
    case c
    of '<': result.add "&lt;"
    of '>': result.add "&gt;"
    of '&': result.add "&amp;"
    of '"': result.add "&quot;"
    of '\'': result.add "&apos;"
    else: result.add c

proc jsonEscape(s: string): string =
  result = newStringOfCap(s.len + 2)
  for c in s:
    case c
    of '\\': result.add "\\\\"
    of '"':  result.add "\\\""
    of '\n': result.add "\\n"
    of '\r': result.add "\\r"
    of '\t': result.add "\\t"
    else:
      if ord(c) < 0x20: result.add "\\u00" & toHex(ord(c), 2).toLowerAscii
      else: result.add c

proc renderJson[T](r: Report[T]): string =
  result = "{"
  result &= "\"outcome\":\"" & $r.outcome & "\""
  result &= ",\"examples\":" & $r.examples
  result &= ",\"seed\":" & $r.seed
  if r.dbReplays > 0:
    result &= ",\"dbReplays\":" & $r.dbReplays
  if r.message.len > 0:
    result &= ",\"message\":\"" & jsonEscape(r.message) & "\""
  if r.counterexample.isSome or r.displayed.len > 0:
    result &= ",\"counterexample\":\"" &
              jsonEscape(displayCounterexample(r)) & "\""
  else:
    result &= ",\"counterexample\":null"
  if r.notes.len > 0:
    result &= ",\"notes\":["
    for i, n in r.notes:
      if i > 0: result &= ","
      result &= "{\"label\":\"" & jsonEscape(n[0]) &
                "\",\"value\":\"" & jsonEscape(n[1]) & "\"}"
    result &= "]"
  if r.crash.isSome:
    # R31: structured crash identity, additive to the pre-existing
    # free-text `message` — a JSON consumer no longer has to grep
    # `message` prose to learn `kind`/`defect`.
    let c = r.crash.get
    result &= ",\"crash\":{\"kind\":\"" & $c.kind & "\""
    case c.kind
    of ckException:
      result &= ",\"defect\":\"" & jsonEscape(c.defect) & "\""
    of ckSignal:
      result &= ",\"signal\":" & $c.signal
    of ckExitCode:
      result &= ",\"exitCode\":" & $c.exitCode
    of ckWinException:
      result &= ",\"code\":" & $c.code
    result &= "}"
  if r.dbErrors.len > 0:
    result &= ",\"dbErrors\":["
    for i, e in r.dbErrors:
      if i > 0: result &= ","
      result &= "\"" & jsonEscape(e) & "\""
    result &= "]"
  result &= "}"

proc renderJunit[T](r: Report[T], testName: string,
                    suiteName: string = "nelli"): string =
  let failures = if r.outcome in {otFalsified, otFlaky, otExhausted}: 1 else: 0
  result = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
  result &= "<testsuite name=\"" & xmlEscape(suiteName) &
            "\" tests=\"1\" failures=\"" & $failures & "\">\n"
  result &= "  <testcase name=\"" & xmlEscape(testName) & "\">\n"
  if failures > 0:
    let body = displayCounterexample(r) & "\n" & r.message
    result &= "    <failure message=\"" & xmlEscape(r.message) & "\""
    if r.crash.isSome:
      # R31: JUnit's own convention for "what raised" is the `type`
      # attribute (normally an exception class name) — additive, so a
      # non-crash falsification's `<failure>` tag is byte-for-byte
      # unchanged from before.
      result &= " type=\"" & xmlEscape(crashTypeLabel(r)) & "\""
    result &= ">"
    result &= xmlEscape(body)
    result &= "</failure>\n"
  result &= "  </testcase>\n"
  result &= "</testsuite>\n"

proc renderGithub[T](r: Report[T], testName: string): string =
  let level = if r.outcome in {otFalsified, otFlaky, otExhausted}: "error"
              else: "notice"
  let cx = displayCounterexample(r)
  # R31: GitHub's workflow-command annotations take optional `key=value`
  # params before the `::` message separator — `title` is the one that
  # actually surfaces in the GitHub UI's annotation summary, so a crash
  # gets its exception name there rather than only inside the free-text
  # message. Additive: absent (empty `params`) leaves a non-crash
  # annotation's `::error::...`/`::notice::...` prefix unchanged.
  let params = if r.crash.isSome: " title=" & crashTypeLabel(r) else: ""
  let crashSuffix = if r.crash.isSome: "; crash=" & $r.crash.get.kind else: ""
  result = "::" & level & params & "::" & testName & " — " & $r.outcome &
           " (counterexample: " & cx & "; seed=" & $r.seed & crashSuffix & ")"

proc renderReport*[T](r: Report[T], format = ofText,
                      testName = "property"): string =
  ## Serialize `r` in the chosen format. `ofText` matches `repro(r)`.
  case format
  of ofText:             repro(r)
  of ofJson:             renderJson(r)
  of ofJunit:            renderJunit(r, testName)
  of ofGithubAnnotation: renderGithub(r, testName)
