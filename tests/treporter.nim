import std/[unittest, json, strutils]
import nelli

suite "renderReport: built-in output formats":
  test "ofText: same content as repro()":
    let r = forAll(integers(0, 100),
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 100, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 100))
    check r.outcome == otFalsified
    check renderReport(r, ofText) == repro(r)

  test "ofJson: parses as JSON and carries outcome + counterexample":
    let r = forAll(integers(0, 100),
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 100, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 100))
    check r.outcome == otFalsified
    let text = renderReport(r, ofJson)
    # Must parse as JSON.
    let parsed = parseJson(text)
    check parsed["outcome"].getStr == "otFalsified"
    check parsed["seed"].kind == JInt
    check parsed.hasKey("counterexample")

  test "ofJunit: emits a <testcase> wrapped in <testsuite>":
    let r = forAll(integers(0, 100),
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 100, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 100))
    let text = renderReport(r, ofJunit, testName = "x must be small")
    check "<testsuite" in text
    check "<testcase" in text
    check "x must be small" in text
    # A falsifying outcome is a `<failure/>`.
    check "<failure" in text

  test "ofGithubAnnotation: emits ::error:: on failure":
    let r = forAll(integers(0, 100),
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 100, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 100))
    let text = renderReport(r, ofGithubAnnotation, testName = "x small")
    check text.startsWith("::error")
    check "x small" in text

suite "renderReport: R31 structured crash fields (Report.crash) reach every format":
  proc crashingReport(): Report[int] =
    proc crashesAtBoundary(x: int) =
      doAssert x < 500, "must stay below 500"
    forAll(integers(0, 1000), crashesAtBoundary,
           Settings(maxExamples: 300, seed: 42))

  test "precondition: forAll actually populates Report.crash for this fixture":
    let r = crashingReport()
    check r.outcome == otFalsified
    check r.crash.isSome
    check r.crash.get.kind == ckException
    check r.crash.get.defect == "AssertionDefect"

  test "ofText / repro(): crash_kind and crash_defect lines appear":
    let r = crashingReport()
    let text = renderReport(r, ofText)
    check renderReport(r, ofText) == repro(r)
    check "crash_kind=ckException" in text
    check "crash_defect=AssertionDefect" in text

  test "ofJson: crash object carries kind and defect":
    let r = crashingReport()
    let parsed = parseJson(renderReport(r, ofJson))
    check parsed.hasKey("crash")
    check parsed["crash"]["kind"].getStr == "ckException"
    check parsed["crash"]["defect"].getStr == "AssertionDefect"

  test "ofJunit: <failure> carries a type attribute naming the defect":
    let r = crashingReport()
    let text = renderReport(r, ofJunit, testName = "crash test")
    check "<failure" in text
    check "type=\"AssertionDefect\"" in text

  test "ofGithubAnnotation: title param and crash= suffix name the defect":
    let r = crashingReport()
    let text = renderReport(r, ofGithubAnnotation, testName = "crash test")
    check text.startsWith("::error title=AssertionDefect::")
    check "crash=ckException" in text

  test "a non-crash falsification is unaffected in every format (no crash_/type=/title= addition)":
    let r = forAll(integers(0, 100),
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 100, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 100))
    check r.crash.isNone
    check "crash_kind=" notin renderReport(r, ofText)
    let parsed = parseJson(renderReport(r, ofJson))
    check not parsed.hasKey("crash")
    check "type=\"" notin renderReport(r, ofJunit, testName = "x")
    check "title=" notin renderReport(r, ofGithubAnnotation, testName = "x")
