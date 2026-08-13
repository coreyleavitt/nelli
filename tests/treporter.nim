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
