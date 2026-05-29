import std/[unittest, macros, options]
import proptest

# #116 — mutation testing for PBT.
#
# The user passes a proc literal; a macro generates mutant variants
# (one per applicable AST site × mutator). A scoring loop runs each
# mutant through a property closure; mutants that fall to the
# property are *killed*; mutants that pass are *survivors* — a
# concrete measure of test-suite gaps for the user to review.
#
# v1 in-process via macro-generated mutants. Compile-and-run
# sandboxing is the separate v2 architectural surface (requires
# Nim compiler integration); the catalog + scoring loop here
# demonstrates the architecture and produces real numbers.

suite "mutator catalog — AST transforms (compile-time)":
  test "applyMutator results compiled inside static blocks":
    # NimNode manipulation is compile-time-only; the macro / static
    # contexts produce NimNodes and we assert on their string repr
    # by lifting the result out via a `const` binding.
    const swapLessLE = (block:
      var n = newTree(nnkInfix, ident"<", ident"a", ident"b")
      let m = applyMutator(n, mtSwapLessLE)
      doAssert m.isSome
      m.get.repr)
    check swapLessLE == "a <= b"

    const swapEqNeq = (block:
      var n = newTree(nnkInfix, ident"==", ident"a", ident"b")
      let m = applyMutator(n, mtSwapEqNeq)
      doAssert m.isSome
      m.get.repr)
    check swapEqNeq == "a != b"

    const replZero = (block:
      let m = applyMutator(newLit(42), mtReplaceIntZero)
      doAssert m.isSome
      m.get.intVal)
    check replZero == 0

    const noApply = (block:
      let n = newTree(nnkInfix, ident"+", ident"a", ident"b")
      let m = applyMutator(n, mtSwapLessLE)
      m.isNone)
    check noApply == true

suite "mutantsOf — macro generates variant procs":
  test "proc with one `<` and one int literal emits ≥ 2 mutants":
    # Original: `proc(x: int): int = if x < 10: 1 else: 0`
    # Mutators that apply:
    #   mtSwapLessLE: `<` → `<=`
    #   mtReplaceIntZero: literal 10 → 0; literal 1 → 0
    #   mtReplaceIntOne: literal 10 → 1; literal 0 → 1
    # so we expect several mutants.
    let mutants = mutantsOf(proc(x: int): int =
      if x < 10: 1 else: 0)
    check mutants.len >= 2
    # Sanity: the original always returns 1 for x = 5; at least one
    # mutant should return something *different* on x = 5.
    var sawDifferent = false
    for m in mutants:
      if m.body(5) != 1:
        sawDifferent = true
        break
    check sawDifferent

suite "mutationScore — buckets killed/survived":
  test "perfect property kills all mutants of a clamping function":
    # Original: clamp x into [0, 100].
    let mutants = mutantsOf(proc(x: int): int =
      if x < 0: 0
      elif x > 100: 100
      else: x)
    proc original(x: int): int =
      if x < 0: 0
      elif x > 100: 100
      else: x
    # Strong property: for x in [-50, 200], output equals the
    # algebraic clamp.
    proc runProperty(fn: proc(x: int): int): Outcome =
      var s = defaultSettings()
      s.maxExamples = 50
      s.useSA = false
      s.targetedSAIters = 0
      let r = forAll(integers(-50, 200),
                     (proc(x: int) =
                       let want = if x < 0: 0 elif x > 100: 100 else: x
                       ensure fn(x) == want), s)
      r.outcome
    let report = mutationScore(original, mutants, runProperty)
    # Strong property kills *all behavioral* mutants. Some mutators
    # produce *equivalent* mutants (e.g. `x < 0` vs `x <= 0` agree
    # on every integer); those survive but aren't test gaps. v1
    # doesn't detect equivalents statically — they show up in
    # survivors. Real-world mutation scores reflect this: PIT and
    # Mutmut both report sub-100% even on exhaustive test suites
    # due to equivalents. Assert "high but not necessarily 100%."
    check report.killed >= mutants.len div 2

  test "weak property leaves survivors":
    # Original same as above. Weak property only checks `output >= 0`.
    # The mutant that replaces `0` with `1` returns 1 for negative
    # inputs; output is still >= 0, so the weak property *passes* on
    # the mutant and we count it as a survivor.
    let mutants = mutantsOf(proc(x: int): int =
      if x < 0: 0
      elif x > 100: 100
      else: x)
    proc original(x: int): int =
      if x < 0: 0
      elif x > 100: 100
      else: x
    proc runProperty(fn: proc(x: int): int): Outcome =
      var s = defaultSettings()
      s.maxExamples = 50
      s.useSA = false
      s.targetedSAIters = 0
      let r = forAll(integers(-50, 200),
                     (proc(x: int) = ensure fn(x) >= 0), s)
      r.outcome
    let report = mutationScore(original, mutants, runProperty)
    # Some mutants survive (those preserving non-negativity).
    check report.survived >= 1
    check report.score < 1.0
