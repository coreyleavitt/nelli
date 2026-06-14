import std/unittest
import std/macros
import proptest/symex

# Phase 15 — Cluster L (templates/macros), cycle L1: boundary audit.
# Hypothesis (RFC §Cluster-L): Nim's semchecker expands all templates/macros
# before the typed AST reaches symex, so `fn.getImpl` always yields a plain,
# fully-expanded `nnkProcDef`. We verify the trust boundary BEHAVIORALLY — the
# strongest end-to-end proof, and independent of the internal `parseProc` —
# by symexing SUTs defined three ways. If any turns RED, the boundary broke.
# See docs/symex/templates-macros.md.

# (a) template-defined SUT
template defViaTemplate(sutName: untyped) =
  proc sutName(x: int) =
    if x == 42: symexTarget("thit")
defViaTemplate(templateSut)

# (b) macro-emitted SUT (quote do)
macro emitSut(sutName: untyped): untyped =
  quote do:
    proc `sutName`(x: int) =
      if x == 7: symexTarget("mhit")
emitSut(macroSut)

# (c) {.dirty.} template-defined SUT (no gensym; injects into caller scope)
template defViaDirty() {.dirty.} =
  proc dirtySut(x: int) =
    if x == 9: symexTarget("dhit")
defViaDirty()

suite "symex Phase 15 — L1 template/macro boundary audit":

  test "template-defined SUT reaches parser as expanded proc and symexes":
    let r = symexFind(templateSut, tLabel("thit"))
    check r.status == sxSat

  test "macro-emitted SUT reaches parser as expanded proc and symexes":
    let r = symexFind(macroSut, tLabel("mhit"))
    check r.status == sxSat

  test "{.dirty.} template-defined SUT also symexes soundly":
    let r = symexFind(dirtySut, tLabel("dhit"))
    check r.status == sxSat
