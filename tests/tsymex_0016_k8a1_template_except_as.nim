## RFC-0016 K8A-1 -- `except T as e:` inside a statement template defined
## and expanded in a proc must not crash the macro-time route scan.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutTemplate(a: int) =
  template w() =
    try:
      if a > 3: raise newException(ValueError, "x")
    except ValueError as e:
      symexTarget("hit")
  w()

proc sutTemplatePlain(a: int) =
  template w() =
    try:
      if a > 3: raise newException(ValueError, "x")
    except ValueError:
      symexTarget("hit")
  w()

proc sutNested(a: int) =
  template outer() =
    template inner() =
      try:
        if a > 3: raise newException(ValueError, "x")
      except ValueError as e:
        symexTarget("hit")
    inner()
  outer()

template modW(a: int) =
  try:
    if a > 3: raise newException(ValueError, "x")
  except ValueError as e:
    symexTarget("hit")

proc sutModule(a: int) =
  modW(a)

iterator itSut(a: int): int =
  template w() =
    try:
      if a > 3: raise newException(ValueError, "x")
    except ValueError as e:
      symexTarget("hit")
  w()
  yield a

proc sutIter(a: int) =
  for x in itSut(a): discard

const dom = sampled([-1, 0, 3, 4, 7])

suite "K8A-1 except-as in a template":
  test "plain except in a template agrees":
    let r = pinExact(sutTemplatePlain, cellKey(axConstruct, "k8a1-plain"),
                     target = tLabel("hit"), domain = dom)
    check r.status == sxSat
  test "except as e in a proc-local template":
    let r = pinExact(sutTemplate, cellKey(axConstruct, "k8a1-as"),
                     target = tLabel("hit"), domain = dom)
    check r.status == sxSat
  test "except as e in a nested template":
    let r = pinExact(sutNested, cellKey(axConstruct, "k8a1-nested"),
                     target = tLabel("hit"), domain = dom)
    check r.status == sxSat
  test "except as e in a module-level template":
    let r = pinExact(sutModule, cellKey(axConstruct, "k8a1-module"),
                     target = tLabel("hit"), domain = dom)
    check r.status == sxSat
  test "except as e in a template inside an iterator":
    let r = pinExact(sutIter, cellKey(axConstruct, "k8a1-iter"),
                     target = tLabel("hit"), domain = dom)
    check r.status == sxSat
