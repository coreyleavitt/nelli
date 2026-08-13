## Rectify #145 + #143 + #140 — container mutations + var T params.
import std/unittest
import std/tables
import std/sets
import nelli/symex

suite "symex mutations #145":
  test "seq.add appends and increments len":
    proc growAndCheck(s: var seq[int]) =
      s.add(42)
      if s.len == 1 and s[0] == 42:
        symexTarget("post")
    let r = symexFind(growAndCheck, tLabel("post"))
    check r.status == sxSat
    check r.witness[0].len == 0

  test "Table[k] = v sets the value":
    proc setKey(t: var Table[string, int]) =
      t["a"] = 7
      if t["a"] == 7:
        symexTarget("set-ok")
    let r = symexFind(setKey, tLabel("set-ok"))
    check r.status == sxSat

  test "Table.del removes the key":
    proc removeKey(t: var Table[string, int]) =
      t["a"] = 99
      t.del("a")
      if "a" notin t:
        symexTarget("removed")
    let r = symexFind(removeKey, tLabel("removed"))
    check r.status == sxSat

  test "HashSet.incl adds a member":
    proc inclMember(s: var HashSet[int]) =
      s.incl(42)
      if 42 in s:
        symexTarget("included")
    let r = symexFind(inclMember, tLabel("included"))
    check r.status == sxSat

  test "HashSet.excl removes a member":
    proc exclMember(s: var HashSet[int]) =
      s.incl(7)
      s.excl(7)
      if 7 notin s:
        symexTarget("excluded")
    let r = symexFind(exclMember, tLabel("excluded"))
    check r.status == sxSat

  test "var T param mutated in helper propagates to caller (#140)":
    proc helper(s: var seq[int]) =
      s.add(9)
    proc outer(s: var seq[int]) =
      helper(s)
      if s.len == 1 and s[0] == 9:
        symexTarget("helper-mutated")
    let r = symexFind(outer, tLabel("helper-mutated"))
    check r.status == sxSat
    check r.witness[0].len == 0
