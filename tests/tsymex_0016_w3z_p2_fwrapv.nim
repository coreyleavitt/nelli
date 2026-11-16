## RFC-0016 W3-z P2 (Part 0, pins P1's fwrapv guard). A `-d:nelliFwrapv
## --overflowChecks:off` build (its `.nim.cfg`). The opaque-call scan answers
## `ubSignedOverflow` for an overflow-capable magic in an opaque callee whose
## owner has overflow checks off, unless the build wraps: under `-fwrapv` the
## signed `+` is a defined wrap and the sat carries no such kind. The opposite
## case (no `-fwrapv`, checks off) is `tsymex_0016_w3z_p1_off`. Under vcc the
## build is refused by design and cannot import `nelli/symex`, so this arm
## asserts the refusal through `admitBuild`, as `tsymex_0016_k5a_fwrapv` and
## `tsymex_0016_k5b_cfg_fwrapv` do; the msvc row's `build:fwrapv` cell is
## allowlisted (`tests/0016-allowlist/build.txt`, `rows=msvc`).
import nelli/smt/buildprofile
when defined(vcc):
  # Neither `nelli/symex` nor `s8cu_helpers` (which imports it) compiles here:
  # the build is refused at compile time.
  import std/[unittest, strutils, options]
  suite "W3-z P2: opaque scan, -fwrapv build (vcc)":
    test "symex refuses the build by name":
      check buildSemantics.fwrapv
      let refusal = admitBuild(buildSemantics, buildProvenance)
      check refusal.isSome
      if refusal.isSome:
        check refusal.get.field == bfFwrapv
        check "-fwrapv" in refusal.get.reason
else:
  import std/[unittest, strutils, tables, macros]
  import nelli
  import nelli/symex
  import nelli/smt/errorkind
  import nelli/smt/definedness
  import ./s8cu_helpers
  import nelli/smt/types
  import nelli/smt/dsl_parser

  proc oAdd(a: int64) {.symexOpaque.} =
    discard a + 1

  proc sutOpaqueTail(x: int64) =
    if x == 5: symexTarget("hit")
    oAdd(x)

  suite "W3-z P2: opaque scan, -fwrapv build":
    test "version floor":
      check parseInt(symexWalkerVersion) >= 313

    test "the build wraps":
      check buildSemantics.fwrapv

    test "an opaque signed add under -fwrapv is a defined wrap: no ubSignedOverflow":
      let r = symexFind(sutOpaqueTail, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds

  # RFC-0016 0.10.0 review F1 (CR-7): `-fwrapv` defines the signed wrap of
  # `+ - *` and nothing else, so a signed zero divisor stays undefined (rows
  # `div/zeroDivisorSigned` and `mod/zeroDivisorSigned` under `dpFwrapv`). The
  # scan had copied the add guard onto the zero divisor and left
  # `ubSignedDivZero` out of `witnessUndefined`; it now asks the table.
  proc oDiv(a, b: int64) {.symexOpaque.} =
    discard a div b

  proc oMod(a, b: int64) {.symexOpaque.} =
    discard a mod b

  proc oAdd2(a, b: int64) {.symexOpaque.} =
    discard a + b

  proc sutDiv(x, y: int64) =
    if x == 5: symexTarget("hit")
    oDiv(x, y)

  proc sutMod(x, y: int64) =
    if x == 5: symexTarget("hit")
    oMod(x, y)

  proc sutAdd(x, y: int64) =
    if x == 5: symexTarget("hit")
    oAdd2(x, y)

  suite "CR-7: opaque signed division, -fwrapv build":
    test "version floor":
      check parseInt(symexWalkerVersion) >= 359

    test "the build wraps and has overflow checks off":
      check buildSemantics.fwrapv
      check definedness(aoDiv, ocZeroDivisorSigned, dpFwrapv).kind == dkUndefined

    test "an opaque signed div under -fwrapv may divide by zero: never a trusted sat":
      let r = symexFind(sutDiv, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check not r.trusted
      check UbKind(ubSignedDivZero) in r.soundness.undefinedKinds

    test "an opaque signed mod under -fwrapv may divide by zero: never a trusted sat":
      let r = symexFind(sutMod, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check not r.trusted
      check UbKind(ubSignedDivZero) in r.soundness.undefinedKinds

    test "control: an opaque signed add under -fwrapv is a defined wrap":
      let r = symexFind(sutAdd, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds
      check UbKind(ubSignedDivZero) notin r.soundness.undefinedKinds

  # RFC-0016 review D1 (slice S1): `arith_regime` against the current parser
  # and walker rules under this build (checks off, -fwrapv). Folded here so
  # the vcc arm above stays this build's one platform site (K2a census).
  import nelli/smt/arith_regime
  import ./d1_regime_helpers

  suite "D1 S1: arith_regime (checks off, fwrapv)":
    test "the truth table: readable x overflowOn x deviates x row x inherit, all four builds":
      checkTruthTable()
    test "literal rows, each citing the line it encodes":
      checkLiterals()
    test "profile, wrapDefined, ownerProfile against defProfile and signedWrapDefined":
      checkProfiles()
    test "frames: the walk rule, the parse rule, emits, the iterator test":
      checkFrames()
    test "stampFor is const-pure":
      checkConstPure()
    test "the cache-key bytes of a stamped block":
      checkKeyBytes()
    test "D1-F2 + F-3: every routine body stamps its own regime; checking and wrapping are one regime":
      checkTotalStamp()
    test "the compiled build":
      check buildSemantics.fwrapv
      check coOverflow notin buildSemantics.checks
      check buildRegime() == rgUnchecked
      check programMayWrap()
      check profile(rgUnchecked) == dpFwrapv
      check profile(rgChecked) == dpChecked

  # RFC-0016 review R2-1: a lambda's alias bodies (`lambdaAliasBodies`, walked
  # when one call passes one location to two `var` formals) are the lambda's
  # own, stamped with its regime. Here the lambda is compiled pushed
  # `overflowChecks: on` (it raises) and called from a routine of the build's
  # wrapping regime: the aliased call took the caller's, wrapped, and reached
  # the label the native run never does.
  {.push overflowChecks: on.}
  proc mkAdder(): proc (a, b: var int) =
    result = proc (a, b: var int) = a = a + b
  {.pop.}

  proc sutAdderPlain(k: int) =
    var x = k
    var y = k
    let f = mkAdder()
    f(x, y)
    if k > 0 and x < 0: symexTarget("hit")

  proc sutAdderAliased(k: int) =
    var x = k
    let f = mkAdder()
    f(x, x)
    if k > 0 and x < 0: symexTarget("hit")

  suite "R2-1: lambda alias bodies take the lambda's regime (-fwrapv build)":
    test "native: the pushed-on lambda raises on both calls":
      check native(sutAdderPlain(high(int))) == "OverflowDefect"
      check native(sutAdderAliased(high(int))) == "OverflowDefect"
    test "the plain call does not reach the label":
      let r = symexFind(sutAdderPlain, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxRaised
      check not r.errors.named(feUnsupportedOp)
    test "walker version floor (R2-1: alias bodies are stamped)":
      check parseInt(symexWalkerVersion) >= 363
    test "the aliased call answers as the plain call does":
      let p = symexFind(sutAdderPlain, tLabel("hit"))
      let r = symexFind(sutAdderAliased, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxRaised
      check r.status == p.status
      check not r.errors.named(feUnsupportedOp)

  # RFC-0016 round-3 R3-2: the same alias bodies, on the other halves of
  # `parseRoutineBody`. (a) a lambda compiled with `boundChecks` pushed off,
  # in a build that checks them: the check-option decline
  # (`withCheckDeclines`) must reach the aliased body as it reaches the plain
  # one. (b) a lambda body with a proc-typed `let`: alias bodies go through
  # `devirtProcLets`, so the aliased verdict is the plain one.
  # The maker is pushed with its lambda: a push inside a routine body is a
  # statement the walker does not model, and a module-level proc `let` is not
  # a modelled global. So the maker declines at entry as well; the alias body's
  # own decline follows from `parseRoutineBody` (an alias body parsed without
  # it carries no marker); this case pins the equal verdict and kind.
  {.push boundChecks: off.}
  proc mkIndexer(): proc (a, b: var int) =
    result = proc (a, b: var int) =
      let tab = [10, 20, 30, 40]
      a = tab[b and 3]
  {.pop.}

  proc sutIdxPlain(k: int) =
    var x = k
    var y = k
    let f = mkIndexer()
    f(x, y)
    if k == 1 and x == 20: symexTarget("hit")

  proc sutIdxAliased(k: int) =
    var x = k
    let f = mkIndexer()
    f(x, x)
    if k == 1 and x == 20: symexTarget("hit")

  # A `let` proc value called with a Table, the form `devirtProcLets` spells as
  # the direct call. Pins that the aliased verdict is the plain one and exact;
  # with the rewrite bypassed for alias bodies the walker still models this
  # call, so the case guards the verdict, not the rewrite itself.
  proc lookOne(t: Table[int, int]; i: int): int = t[i]

  proc mkLetter(): proc (a, b: var int) =
    result = proc (a, b: var int) =
      var t = initTable[int, int]()
      t[1] = 10
      let g = lookOne
      a = g(t, 1) + b

  proc sutLetPlain(k: int) =
    var x = k
    var y = k
    let f = mkLetter()
    f(x, y)
    if x == 13: symexTarget("hit")

  proc sutLetAliased(k: int) =
    var x = k
    let f = mkLetter()
    f(x, x)
    if x == 13: symexTarget("hit")

  suite "R3-2: alias bodies take the check-option declines and the proc-let rewrite":
    test "walker version floor":
      check parseInt(symexWalkerVersion) >= 363
    test "a lambda pushed boundChecks off declines on the plain call":
      let r = symexFind(sutIdxPlain, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check r.errors.named(feCheckOption)
    test "the aliased call declines exactly as the plain call does":
      let p = symexFind(sutIdxPlain, tLabel("hit"))
      let r = symexFind(sutIdxAliased, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check r.status == p.status
      check r.errors.named(feCheckOption)
      check not r.errors.named(feUnsupportedOp)
    test "a proc-typed let in the body: the plain call finds the label":
      let r = symexFind(sutLetPlain, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
      check not r.errors.named(feUnsupportedOp)
    test "a proc-typed let in the body: the aliased call answers as the plain":
      let p = symexFind(sutLetPlain, tLabel("hit"))
      let r = symexFind(sutLetAliased, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
      check r.status == p.status
      check not r.errors.named(feUnsupportedOp)

  # R3-2, structural half. The verdict cases above cannot tell an alias body
  # parsed through `parseRoutineBody` from one parsed bare (the maker declines
  # on entry; the walker models the proc-let call either way), so the parsed
  # lambda is read directly: every alias body's root is a claiming stamped
  # routine block, as the main body's is, and carries the check-option decline
  # marker whenever the main body does (`checkTotalStamp`'s claim, applied to
  # `lambdaAliasBodies`).
  macro lambdaShape(maker: typed): untyped =
    ## "main=<claims>,<declines>;alias=<claims>,<declines>;..." for the lambda
    ## `maker` builds.
    let parsed = parseProc(maker.getImpl)
    var lam: IRExpr
    proc visit(s: IRStmt) =
      if s == nil: return
      case s.kind
      of isBlock:
        for c in s.stmts: visit(c)
      of isLet:
        if lam == nil and s.lvalue != nil and s.lvalue.kind == iekLambda:
          lam = s.lvalue
      of isAssign:
        if lam == nil and s.avalue != nil and s.avalue.kind == iekLambda:
          lam = s.avalue
      else: discard
    visit(parsed.body)
    if lam == nil: error("no lambda found in " & maker.repr)
    proc shape(b: IRStmt): string =
      if b == nil or b.kind != isBlock: return "notblock"
      var declines = false
      for c in b.stmts:
        if c != nil and c.kind == isUnsupported and c.unKind == feCheckOption:
          declines = true
      $b.blkArith.claims & "," & $declines
    var r = "main=" & shape(lam.lambdaBody)
    for b in lam.lambdaAliasBodies: r.add ";alias=" & shape(b)
    newLit(r)

  proc checkAliasShape(shape: string) =
    let parts = shape.split(';')
    check parts.len >= 2                      # the lambda has an alias body
    let main = parts[0]["main=".len .. ^1]
    check main.startsWith("true,")            # the main body is a claiming block
    for a in parts[1 .. ^1]:
      let v = a["alias=".len .. ^1]
      check v.startsWith("true,")             # so is every alias body
      check v == main                         # and it declines iff the main does

  suite "R3-2: every alias body is a stamped routine block like the main body":
    test "the pushed-on adder":
      let sh = lambdaShape(mkAdder)
      checkpoint sh
      checkAliasShape(sh)
    test "the boundChecks-off indexer carries the decline in main and alias":
      let sh = lambdaShape(mkIndexer)
      checkpoint sh
      checkAliasShape(sh)
      check sh.endsWith("true,true")
      check sh.contains("main=true,true")
