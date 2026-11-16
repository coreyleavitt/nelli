## RFC-0016 0.10.0 review D5 -- the magic dispatch, split from `magic_rows`.
##
## `magic_rows` is an axis: a site enum, a table and `admitMagic`. The
## consumers below read two axes at once (`dispatchMagic` checks an unsigned
## operator's arm against `stdlibAxis`, `lowerMagic` takes either axis's
## proof), so they sit above both: an axis module imports no other axis
## module. Importers of the dispatch get `magic_rows` with it.
import std/[options, macros, sequtils]
import ./admission
import ./magic_rows
import ./stdlib_rows
export magic_rows

var dispatchedSites {.compileTime.}: set[MagicSite]
  ## The sites a `dispatchMagic` expansion has covered, in this compilation.

proc dispatchedMagicSites*(): set[MagicSite] {.compileTime.} = dispatchedSites

template lowerMagic*(proof: Admit[MagicModel] | Admit[StdlibBody];
                     body: untyped): untyped =
  ## RFC-0016 ADM-IR (section 8.1). The one place a magic arm's lowering runs:
  ## `dispatchMagic` wraps every `of` arm's body in it, with the proof the
  ## arm's row gives at the site (`admitMagic`, or `admitStdlibBody` for an
  ## unsigned operator). The lowering does not run on a declined proof, so a
  ## magic's node is built only for a magic the table admits; another axis's
  ## proof is a type error. The census in `tests/tsymex_0016_admir.nim`
  ## counts the magic arms outside a dispatch.
  doAssert proof.admitted, "lowerMagic: " & proof.decline[1]
  body

template whenMagic*(magic: string; name: static string; body: untyped) =
  ## ADM-IR. The expression-form twin of a `dispatchMagic` arm: `body` runs
  ## when `magic` is `name`, under that row's proof at `msArm`
  ## (`lowerMagic`), so a node is built only for a magic the table admits.
  if magicIs(magic, name):
    lowerMagic(admitMagic(magic, msArm), body)

template whenMagicIn*(magic: string; names: static seq[string];
                      body: untyped) =
  ## `whenMagic` over a group of magics that share one lowering.
  if magicIn(magic, names):
    lowerMagic(admitMagic(magic, msArm), body)

macro dispatchMagic*(site: static MagicSite; body: untyped): untyped =
  ## RFC-0016 K4a-dispatch (section 8.1). `body` is the site's `case` over a
  ## magic's name. The expansion is that `case`, after the table has been
  ## read at compile time:
  ##   * every `of` string must have a row in `magicAxis` admitted at `site`;
  ##   * every row admitted at `site` must have an `of` arm;
  ##   * the `else` is the decline (the name is refused, absent, or admitted
  ##     elsewhere), and must exist;
  ##   * a site is expanded once: a second expansion is an error, so
  ##     `dispatchedMagicSites()` is a registry of covered sites.
  if site notin magicDispatchSites:
    error("dispatchMagic: " & $site & " is not a dispatched site", body)
  if site in dispatchedSites:
    error("dispatchMagic: " & $site & " is dispatched twice", body)
  let hasStd = site in {msInfix, msCallSwitch}
  let stdlibSite = if site == msInfix: ssInfix else: ssCallSwitch
  var cs = body
  while cs.kind in {nnkStmtList, nnkStmtListExpr} and cs.len == 1: cs = cs[0]
  if cs.kind != nnkCaseStmt:
    error("dispatchMagic: the body is a `case` over the magic's name", body)
  var arms: seq[string]
  var hasElse = false
  for i in 1 ..< cs.len:
    let br = cs[i]
    if br.kind == nnkElse: hasElse = true
    else:
      for j in 0 ..< br.len - 1:
        if br[j].kind notin {nnkStrLit .. nnkTripleStrLit}:
          error("dispatchMagic: an arm names a magic by a string literal", br[j])
        let a = br[j].strVal
        if a in arms:
          error("dispatchMagic: duplicate arm `" & a & "`", br[j])
        arms.add a
        if hasStd and stdlibAxis.hasRow(unsignedOpKey(a)):
          # K4c: a `system` routine (the unsigned operators), not a magic.
          if not stdlibAxis.admit(unsignedOpKey(a), stdlibSite).admitted:
            error("dispatchMagic: arm `" & a & "` has a stdlib row that is " &
                  "not admitted at " & $stdlibSite, br[j])
        elif not magicAxis.hasRow(a):
          error("dispatchMagic: arm `" & a & "` has no row in magicAxis or " &
                "stdlibAxis", br[j])
        elif not magicAxis.admit(a, site).admitted:
          error("dispatchMagic: arm `" & a & "` has a row that is not " &
                "admitted at " & $site, br[j])
  if not hasElse:
    error("dispatchMagic: the case needs an `else`, the decline", body)
  for k in magicAxis.keysAt(site):
    if k notin arms:
      error("dispatchMagic: the row `" & k & "` is admitted at " & $site &
            " and has no arm", body)
  for k in (if hasStd: toSeq(stdlibAxis.keysAt(stdlibSite)) else: @[]):
    if k notin arms.mapIt(unsignedOpKey(it)):
      error("dispatchMagic: the stdlib row `" & k & "` is admitted at " &
            $stdlibSite & " and has no arm", body)
  # ADM-IR: each arm's lowering runs under the proof of its row at the site.
  for i in 1 ..< cs.len:
    let br = cs[i]
    if br.kind == nnkElse: continue
    var arm = br[^1]
    for j in countdown(br.len - 2, 0):
      let nm = br[j].strVal
      let proof =
        if hasStd and stdlibAxis.hasRow(unsignedOpKey(nm)):
          newCall(bindSym"admitStdlibBody", newLit(unsignedOpKey(nm)),
                  newLit(stdlibSite))
        else:
          newCall(bindSym"admitMagic", newLit(nm), newLit(site))
      arm = newCall(bindSym"lowerMagic", proof, arm)
    br[^1] = arm
  dispatchedSites.incl site
  result = cs
