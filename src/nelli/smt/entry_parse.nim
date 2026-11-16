## nelli/smt/entry_parse -- what every symex entry macro does first: warn on
## an incoherent `SymexSettings`, parse the entry routine, register the
## methods it calls and re-expand (`entryParse`), and spell a static
## `SymexTarget` as an expression (`targetLit`).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The `parseEntryImpl`
## call site lives in `parseEntryImplWarned` here (`tentrypointwiring`).

import std/[macros, sets, tables, algorithm, options, strutils, importutils]
import ../choice
import ../db
import ./dsl
import ./scan
import ./scan_kinds
import ./impl_digest
import ./replayproc
import ./replaywire
import ./replayresult
from ./scoped_names import isModuleGlobal, isRoutineGlobal, globalIRName
import ../engine/types as engineTypes
from ../engine/frame import recordSymexFinding, FindingOrigin
import ./sha256
import ./canonicalize
import ./witness_render
import ./witness_emit
import ./replay_emit
import ./replay_settle
import ./run_replayed
import ./symex_cache


# ---- The driver macro -------------------------------------------------------

proc warnIncoherentSettings*(settings: SymexSettings, entry: string) =
  ## RFC-0010 C3a. `validateSymexSettings` is exported and unit-tested and was
  ## called by nothing in `src/` -- a validator that never runs on a real
  ## configuration, which is this RFC's own pattern sitting inside the RFC that
  ## exists to end it. §5 required a decision: wire it in or delete it.
  ##
  ## Wire it in. (Its warning for an empty `arithChecks` -- the defect round B
  ## found in the ten const literals -- went with that setting in RFC-0016
  ## K10d: the build alone decides which checks run.) The mechanism that could
  ## have caught that defect was already written; it was simply never called.
  ##
  ## RFC-0010 review round 2: this proc is no longer called directly from
  ## any entry macro. Every macro that reaches the walker under a
  ## caller-chosen `settings` calls `parseEntryImplWarned` below instead
  ## of `dsl_parser.parseEntryImpl` directly, and that wrapper is the one
  ## call site left that invokes this. That makes coverage true BY
  ## CONSTRUCTION rather than by each macro author remembering to add the
  ## call: a future entry macro gets the check for free by reusing the
  ## helper it already needs for parsing, not by a separate step that can
  ## be forgotten the way the original four call sites were.
  ##
  ## Known duplicate (RFC-0010 review round 2, finding R2-06): an
  ## incoherent `settings` passed to `assertCoveredBy` reaches THIS `for`
  ## loop twice for one user call -- once with `entry == "assertCoveredBy"`
  ## from its own `parseEntryImplWarned` call, once with
  ## `entry == "symexFind"` from the `symexFind` macro that
  ## `assertCoveredBy`'s expansion calls internally. See the long comment
  ## on `assertCoveredBy` (below) for why this is intentional and why a
  ## `{.compileTime.}` dedup here was tried and rejected as unsafe.
  for w in validateSymexSettings(settings):
    warning(entry & ": " & w)

proc parseEntryImplWarned*(fn: NimNode, apiName: string,
                          settings: SymexSettings): ParseResult =
  ## The chokepoint referenced above. Parses `fn` exactly like
  ## `dsl_parser.parseEntryImpl` (it delegates to that proc for the parse
  ## itself) and, before doing so, unconditionally emits a `warning()` via
  ## `warnIncoherentSettings` when `settings` looks incoherent. That is ALL
  ## it does: nothing here rejects, fixes up, or substitutes a corrected
  ## `settings` -- a caller who ignores the compiler warning gets back
  ## exactly the same `ParseResult` as one who heeds it. Despite the RFC's
  ## review-round comments (kept verbatim below) using the word "validates",
  ## this is not validation in the gating sense; it is parse-plus-warn. The
  ## name was corrected from `parseEntryImplValidated` to
  ## `parseEntryImplWarned` in a later review round (finding R2-08) for
  ## exactly this reason.
  ##
  ## `dsl_parser.parseEntryImpl` (owned by RFC-parser-normalization N1,
  ## outside this file) takes only the derived `maxInst: int`, not
  ## `settings` itself -- its signature has no `static` settings value to
  ## inspect, so the warning cannot live inside it without changing that
  ## signature. This wrapper is the closest genuine chokepoint reachable
  ## from `symex.nim` alone: every macro that runs the WALKER under a
  ## caller-chosen `settings` (`symexFind`, `concolicCollect`,
  ## `concolicFlip`, `assertCoveredBy`, `symexFindAllWitnesses` — and,
  ## transitively, `symexForAll`, which itself emits a call to
  ## `symexFindAllWitnesses`) calls THIS instead of `parseEntryImpl`
  ## directly, so parsing and warning can never drift apart again for
  ## that set. The five cache/DB helper macros
  ## (`symexCacheKeyForFn`/`saveSymexWitness`/`loadSymexWitnesses`/
  ## `saveSymexVerdict`/`loadSymexVerdict`) parse through the same
  ## `entryParse` with `warn = false`: they don't run the walker
  ## themselves, they key or persist results computed elsewhere, so a
  ## warning at a cache lookup would be noise pointing at the wrong call
  ## site. (Review R1-11: they once called `parseEntryImpl`
  ## directly and so skipped `methodPrelude` too.)
  ##
  ## `settings` is `static SymexSettings` at every call site (an entry
  ## macro's own `static` parameter), so this whole call resolves at macro
  ## time: zero runtime cost, and `warnIncoherentSettings`'s `warning()`
  ## lands on the user's call site, not inside the library.
  warnIncoherentSettings(settings, apiName)
  parseEntryImpl(fn, apiName, settings.budget.maxInstantiationsPerProc)


proc targetLit*(t: SymexTarget): NimNode =
  ## RFC-0005 S8bn. A static `SymexTarget` as an expression, for an entry
  ## macro's re-expansion (`methodPrelude`).
  case t.kind
  of stkLabel: newCall(bindSym"tLabel", newLit(t.label))
  of stkRaisedExn: newCall(bindSym"tRaisedExn", newLit(t.typeFilter))
  of stkUndefined: newCall(bindSym"tUndefined", newLit(t.ubKinds))
  else: nnkObjConstr.newTree(bindSym"SymexTarget",
                             newColonExpr(ident"kind", newLit(t.kind)))

type EntryParse* = object
  ## RFC-0005 review R1-11. What an entry macro starts from (`entryParse`).
  again*: NimNode      ## non-nil: return this (the methods' registration, then
                      ## the macro again)
  parsed*: ParseResult
  prog*: NimNode       ## the `SymexProgram` constructor, keyed and walked

proc entryParse*(fn: NimNode; apiName: string; settings: SymexSettings;
                again: NimNode; warn = true): EntryParse =
  ## RFC-0005 review R1-11. Every entry macro's parse of `fn`, the cache and DB
  ## helpers' among them, so what they key cannot drift from what the walking
  ## entries write. First the methods `fn` calls are registered in the
  ## caller's scope (`methodPrelude`): `again` is the macro's own call, which
  ## then expands once more, after them. Before this the five cache/DB macros
  ## parsed without it, and keyed the undispatched program wherever no other
  ## entry had registered the methods yet.
  ##
  ## `warn`: the walking entries warn on an incoherent `settings`
  ## (`parseEntryImplWarned`); the cache/DB macros run no walk and do not.
  ## `prog` carries the source digest of the routines `fn` calls
  ## (`implDigest`, R1-09).
  let pre = methodPrelude(fn)
  if pre != nil:
    result.again = newTree(nnkStmtListExpr, pre, again)
    return
  result.parsed =
    if warn: parseEntryImplWarned(fn, apiName, settings)
    else: parseEntryImpl(fn, apiName, settings.budget.maxInstantiationsPerProc)
  var p = result.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)
  let paramsExpr = p.paramsNimNode
  let bodyExpr = p.bodyNimNode
  let procsExpr = p.procsNimNode
  let glExpr = p.globalsNimNode
  let rtExpr = p.retTyNimNode
  let uxhExpr = p.userExnHierarchyNimNode
  let peExpr = p.parseErrorsNimNode
  let avExpr = p.annotationViolationsNimNode
  let digest = newLit(implDigest(fn))
  result.prog = quote do:
    SymexProgram(params: `paramsExpr`, body: `bodyExpr`, procs: `procsExpr`,
                 globals: `glExpr`, retTy: `rtExpr`,
                 userExnHierarchy: `uxhExpr`, parseErrors: `peExpr`,
                 annotationViolations: `avExpr`, implDigest: `digest`)
