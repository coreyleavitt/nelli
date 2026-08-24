## N49 (RFC-chapulin-hardening bucket-2, N7 design round) -- dotted-field
## lvalue mutation crash.
##
## ---- Root cause -----------------------------------------------------------
## `parseStmtInner`'s `nnkCall`/`nnkCommand` handling recognizes seq/string/
## Table/HashSet MUTATIONS (`.add`, `.del`, `.insert`, `.incl`, `.excl`,
## `[]=`) by NAME + receiver kind ("#145 mutations recognised by name +
## receiver kind") -- but the recognizer gated on `recv1.kind == nnkSym`, a
## BARE-SYMBOL receiver only, because the encoding rebinds the receiver's own
## env slot (`mkAssign(recvName, ...)`). A dotted-field lvalue receiver
## (`obj.seqField.add(x)`) has no such slot, so it never matched and fell
## through to the generic `ensureProcRegistered` call-registration path --
## which then tried to treat Nim's own compiler-magic `add`/`del`/etc. as an
## ordinary user proc, classifying its `monomorphize()`-synthesized (and
## therefore typeless) formal-parameter nodes. `classifyType`'s own
## `getTypeInst` call on such a node is a NON-CATCHABLE compile error ("node
## has no type") -- the same A5 hard-crash class this codebase has closed at
## several other sites (`sink`/`lent`, `owned`, `static[N]` arrays,
## `nnkProcTy` formals), reached here through a path none of those guards
## anticipated.
##
## ---- Adjudication ----------------------------------------------------------
## A genuine value-typed field-write REBIND (reconstructing the whole
## enclosing record with one field replaced) is a real new engine capability
## -- out of proportion for this fix. Instead: honest PARSE-TIME classified
## decline, via the new `isKnownMutatingReceiverCall` predicate
## (`dsl_parser.nim`) -- mirrors the PRE-EXISTING sibling decline for direct
## field assignment (`obj.plainField = value`, the `nnkAsgn` arm's own
## "unsupported nnkAsgn shape" catch-all, which already declined gracefully
## for a NON-variant-discriminator field write). Applies uniformly to plain
## objects and variant-ARM fields (`nnkCheckedFieldExpr`-wrapped dot-exprs).
## RED (compile crash) -> GREEN (classified `sxUnknown`, never a crash, never
## a silent wrong verdict) -- walker v121->v122 (see `symexWalkerVersion`'s
## own doc comment, `canonicalize.nim`, for the full writeup).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type
  Kind = enum kA, kB
  Widget = object
    items: seq[int]

  VariantThing = object
    case kind: Kind
    of kA: items2: seq[int]
    of kB: n: int

proc mutatePlainField(w: Widget, x: int) =
  ## Pre-fix: crashed the whole macro expansion (RED, confirmed via
  ## stash-bisection against this slice's own diff -- reverting the
  ## `dsl_parser.nim` change reproduces the compile-time abort exactly).
  var w2 = w
  w2.items.add(x)
  if w2.items.len > 0:
    symexTarget("plain_added")

proc mutateVariantArmField(v: VariantThing, x: int) =
  ## Same crash class through a variant ARM field -- the receiver arrives
  ## as `nnkCheckedFieldExpr(dotExpr, discCheck)`, not a bare `nnkDotExpr`.
  var v2 = v
  if v2.kind == kA:
    v2.items2.add(x)
    if v2.items2.len > 0:
      symexTarget("variant_added")

proc helperOnSeq(xs: seq[int]): bool =
  xs.len > 100

proc nonMutatingDottedCall(w: Widget) =
  ## Regression trip-wire: an ORDINARY (non-mutating) call whose first
  ## argument happens to be a dotted-field expression must NOT be swept
  ## into the new decline branch -- `helperOnSeq` is not one of the
  ## recognized mutation verbs, so this must reach the real
  ## `ensureProcRegistered` path and prove normally, unaffected.
  if helperOnSeq(w.items):
    symexTarget("helper_true")

proc mutateBareLocal(xs: seq[int], x: int) =
  ## Regression trip-wire: the PRE-EXISTING bare-symbol receiver path (the
  ## one this fix must not touch) still gets the real modeled mutation, not
  ## the new decline.
  var ys = xs
  ys.add(x)
  if ys.len > 0:
    symexTarget("bare_added")

suite "N49 -- dotted-field lvalue mutation: honest classified decline":
  test "plain object dotted-field seq .add() declines cleanly (no crash)":
    let r = symexFind(mutatePlainField, tLabel("plain_added"))
    check r.status == sxUnknown

  test "variant-arm object dotted-field seq .add() declines cleanly (no crash)":
    let r = symexFind(mutateVariantArmField, tLabel("variant_added"))
    check r.status == sxUnknown

suite "N49 -- regression: unaffected shapes":
  test "an ordinary non-mutating call with a dotted-field argument is unaffected":
    let r = symexFind(nonMutatingDottedCall, tLabel("helper_true"))
    check r.status == sxSat

  test "the pre-existing bare-symbol receiver mutation is still modeled, not declined":
    let r = symexFind(mutateBareLocal, tLabel("bare_added"))
    check r.status == sxSat

suite "N49 -- walker version pin":
  test "walker version floor >= 122 (N49: dotted-field mutation crash -> classified decline)":
    check parseInt(symexWalkerVersion) >= 122
