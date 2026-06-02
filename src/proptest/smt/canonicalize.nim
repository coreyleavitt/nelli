## Canonical structural encoding for the symex IR.
##
## The output of every `canonicalize` proc here is a deterministic
## string that depends only on the witness-relevant structure of
## its input. Source locations, local-variable name spellings, and
## map-iteration order are all encoded out — the canonical string
## of two structurally-equivalent inputs is byte-identical.
##
## Used by Phase 10's content-addressed DB cache key
## (`symexCacheKey`). See `docs/symex/determinism.md`.
##
## Reserved sigils:
##   `<` `>`  — open/close one constructor's payload
##   `;`      — field separator within a constructor
##   `:`      — kind/payload separator
## No constructor's payload may contain an unescaped sigil; primitives
## are wrapped to enforce that.

import std/[strutils, tables, algorithm, sha1]
import ./types

const symexWalkerVersion* = "1"
  ## Bumped by maintainers whenever the walker's semantics shift in a
  ## witness-affecting way. Participates in `symexCacheKey` so old
  ## persisted witnesses become invisible after a walker semantic
  ## change.

# ---- IRType -----------------------------------------------------------------

proc canonicalize*(t: IRType): string =
  if t.isNil:
    return "Ty<nil>"
  case t.kind
  of itInt:
    "Ty<I:" & $t.width & ":" & (if t.signed: "s" else: "u") & ">"
  of itBool:
    "Ty<B>"
  of itString:
    "Ty<S>"
  of itTuple:
    # Positional encoding: field order is significant; field-name
    # spelling is encoded only when present (named tuples / object
    # field accessors), since renaming an anonymous-tuple field is
    # by definition a no-op but renaming a named field changes
    # `iekField` lookups.
    var parts: seq[string]
    for i in 0 ..< t.fields.len:
      let nm = if i < t.fieldNames.len: t.fieldNames[i] else: ""
      parts.add nm & "=" & canonicalize(t.fields[i])
    "Ty<T:" & t.objectName & ":" & parts.join(";") & ">"
  of itArray:
    "Ty<A:" & $t.size & ":" & canonicalize(t.elemTy) & ">"
  of itSeq:
    "Ty<Sq:" & canonicalize(t.seqElemTy) & ">"
  of itTable:
    "Ty<Tb:" & canonicalize(t.tabKeyTy) & ";" & canonicalize(t.tabValTy) & ">"
  of itSet:
    "Ty<Se:" & canonicalize(t.setElemTy) & ">"

# ---- Local-name rewriting ---------------------------------------------------
#
# Local let/assign names are encoded positionally so renames don't
# invalidate witnesses. `LocalEnv` walks the IR in declaration order
# (depth-first, syntactic) and assigns each `let` the next `$N` slot;
# every later `iekVar` that refers to a local gets rewritten through
# the same map. Free variables (params, top-level callees) are
# encoded by their original name — they're part of the program's
# external surface, not internal.
type LocalEnv = ref object
  slots: Table[string, int]   # original-name → de-Bruijn-style slot id
  next:  int

proc newLocalEnv(): LocalEnv =
  LocalEnv(slots: initTable[string, int](), next: 0)

proc bindLocal(env: LocalEnv, name: string): int =
  result = env.next
  env.slots[name] = result
  inc env.next

proc lookupLocal(env: LocalEnv, name: string): string =
  if name in env.slots:
    "$" & $env.slots[name]
  else:
    name  # free — encode by original name

# ---- IRExpr -----------------------------------------------------------------

proc binopTag(op: IRBinop): string =
  case op
  of bAdd: "+"
  of bSub: "-"
  of bMul: "*"
  of bDiv: "/"
  of bMod: "%"
  of bAnd: "&"
  of bOr:  "|"
  of bXor: "^"
  of bShl: "<<"
  of bShr: ">>"
  of bEq:  "=="
  of bNe:  "!="
  of bLt:  "<"
  of bLe:  "<="
  of bGt:  ">"
  of bGe:  ">="

proc unopTag(op: IRUnop): string =
  case op
  of uNot: "!"
  of uNeg: "~"

proc canonicalize(e: IRExpr, env: LocalEnv): string =
  if e.isNil: return "Ex<nil>"
  case e.kind
  of iekIntLit:    "Ex<IL:" & $e.ival & ">"
  of iekBoolLit:   "Ex<BL:" & $e.bval & ">"
  of iekVar:       "Ex<V:" & lookupLocal(env, e.vname) & ">"
  of iekBinop:
    "Ex<Bn:" & binopTag(e.bop) & ";" &
      canonicalize(e.lhs, env) & ";" & canonicalize(e.rhs, env) & ">"
  of iekUnop:
    "Ex<Un:" & unopTag(e.uop) & ";" & canonicalize(e.operand, env) & ">"
  of iekField:
    "Ex<F:" & $e.fieldIx & ";" & canonicalize(e.obj, env) & ">"
  of iekIndex:
    "Ex<Ix:" & canonicalize(e.arr, env) & ";" &
      canonicalize(e.idx, env) & ">"
  of iekArrayLit:
    var parts: seq[string]
    for x in e.lelems: parts.add canonicalize(x, env)
    "Ex<AL:" & canonicalize(e.lelemTy) & ";[" & parts.join(",") & "]>"
  of iekSeqLen:    "Ex<SL:" & canonicalize(e.lenObj, env) & ">"
  of iekStrLit:    "Ex<S:" & e.sval.escape & ">"
  of iekContains:
    "Ex<C:" & canonicalize(e.container, env) & ";" &
      canonicalize(e.key, env) & ">"
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    "Ex<" & $e.kind & ":" & canonicalize(e.mutRecv, env) & ";" &
      canonicalize(e.mutArg, env) & ">"
  of iekSeqDel:
    "Ex<SqD:" & canonicalize(e.delSeq, env) & ";" &
      canonicalize(e.delIdx, env) & ">"
  of iekSeqInsert:
    "Ex<SqI:" & canonicalize(e.insSeq, env) & ";" &
      canonicalize(e.insVal, env) & ";" &
      canonicalize(e.insIdx, env) & ">"
  of iekSeqPop:    "Ex<SqP:" & canonicalize(e.popSeq, env) & ">"
  of iekTableSet:
    "Ex<TS:" & canonicalize(e.tabRecv, env) & ";" &
      canonicalize(e.tabKey, env) & ";" &
      canonicalize(e.tabVal, env) & ">"

# ---- IRStmt -----------------------------------------------------------------

proc canonicalize(s: IRStmt, env: LocalEnv): string =
  if s.isNil: return "St<nil>"
  case s.kind
  of isBlock:
    var parts: seq[string]
    for x in s.stmts: parts.add canonicalize(x, env)
    "St<Bk:[" & parts.join(",") & "]>"
  of isIf:
    var parts: seq[string]
    for br in s.branches:
      parts.add "(" & canonicalize(br.cond, env) & "=>" &
        canonicalize(br.body, env) & ")"
    "St<If:[" & parts.join(",") & "];else=" &
      canonicalize(s.elseBody, env) & ">"
  of isLet:
    let slot = bindLocal(env, s.lname)
    "St<Lt:$" & $slot & ":" & canonicalize(s.lty) & "=" &
      canonicalize(s.lvalue, env) & ">"
  of isAssign:
    "St<As:" & lookupLocal(env, s.aname) & "=" &
      canonicalize(s.avalue, env) & ">"
  of isWhile:
    "St<W:" & canonicalize(s.wcond, env) & ";body=" &
      canonicalize(s.wbody, env) & ">"
  of isBreak:    "St<Bk>"
  of isContinue: "St<Co>"
  of isReturn:
    "St<R:" & canonicalize(s.retExpr, env) & ">"
  of isCall:
    var args: seq[string]
    for a in s.cargs: args.add canonicalize(a, env)
    let retSlot =
      if s.retName.len > 0: "$" & $bindLocal(env, s.retName)
      else: ""
    "St<Cl:" & s.callee & ";opaque=" & $s.opaque & ";ret=" & retSlot &
      ";retTy=" & canonicalize(s.retTy) & ";args=[" & args.join(",") & "]>"
  of isIndex:
    let retSlot = "$" & $bindLocal(env, s.ixRetName)
    "St<Ix:" & retSlot & "=" & canonicalize(s.ixArr, env) &
      "[" & canonicalize(s.ixIdx, env) & "];ety=" &
      canonicalize(s.ixElemTy) & ">"
  of isAssert:
    "St<At:" & canonicalize(s.acond, env) & ">"
  of isTargetLabel:
    "St<Tg:" & s.tname.escape & ">"
  of isUnsupported:
    "St<Un:" & s.reason.escape & ">"

# ---- Top-level overloads ---------------------------------------------------

proc canonicalize*(e: IRExpr): string =
  canonicalize(e, newLocalEnv())

proc canonicalize*(s: IRStmt): string =
  canonicalize(s, newLocalEnv())

# ---- IRParam ---------------------------------------------------------------

proc canonicalize*(p: IRParam): string =
  # Params live at the program's external boundary — their *position*
  # is the witness's identity (witness[0], witness[1], …), and their
  # *type* matters for encoding. The name is part of the program's
  # source-level surface; renaming a param doesn't affect the
  # witness's structural validity, so it's excluded from the canonical
  # form. `isVar` matters because it affects mutation propagation.
  # Range hints (rangeLo/rangeHi from Natural / range[...]) DO matter
  # because they're consumed by the abstraction layer.
  var range = ""
  if p.hasRange:
    range = ";range=[" & $p.rangeLo & "," & $p.rangeHi & "]"
  "Pm<" & canonicalize(p.ty) & ";isVar=" & $p.isVar & range & ">"

# ---- ProcSig ---------------------------------------------------------------

proc canonicalize*(sig: ProcSig): string =
  var params: seq[string]
  let env = newLocalEnv()
  for p in sig.params:
    discard bindLocal(env, p.name)  # so body's iekVar refs to params
                                    # resolve as locals positionally
    params.add canonicalize(p)
  "Pr<" & sig.name & ";retTy=" & canonicalize(sig.retTy) &
    ";isVoid=" & $sig.isVoid &
    ";params=[" & params.join(",") & "]" &
    ";body=" & canonicalize(sig.body, env) & ">"

# ---- SymexProgram ----------------------------------------------------------

proc canonicalize*(prog: SymexProgram): string =
  # Top-level body sees params as bound locals (positionally).
  let env = newLocalEnv()
  var paramParts: seq[string]
  for p in prog.params:
    discard bindLocal(env, p.name)
    paramParts.add canonicalize(p)
  # Callees sorted by name — `Table` iteration order isn't stable.
  var keys: seq[string]
  for k in prog.procs.keys: keys.add k
  sort(keys)
  var procParts: seq[string]
  for k in keys:
    procParts.add canonicalize(prog.procs[k])
  "Pg<params=[" & paramParts.join(",") & "];body=" &
    canonicalize(prog.body, env) &
    ";procs=[" & procParts.join(",") & "]>"

# ---- SymexTarget -----------------------------------------------------------

proc canonicalize*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "Tg<L:" & t.label.escape & ">"
  of stkAssertionViolation: "Tg<AV>"
  of stkIndexError:         "Tg<IE>"

# ---- SymexSettings ---------------------------------------------------------

proc canonicalize*(s: SymexSettings): string =
  # Witness-relevant subset ONLY. `acceptUnknownAsCovered` is
  # provably excluded because it influences the verifier's
  # raise/pass decision (`assertCoveredBy`) and not the walker's
  # output.
  "St<is=" & $s.integerSemantics &
    ";to=" & $s.queryTimeoutMs &
    ";fr=" & $s.maxFrontierSize &
    ";cd=" & $s.maxCallDepth &
    ";lu=" & $s.maxLoopUnwind & ">"

# ---- Cache key -------------------------------------------------------------

proc symexCacheKey*(prog: SymexProgram, target: SymexTarget,
                    settings: SymexSettings,
                    z3Version, nimVersion, walkerVersion: string): string =
  ## Content-addressed key over every input that determines a
  ## witness's validity. Stable across builds (no source locations,
  ## no map-iteration order, no compiler-specific hashes). Returns
  ## `"sx:" & <40-char SHA-1 hex>`.
  let canon =
    "K|" & canonicalize(prog) &
    "|" & canonicalize(target) &
    "|" & canonicalize(settings) &
    "|z3=" & z3Version &
    "|nim=" & nimVersion &
    "|w=" & walkerVersion
  "sx:" & $secureHash(canon)
