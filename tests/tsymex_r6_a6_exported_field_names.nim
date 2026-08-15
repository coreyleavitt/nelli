## Round-6 A6 (discovered while un-voiding chapulin's t_symex_decode.nim) --
## a genuinely EXPORTED case-object's discriminator/arm field names crashed
## macro expansion.
##
## chapulin's `TftpPacket*`'s `case opcode*: TftpOpcode` and every arm field
## (`filename*`, `blockNum*`, ...) are export-marked -- the FIRST real,
## exported case-object `symexFind` has ever been pointed at (every prior
## synthetic SUT across A0-A5's own test files used unexported local types,
## so this shape went unexercised). `classifyObjectRecordFields`'s variant
## path (`dsl_typebridge.nim`) read each field name via a bare `.strVal` on
## the raw `getImpl` syntax node -- for an exported field that node is
## `nnkPostfix("*", name)`, not a bare `nnkSym`/`nnkIdent`, so `.strVal`
## crashed macro expansion ("node lacks field: strVal"), aborting the whole
## file. The IDENTICAL crash (and fix) already existed for the PLAIN-record
## path (v64 Sec.0 clause (b), chapulin round-3) -- this pass extracts that
## fix into a shared `fieldNameStr`/`unwrapFieldNameNode` helper and applies
## it to the three analogous variant-path sites (plain fields declared
## before a `case`, the discriminator itself, and each arm's own fields).
##
## Ver: -- (no symexWalkerVersion bump -- a macro-expansion-time NimNode
## crash fix, not a verdict-surface change on any existing pin; mirrors A5's
## "crash -> correct verdict, no bump" precedent).
import std/[unittest, strutils]
import nelli/symex

type
  EKind* = enum ekCircle, ekSquare
  EShape* = object
    tag*: int                       ## exported plain field
    case kind*: EKind                ## exported discriminator
    of ekCircle: radius*: int        ## exported arm field
    of ekSquare: side*: int          ## exported arm field

proc sutExportedCircleHit(r: int) =
  let s = EShape(kind: ekCircle, radius: r, tag: 42)
  if s.radius == 7 and s.tag == 42:
    symexTarget("exported_circle_radius_7")

proc sutExportedSquareHit(sd: int) =
  let s = EShape(kind: ekSquare, side: sd)
  if s.side == 11:
    symexTarget("exported_square_side_11")

suite "symex round-6 A6 -- exported case-object field names classify and construct":

  test "A6-fix-1: exported discriminator + exported arm field + exported plain field all classify -- sxSat, witness r==7":
    let res = symexFind(sutExportedCircleHit, tLabel("exported_circle_radius_7"))
    check res.status == sxSat
    check res.witness[0] == 7

  test "A6-fix-2: the OTHER exported arm also constructs and proves":
    let res = symexFind(sutExportedSquareHit, tLabel("exported_square_side_11"))
    check res.status == sxSat
    check res.witness[0] == 11

  test "A6-fix-3: no IndexError/FieldDefect path (sxUnsat)":
    check symexFind(sutExportedCircleHit, tIndexError()).status == sxUnsat
    check symexFind(sutExportedCircleHit, tFieldDefect()).status == sxUnsat
