## RFC-0005 review R4, R5. The walker's exit channels: where a path waits
## after it left the statement that produced it -- through a `return`, a
## `break` or `continue`, a caught or escaping raise, or a `finally` it must
## run first -- until the scope it is bound for claims it.
##
## The channels are grouped by the scope that owns them (a call's returns, a
## loop's breaks and continues, a call frame's raise and `finally`
## channels); a group is an object whose every field is an `ExitChannel` or
## a nested group. All the channels of one walk are bound to its one
## `ExitClock`, which serializes them. Two scopes read a channel by when its
## entries were parked:
##   * a statement stamps its stray lowering taint on the entries parked
##     after it began (`mark` at its start, `mitemsSince` at its end);
##   * a `try` claims, at its handler depth, only the entries parked while
##     it ran (`claimAt`): an older entry at the same depth belongs to a
##     try whose `except` arm holds this one.
##
## Both are only as sound as the serials. The storage is private, so the
## only way onto a channel is `park`, which takes the next serial from the
## clock the channel was bound to (`newExits`): no other clock can be
## passed. An entry keeps its serial until it is claimed. It lives on the
## entry, never on the item, so one path parked twice (or forked from a
## parked one) cannot move another entry's serial. What is not claimed is
## never touched: a claim filters the channel in place, and the entries it
## keeps stay where they were with their own serials. A mark is taken only
## from a clock and remembers it; reading a channel with a mark of another
## clock, or with a default one, is a fault.
##
## The generic walks over a group (`newExits`, `claimAt`, `visitSince`,
## `parkOnEach`) reach a channel's items through two hooks the item type
## provides: `exitPath(var item): var P` (the path it carries) and, for a
## channel a `try` claims, `depthOf(item): int` (the handler depth it is
## bound for).

type
  ExitClock* = ref object
    ## The walk's exit serial counter. Monotonic for the whole walk: never
    ## saved or restored. A `ref`, so every channel bound to it shares it.
    last: int

  ExitMark* = object
    ## The clock's reading when a scope began (`mark`). An entry was parked
    ## after it when its serial is past it. Only a clock makes one.
    clock: ExitClock
    serial: int

  ParkedEntry[T] = object
    item: T
    serial: int

  ExitChannel*[T] = object
    ## One exit channel: its entries in the order they were parked, and the
    ## clock it parks on (nil until bound by `newExits`).
    clock: ExitClock
    entries: seq[ParkedEntry[T]]

proc newExitClock*(): ExitClock = ExitClock()

func mark*(clock: ExitClock): ExitMark =
  ## The reading a scope keeps at its start.
  doAssert clock != nil, "exits: mark of an unset clock"
  ExitMark(clock: clock, serial: clock.last)

proc checkMark(owner: ExitClock; m: ExitMark) {.inline.} =
  doAssert m.clock != nil and m.clock == owner,
    "exits: a mark read against a clock that did not make it"

func parkedSince*(clock: ExitClock; m: ExitMark): bool =
  ## Whether anything was parked, on any channel of this clock, after `m`.
  checkMark(clock, m)
  clock.last > m.serial

proc park*[T](ch: var ExitChannel[T]; item: sink T) =
  ## The one way onto a channel: append `item` with its clock's next serial.
  doAssert ch.clock != nil, "exits: park on a channel bound to no clock"
  inc ch.clock.last
  ch.entries.add ParkedEntry[T](item: item, serial: ch.clock.last)

func len*[T](ch: ExitChannel[T]): int = ch.entries.len

iterator items*[T](ch: ExitChannel[T]): T =
  ## Every entry's item, in parking order.
  for e in ch.entries: yield e.item

func contents*[T](ch: ExitChannel[T]): seq[T] =
  ## Every entry's item, in parking order, as a seq.
  result = newSeqOfCap[T](ch.entries.len)
  for e in ch.entries: result.add e.item

proc takeAll*[T](ch: var ExitChannel[T]): seq[T] =
  ## Claim every entry, whenever it was parked, leaving the channel empty:
  ## for the scope that owns the whole channel (a loop iteration taking
  ## its `continue`s).
  result = ch.contents
  ch.entries.setLen(0)

proc claimAt*[T](ch: var ExitChannel[T]; m: ExitMark; depth: int): seq[T] =
  ## Claim the entries parked after `m` whose item's `depthOf` is `depth`,
  ## in parking order. Every other entry stays, in order, with its serial.
  mixin depthOf
  if ch.entries.len == 0: return
  checkMark(ch.clock, m)
  var kept: seq[ParkedEntry[T]]
  for e in ch.entries:
    if e.serial > m.serial and depthOf(e.item) == depth: result.add e.item
    else: kept.add e
  ch.entries = move kept

iterator mitemsSince*[T](ch: var ExitChannel[T]; m: ExitMark): var T =
  ## The items of the entries parked after `m`, to replace in place. An
  ## entry's serial is not the item's to change.
  if ch.entries.len > 0:
    checkMark(ch.clock, m)
    for e in ch.entries.mitems:
      if e.serial > m.serial: yield e.item

# ---- Groups ------------------------------------------------------------------
# Each walk below recurses through nested groups and visits the channels in
# declaration order. A field that is neither a channel nor a group is a
# compile error: a group holds only channels, so every channel in it is
# bound, stamped and probed by the same walk.

proc bindGroup[G: object](g: var G; clock: ExitClock) =
  for f in fields(g):
    when f is ExitChannel: f.clock = clock
    elif f is object: bindGroup(f, clock)
    else: {.error: "exits: a group holds only exit channels and groups".}

proc newExits*[G: object](clock: ExitClock; _: typedesc[G]): G =
  ## An empty group of type `G`, every channel in it bound to `clock`.
  doAssert clock != nil, "exits: newExits with an unset clock"
  bindGroup(result, clock)

proc claimAt*[G: object](g: var G; m: ExitMark; depth: int): G =
  ## Claim, from every channel of the group in declaration order, the
  ## entries parked after `m` at `depth` (`claimAt` on each). The result is
  ## a group of the claimed items, read with `contents`; it is bound to no
  ## clock, so nothing can be parked on it.
  for mine, taken in fields(g, result):
    when mine is ExitChannel:
      for item in mine.claimAt(m, depth):
        taken.entries.add ParkedEntry[typeof(item)](item: item)
    elif mine is object:
      taken = mine.claimAt(m, depth)
    else: {.error: "exits: a group holds only exit channels and groups".}

proc visitSince*[G: object; P](g: var G; m: ExitMark;
                               visit: proc (p: var P) {.closure.}) =
  ## `visit` the path (`exitPath`) of every entry of the group parked after
  ## `m`, to replace it in place.
  mixin exitPath
  for f in fields(g):
    when f is ExitChannel:
      for e in f.mitemsSince(m): visit(exitPath(e))
    elif f is object: visitSince(f, m, visit)
    else: {.error: "exits: a group holds only exit channels and groups".}

proc parkOnEach*[G: object; P](g: var G; mk: proc (): P {.closure.}) =
  ## Park one default item on every channel of the group, carrying the path
  ## `mk` makes: for a probe that must reach every channel there is.
  mixin exitPath
  for f in fields(g):
    when f is ExitChannel:
      var item: typeof(f.entries[0].item)
      exitPath(item) = mk()
      f.park(item)
    elif f is object: parkOnEach(f, mk)
    else: {.error: "exits: a group holds only exit channels and groups".}
