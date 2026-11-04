## RFC-0005 review R4. The walker's exit channels: where a path waits after
## it left the statement that produced it -- through a `return`, a `break`
## or `continue`, a caught or escaping raise, or a `finally` it must run
## first -- until the scope it is bound for claims it.
##
## The runtime keeps one `ExitChannel` per channel (the SUT's and each
## call's returns, each loop frame's breaks and continues, and the call
## frame's raise and `finally` channels), all serialized by the walk's one
## `ExitClock`. Two scopes read a channel by when its entries were parked:
##   * a statement stamps its stray lowering taint on the entries parked
##     after it began (`mark` at its start, `mitemsSince` at its end);
##   * a `try` claims, at its handler depth, only the entries parked while
##     it ran (`claimAt`): an older entry at the same depth belongs to a
##     try whose `except` arm holds this one.
##
## Both are only as sound as the serials. The storage is private, so the
## only way onto a channel is `park`, which takes the next serial; an entry
## keeps it until it is claimed. It lives on the entry, never on the item,
## so one path parked twice (or forked from a parked one) cannot move
## another entry's serial. What is not claimed is never touched: a claim
## filters the channel in place, and the entries it keeps stay where they
## were with their own serials.

type
  ExitClock* = object
    ## The walk's exit serial counter. Monotonic for the whole walk: never
    ## saved or restored.
    last: int

  ExitMark* = distinct int
    ## The clock's reading when a scope began (`mark`). An entry was parked
    ## after it when its serial is past it.

  ParkedEntry[T] = object
    item: T
    serial: int

  ExitChannel*[T] = object
    ## One exit channel: its entries in the order they were parked.
    entries: seq[ParkedEntry[T]]

func mark*(clock: ExitClock): ExitMark =
  ## The reading a scope keeps at its start.
  ExitMark(clock.last)

func parkedSince*(clock: ExitClock; m: ExitMark): bool =
  ## Whether anything was parked, on any channel of this clock, after `m`.
  clock.last > int(m)

proc park*[T](ch: var ExitChannel[T]; clock: var ExitClock; item: sink T) =
  ## The one way onto a channel: append `item` with the clock's next serial.
  inc clock.last
  ch.entries.add ParkedEntry[T](item: item, serial: clock.last)

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
  ## Claim the entries parked after `m` whose item's `depth` is `depth`, in
  ## parking order. Every other entry stays, in order, with its serial.
  var kept: seq[ParkedEntry[T]]
  for e in ch.entries:
    if e.serial > int(m) and e.item.depth == depth: result.add e.item
    else: kept.add e
  ch.entries = move kept

iterator mitemsSince*[T](ch: var ExitChannel[T]; m: ExitMark): var T =
  ## The items of the entries parked after `m`, to replace in place. An
  ## entry's serial is not the item's to change.
  for e in ch.entries.mitems:
    if e.serial > int(m): yield e.item
