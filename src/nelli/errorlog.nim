## R2-3: a bounded record of error messages. A failing backend can raise one
## error per execution over millions of executions; keeping each is an
## unbounded leak. An `ErrorLog` keeps each DISTINCT message once, in
## first-occurrence order, up to `errorLogCap`, and counts every message it
## did not keep (a repeat, or a new one past the cap).

import std/sets

const errorLogCap* = 256
  ## The most distinct messages an `ErrorLog` keeps.

type ErrorLog* = object
  entries*: seq[string]     ## distinct messages, first occurrence first
  omitted*: int             ## every message added and not kept in `entries`
  seen: HashSet[string]

proc add*(l: var ErrorLog; msg: string) =
  if msg in l.seen: inc l.omitted
  elif l.entries.len >= errorLogCap: inc l.omitted
  else:
    l.seen.incl msg
    l.entries.add msg

proc add*(l: var ErrorLog; msgs: openArray[string]) =
  for m in msgs: l.add m

proc merge*(l: var ErrorLog; other: ErrorLog) =
  ## Folds `other` in as if its entries were added after `l`'s, and carries
  ## its omitted count.
  l.add other.entries
  l.omitted += other.omitted
