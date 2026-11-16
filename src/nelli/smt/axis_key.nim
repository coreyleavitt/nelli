## RFC-0016 0.10.0 review D5 -- the leaf the axis modules share.
##
## An axis is a site enum, a `const` `AxisTable` and a verb returning an
## `Admit` (`admission`). Every axis module builds its table the same way: a
## row is `(key, Row)`, and a family of names that share one reason becomes one
## row each. That builder lived as a private copy in each axis module
## (`decided`/`declines`, `proved`/`may`, `inert`/`read`/`declined`/
## `neverField`, `floatDeclined`); it is here once.
##
## `MagicModel` is also here: it is the payload the magic axis proves, and the
## definedness axis takes it as the proof of a defect site. Held below both, the
## two axis modules do not import each other.
##
## This module imports `admission` and `errorkind` only: no axis module, no
## walker. The census in `tests/tsymex_0016_d5_axisdeps.nim` keeps it so.
import std/options
import ./admission
import ./errorkind

type
  AxisRow*[S: enum; P] = tuple[key: string, row: Row[S, P]]
    ## One entry of an axis's row list, the `axisTable` argument's element.

  MagicModel* = enum
    mmModelled, mmPartial, mmFolded, mmBody

func modelledEach*[S: enum; P](prefix: string; names: openArray[string];
                               payload: P; sites: set[S]; why: string;
                               elsewhere = some(feUnadmitted)):
    seq[AxisRow[S, P]] =
  ## An admitted row per name, keyed `prefix & name`, all with one payload,
  ## site set and reason.
  for n in names:
    result.add (prefix & n, modelled[S, P](payload, sites, why, elsewhere))

func refusedEach*[S: enum; P](prefix: string; names: openArray[string];
                              kind: Option[SymexErrorKind]; why: string;
                              intent = iModel;
                              never = nrByDesign): seq[AxisRow[S, P]] =
  ## A declined row per name, keyed `prefix & name`, all with one kind and
  ## reason.
  for n in names:
    result.add (prefix & n, refused[S, P](kind, why, intent, never))
