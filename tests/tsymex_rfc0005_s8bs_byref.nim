## RFC-0005 (soundness channels) slice S8bs -- a `var` or `addr` actual
## named by a path into an address-taken variable, and a heap lvalue passed
## by reference (through inheritance conversions too). The exhibit and the
## family are in `tsymex_rfc0005_s8bs_addrglobal.nim`.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
include "s8bs_suts.nim"

suite "S8bs: paths by name and by reference":

  test "nim: paths by name":
    let ks2 = [-1, 0, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    let h = nativeHits(sutVariant, ks2) + nativeHits(sutVariantByName, ks2) +
            nativeHits(sutTwoDeepByName, ks2) +
            nativeHits(sutHeapFieldByName, ks2) +
            nativeHits(sutCaptureByName, ks2) +
            nativeHits(sutProcValueByName, ks2) +
            nativeHits(sutAddrActualByName, ks2) + nativeHits(sutNested, ks2)
    for l in ["va", "van", "tdn", "hfn", "cpn", "pvn", "aa", "ne"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a variant-arm field":
    clean(sutVariant, "va", sxSat)
    clean(sutVariant, "va_dead", sxUnsat)
    clean(sutVariantByName, "van", sxSat)
    clean(sutVariantByName, "van_dead", sxUnsat)
  test "by name, through every route":
    clean(sutTwoDeepByName, "tdn", sxSat)
    clean(sutTwoDeepByName, "tdn_dead", sxUnsat)
    clean(sutHeapFieldByName, "hfn", sxSat)
    clean(sutHeapFieldByName, "hfn_dead", sxUnsat)
    clean(sutCaptureByName, "cpn", sxSat)
    clean(sutCaptureByName, "cpn_dead", sxUnsat)
    # RFC-0005 S8bu: a closure descent binds the formal to the cell too
    # (`bindVarLocs`); S8bs declined it.
    clean(sutProcValueByName, "pvn", sxSat)
    clean(sutProcValueByName, "pvn_dead", sxUnsat)
    clean(sutNested, "ne", sxSat)
    clean(sutNested, "ne_dead", sxUnsat)
  test "an addr actual by name":
    # RFC-0005 S8bu: `addr b.x` of an address-taken `b` is a sub-cell of
    # `b`'s cell (`bindVarLocs`); S8bs declined it (it was a swapped verdict).
    clean(sutAddrActualByName, "aa", sxSat)
    clean(sutAddrActualByName, "aa_dead", sxUnsat)

  test "nim: by reference, and through conversions":
    let ks3 = [-1, 0, 5, 17, 18, 19, 20, 21, 22, 23]
    let h = nativeHits(sutDerefPlain, ks3) + nativeHits(sutDerefInner, ks3) +
            nativeHits(sutRefDeref, ks3) + nativeHits(sutPtrValueByName, ks3) +
            nativeHits(sutUpcast, ks3) + nativeHits(sutDowncast, ks3) +
            nativeHits(sutDowncastBad, ks3)
    for l in ["dp", "di", "rd", "pq", "uc", "dc", "dx"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h
  test "a heap lvalue goes by reference":
    clean(sutDerefPlain, "dp", sxSat)
    clean(sutDerefPlain, "dp_dead", sxUnsat)
    clean(sutDerefInner, "di", sxSat)
    clean(sutDerefInner, "di_dead", sxUnsat)
    clean(sutRefDeref, "rd", sxSat)
    clean(sutRefDeref, "rd_dead", sxUnsat)
    clean(sutPtrValueByName, "pq", sxSat)
    clean(sutPtrValueByName, "pq_dead", sxUnsat)
  test "an inheritance conversion on a by-reference actual":
    # RFC-0005 S8cs: `BaseR` and `DerR` inherit, and the SUTs read a global of
    # one: a subtype's lifetime hook could write it, so the reads decline
    # (RFC-0016). The verdicts these pins held were not luck: the "nim" test
    # above runs every SUT and hits `uc`, `dc` and `dx`, never a `_dead`.
    template routeDeclines(fn: typed, lbl: string) =
      block:
        let r = symexFind(fn, tLabel(lbl))
        checkpoint lbl & " " & $r.status & " " & show(r.errors)
        check r.status == sxUnknown
        var named = false
        for e in r.errors:
          if e.kind == feGlobalRouteUnproved: named = true
        check named
    routeDeclines(sutUpcast, "uc")
    routeDeclines(sutUpcast, "uc_dead")
    routeDeclines(sutDowncast, "dc")
    routeDeclines(sutDowncast, "dc_dead")
    routeDeclines(sutDowncastBad, "dx_dead")
    # `dx` is reached on a path that does not read `gdr`: it stays an `sxSat`,
    # and the decline of the other path's read is reported beside it.
    block:
      let r = symexFind(sutDowncastBad, tLabel("dx"))
      checkpoint "dx " & $r.status & " " & show(r.errors)
      check r.status == sxSat
      for e in r.errors:
        check e.severity == sevHint or e.kind == feGlobalRouteUnproved
