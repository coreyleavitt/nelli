## RFC-0016 CR4-H1 (round 3). A chain of 20 templates, each wrapping the next,
## the last pushing: past the read depth, so the scan declines, never trusts.
template deepT0*(body: untyped) =
  deepT1(body)
template deepT1*(body: untyped) =
  deepT2(body)
template deepT2*(body: untyped) =
  deepT3(body)
template deepT3*(body: untyped) =
  deepT4(body)
template deepT4*(body: untyped) =
  deepT5(body)
template deepT5*(body: untyped) =
  deepT6(body)
template deepT6*(body: untyped) =
  deepT7(body)
template deepT7*(body: untyped) =
  deepT8(body)
template deepT8*(body: untyped) =
  deepT9(body)
template deepT9*(body: untyped) =
  deepT10(body)
template deepT10*(body: untyped) =
  deepT11(body)
template deepT11*(body: untyped) =
  deepT12(body)
template deepT12*(body: untyped) =
  deepT13(body)
template deepT13*(body: untyped) =
  deepT14(body)
template deepT14*(body: untyped) =
  deepT15(body)
template deepT15*(body: untyped) =
  deepT16(body)
template deepT16*(body: untyped) =
  deepT17(body)
template deepT17*(body: untyped) =
  deepT18(body)
template deepT18*(body: untyped) =
  deepT19(body)
template deepT19*(body: untyped) =
  {.push rangeChecks: off.}
  body
  {.pop.}
