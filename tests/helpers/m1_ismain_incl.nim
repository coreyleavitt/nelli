## RFC-0016 W3-z P8: a SUT in a file `include`d into the test. The code is the
## main module's (isMainModule is true natively), but its line info names this
## file, so the walker must decline rather than fold false.
proc sutIsMainIncluded(a: int) =
  if isMainModule and a == 3: symexTarget("hit")
