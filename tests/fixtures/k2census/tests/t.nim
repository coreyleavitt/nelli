suite "x":
  test "a":
    skip()
  test "b":
    skipCell(magic("DivU"))
  test "c":
    # skip() in a comment is not counted
    skip()
