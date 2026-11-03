# The cpp backend cannot build setjmp exceptions; there the suite pins cpp's.
if getCommand() != "cpp":
  switch("exceptions", "setjmp")
