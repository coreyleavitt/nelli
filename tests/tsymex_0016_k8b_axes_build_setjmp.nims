# The cpp backend cannot build setjmp exceptions, and on Windows a setjmp build
# of the walk crashes entering its fiber (SIGSEGV in `runSymexCaught`); there
# the suite pins the default exceptions instead.
if getCommand() != "cpp" and not defined(windows):
  switch("exceptions", "setjmp")
