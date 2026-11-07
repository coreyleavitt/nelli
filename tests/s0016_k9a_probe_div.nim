## K9a probe: an integer division by zero the compiler cannot fold, raw C so no
## Nim check intervenes. Natively a SIGFPE on POSIX, 0xC0000094 on Windows.
{.emit: "static volatile int k9aZero = 0;".}
proc cdiv(): cint =
  {.emit: "`result` = 10 / k9aZero;".}
echo "RESULT ", cdiv()
