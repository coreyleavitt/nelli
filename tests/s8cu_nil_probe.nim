## RFC-0005 S8cu fixture (no nelli): a nil field read under `except
## NilAccessDefect` and a `finally`, compiled by `tsymex_rfc0005_s8cu_nil_native`
## in each exceptions mode, with and without `std/segfaults`.
when defined(withSegfaults):
  import std/segfaults

type R = ref object
  a: int

proc f(r: R): int =
  try:
    result = r.a
  except NilAccessDefect:
    echo "CAUGHT"
    result = -1
  finally:
    echo "FINALLY"

echo "RET ", f(nil)
