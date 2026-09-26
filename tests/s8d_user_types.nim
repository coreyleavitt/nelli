## RFC-0005 S8d helper module (not a test file): SUTs over USER types whose
## names collide with stdlib/system type heads. It lives in its own module
## because the declarations below shadow `seq`/`bool`/`int8`/... for every
## line of the module they are in, and the symex witness emitter spells the
## real `seq`/`Table`/... by name in its caller's scope; the test file imports
## only the SUT procs, so neither side sees the other's names.
##
## Each type is built so that the stdlib model of its NAME gives a different
## answer from the program: a fixed-length array is not a variable-length
## container, an alias of `int` is not `range[0..high(int)]` or 8 bits wide,
## a distinct over a user `int32` alias is not a Unicode scalar.
from nelli/engine/markers import symexTarget

type
  seq*[T] = array[3, T]
    ## A user generic named `seq`: always exactly three elements.
  Table*[K, V] = array[3, V]
    ## A user generic named `Table` (the key parameter is phantom).
  HashSet*[T] = array[3, T]
    ## A user generic named `HashSet`.
  Option*[T] = object
    ## A user generic named `Option`.
    has*: system.bool
    val*: T
  Natural* = int
    ## NOT `system.Natural`: admits negatives.
  int8* = int
    ## NOT `system.int8`: 64 bits wide.
  RuneImpl* = int32
  Rune* = distinct RuneImpl
    ## NOT `unicode.Rune`: any int32, negatives included.
  bool* = enum
    ## NOT `system.bool`: three members.
    bNo, bYes, bMaybe

proc s8dSeqLen*(s: seq[int]) =
  ## Real: `len` of an `array[3, int]` is 3.
  let n = s.len
  if n == 4:
    symexTarget("s8d_seq_len")

proc s8dTableLen*(t: Table[string, int]) =
  ## Real: 3, whatever the (phantom) key type.
  let n = t.len
  if n == 4:
    symexTarget("s8d_table_len")

proc s8dSetLen*(s: HashSet[int]) =
  ## Real: 3.
  let n = s.len
  if n == 4:
    symexTarget("s8d_set_len")

proc s8dOption*(o: Option[int]) =
  ## Real: reachable (has = true, val = 3).
  if o.has and o.val == 3:
    symexTarget("s8d_option")

proc s8dNatural*(x: Natural) =
  ## Real: reachable -- this `Natural` is a plain `int`.
  if x < 0:
    symexTarget("s8d_natural")

proc s8dLowInt8*(x: int) =
  ## Real: `low(int8)` is `low(int)`, and no int is below it.
  if x < low(int8):
    symexTarget("s8d_low_int8")

proc s8dRune*(r: Rune) =
  ## Real: reachable -- any int32, negatives included.
  if int32(r) < 0:
    symexTarget("s8d_rune")

proc s8dBool*(b: bool) =
  ## Real: reachable (b = bMaybe) -- this `bool` has a third member.
  if b != bNo and b != bYes:
    symexTarget("s8d_bool")
