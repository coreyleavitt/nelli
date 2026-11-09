## PRC-02 probe 3. The base type and its base method. The override lives in
## `prc03_over`, which only `prc03_sut` imports.
type
  Base* = ref object of RootObj
    b*: int
  Sub* = ref object of Base
    s*: int

method area*(x: Base; v: int): int {.base, gcsafe.} = v
