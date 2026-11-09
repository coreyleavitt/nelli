## PRC-02 probe 3. An override of `area` in a module the test never imports.
import prc03_types

method area*(x: Sub; v: int): int {.gcsafe.} = v + 1
