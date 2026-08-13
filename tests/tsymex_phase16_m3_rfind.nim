## Phase 16 — RFC Cluster 3 slice M3: `s.rfind(sub)` (strutils).
##
## Models `s.rfind(sub)` via nim-z3's native `lastIndexOf` (Z3 `(seq.last_indexof
## a sub)`), the byte offset of the LAST occurrence, or -1 when absent — a
## near-clone of the already-modeled `s.find(sub)` (`iekStrFind` → Z3 `indexOf`,
## S4), which returns the FIRST occurrence. This is a native Z3 Sequence-theory
## primitive (`Z3_mk_seq_last_index`), NOT a bounded-scan encoding, so it carries
## no hang risk.
##
## Byte-faithful (ADR-0006): under the ≤0xFF char-range constraint asserted on
## every free string, a byte offset equals a Z3 position offset, so `rfind`'s
## return value is a Nim byte index with no codepoint adjustment — same as
## `find`.
import std/unittest
import std/strutils  ## find/rfind on strings
import nelli/symex
import nelli/smt/canonicalize  ## symexCacheKeyForFn — cache-key distinctness

# --- rfind: present, single occurrence → same offset as find ---
proc rfindBc(s: string) =
  if s == "abc" and s.rfind("bc") == 1:
    symexTarget("hit")

# --- rfind: absent → -1, no crash (parity with find's -1 convention) ---
proc rfindAbsent(s: string) =
  if s == "abc" and s.rfind("zz") == -1:
    symexTarget("hit")

# --- rfind ≠ find (load-bearing): substring appears TWICE, must return the
# LAST occurrence, not the first (proves lastIndexOf, not indexOf). ---
proc rfindVsFindTwice(s: string) =
  if s.rfind("a") == 5 and s.find("a") == 1:
    symexTarget("hit")

# --- UNSAT soundness: an impossible rfind constraint ---
proc rfindImpossible(s: string) =
  if s == "abc" and s.rfind("bc") == 99:
    symexTarget("hit")

suite "symex Phase 16 M3 — string rfind (nim-z3 lastIndexOf)":
  test "rfind: \"abc\".rfind(\"bc\") == 1 is SAT (byte offset, single occurrence)":
    let r = symexFind(rfindBc, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abc"
    check r.witness[0].rfind("bc") == 1  ## witness round-trips against real Nim rfind

  test "rfind absent: \"abc\".rfind(\"zz\") == -1 is SAT (no crash, -1 sentinel)":
    let r = symexFind(rfindAbsent, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abc"
    check r.witness[0].rfind("zz") == -1

  test "rfind != find: last-occurrence semantics distinguishes rfind from find":
    let r = symexFind(rfindVsFindTwice, tLabel("hit"))
    check r.status == sxSat
    let w = r.witness[0]
    check w.rfind("a") == 5   ## real Nim rfind: LAST occurrence
    check w.find("a") == 1    ## real Nim find: FIRST occurrence
    check w.rfind("a") != w.find("a")

  test "rfind UNSAT: an impossible rfind target is unsatisfiable":
    let r = symexFind(rfindImpossible, tLabel("hit"))
    check r.status == sxUnsat

  test "cache-key distinctness: find and rfind on the same receiver/arg differ":
    let rfindKey = symexCacheKeyForFn(rfindBc, tLabel("hit"))
    # A structurally-identical SUT using `find` instead of `rfind` must produce
    # a DIFFERENT cache key — a collision here would be a silent-wrong-answer
    # bug (stale `find` result served for an `rfind` query), the SND-2 Am/At
    # class of defect.
    proc findBcTwin(s: string) =
      if s == "abc" and s.find("bc") == 1:
        symexTarget("hit")
    let findKey = symexCacheKeyForFn(findBcTwin, tLabel("hit"))
    check findKey != rfindKey

  test "walker version floor: symexWalkerVersion >= 49 (M3 rfind modeled)":
    check parseInt(symexWalkerVersion) >= 49
