## RFC-0005 code review, round 2 (SM1, SM2, isOwnRuntime) -- the implementation
## digest's serialisation is injective, the hash is a real one, and a nelli
## runtime path is told from a user's.
##
## SM1: the old serialisation wrote `$ord(kind)` and then `:val` with no
## delimiter, so a leaf's text ran into the next sibling's kind digits:
## StmtList(IntLit 1, Empty) and StmtList(IntLit 11) were the same string.
import std/[unittest, macros, strutils]
import nelli/smt/impl_digest
import nelli/smt/sha256   ## review R3 (E10): the one SHA-256, shared

macro serialised(build: static[int]): untyped =
  ## The serialisation of the `build`-th tree of a fixed table.
  let one = newIntLitNode(1)
  let eleven = newIntLitNode(11)
  var t: NimNode
  case build
  of 0: t = newStmtList(one, newEmptyNode())        # [1, <empty>]
  of 1: t = newStmtList(eleven)                      # [11]
  of 2: t = newStmtList(ident("a"), ident("b"))      # [a, b]
  of 3: t = newStmtList(ident("ab"))                 # [ab]
  of 4: t = newStmtList(newStrLitNode("1"), newStrLitNode("2"))
  of 5: t = newStmtList(newStrLitNode("1\"2"))
  of 6: t = newStmtList(newStmtList(one), eleven)    # [[1], 11]
  of 7: t = newStmtList(newStmtList(one, eleven))    # [[1, 11]]
  of 8: t = newStmtList(ident("x"), newEmptyNode())
  of 9: t = newStmtList(ident("x1"))
  else: t = newEmptyNode()
  result = newLit(serialiseNode(t))

suite "R2 SM1: the serialisation is injective":
  test "a literal does not run into the next sibling's kind digits":
    check serialised(0) != serialised(1)
  test "idents split differently differ":
    check serialised(2) != serialised(3)
  test "strings split differently differ":
    check serialised(4) != serialised(5)
  test "nesting differs from flat":
    check serialised(6) != serialised(7)
  test "an ident followed by an empty node is not a longer ident":
    check serialised(8) != serialised(9)
  test "equal trees serialise equally":
    check serialised(0) == serialised(0)

suite "R2 SM2: the hash":
  test "sha256 standard vectors":
    check sha256Hex("") ==
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    check sha256Hex("abc") ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    check sha256Hex("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
  test "review R3 (E10): every tail length, against a reference":
    # 55, 56, 63, 64 and 65 bytes straddle the one- and two-block padding;
    # 1,000,000 x 'a' is the FIPS long vector, read in place block by block.
    check sha256Hex(repeat('a', 55)) ==
      "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
    check sha256Hex(repeat('a', 56)) ==
      "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
    check sha256Hex(repeat('a', 63)) ==
      "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"
    check sha256Hex(repeat('a', 64)) ==
      "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
    check sha256Hex(repeat('a', 65)) ==
      "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"
    check sha256Hex(repeat('a', 1_000_000)) ==
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
  test "it agrees at compile time and run time":
    const ct = sha256Hex("nelli" & repeat('x', 200))
    check ct == sha256Hex("nelli" & repeat('x', 200))
    const ct56 = sha256Hex(repeat('a', 56))   # the two-block tail, in the VM
    check ct56 == sha256Hex(repeat('a', 56))

suite "R2: isOwnRuntime path test":
  test "nelli's runtime directory matches only itself":
    check pathUnder("/a/src/nelli/smt/x.nim", "/a/src/nelli/")
    check not pathUnder("/b/src/nelli/smt/x.nim", "/a/src/nelli/")
    check not pathUnder("/a/src/nelli-extras/x.nim", "/a/src/nelli/")
    check not pathUnder("/a/src/nellix.nim", "/a/src/nelli/")
    check not pathUnder("/home/u/proj/src/nelli/x.nim", "/a/src/nelli/")
    check pathUnder("C:\\a\\src\\nelli\\x.nim", "C:/a/src/nelli/") or
          defined(windows) == false
