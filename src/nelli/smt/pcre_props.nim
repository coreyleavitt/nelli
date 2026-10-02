## RFC-0005 S8bb. PCRE 8.45's byte sets for `\p{..}` and for the classes
## `(*UCP)` changes, in Nim's `std/re` mode (no UTF: a subject byte is the
## code point U+0000..U+00FF of the same value).
##
## Generated, not written: every set is the concrete `re` run on each of
## the 256 one-byte subjects (`"\p{" & name & "}"` and `"(*UCP)" & cls`),
## PCRE 8.45 in the dev image. A map is 64 hex digits, byte `k` (digits
## `2k .. 2k+1`) holding bytes `8k .. 8k+7`, least significant bit first.
## `pcreEmptyProps` are the property and script names PCRE accepts whose
## set is empty in this range; a name in neither list is not read (the
## pattern is `psUnknown`). `\P{X}` and `\p{^X}` are the complements
## (probed). Case-insensitive matching does not change a property set
## (probed). The pinned differential is
## `tests/tsymex_rfc0005_s8bb_selection.nim`.

import std/strutils

const pcrePropMaps* = [
  ("C", "FFFFFFFF000000000000000000000080FFFFFFFF002000000000000000000000"),
  ("Cc", "FFFFFFFF000000000000000000000080FFFFFFFF000000000000000000000000"),
  ("Cf", "0000000000000000000000000000000000000000002000000000000000000000"),
  ("L", "0000000000000000FEFFFF07FEFFFF070000000000042004FFFF7FFFFFFF7FFF"),
  ("Ll", "000000000000000000000000FEFFFF07000000000000200000000080FFFF7FFF"),
  ("Lo", "0000000000000000000000000000000000000000000400040000000000000000"),
  ("Lu", "0000000000000000FEFFFF07000000000000000000000000FFFF7F7F00000000"),
  ("N", "000000000000FF0300000000000000000000000000000C720000000000000000"),
  ("Nd", "000000000000FF03000000000000000000000000000000000000000000000000"),
  ("No", "000000000000000000000000000000000000000000000C720000000000000000"),
  ("P", "00000000EEF7008C010000B800000028000000008208C0880000000000000000"),
  ("Pc", "0000000000000000000000800000000000000000000000000000000000000000"),
  ("Pd", "0000000000200000000000000000000000000000000000000000000000000000"),
  ("Pe", "0000000000020000000000200000002000000000000000000000000000000000"),
  ("Pf", "0000000000000000000000000000000000000000000000080000000000000000"),
  ("Pi", "0000000000000000000000000000000000000000000800000000000000000000"),
  ("Po", "00000000EED4008C0100001000000000000000008200C0800000000000000000"),
  ("Ps", "0000000000010000000000080000000800000000000000000000000000000000"),
  ("S", "00000000100800700000004001000050000000007CD313010000800000008000"),
  ("Sc", "00000000100000000000000000000000000000003C0000000000000000000000"),
  ("Sk", "0000000000000000000000400100000000000000008110010000000000000000"),
  ("Sm", "0000000000080070000000000000005000000000001002000000800000008000"),
  ("So", "0000000000000000000000000000000000000000404201000000000000000000"),
  ("Z", "0000000001000000000000000000000000000000010000000000000000000000"),
  ("Zs", "0000000001000000000000000000000000000000010000000000000000000000"),
  ("Any", "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"),
  ("L&", "0000000000000000FEFFFF07FEFFFF070000000000002000FFFF7FFFFFFF7FFF"),
  ("Xan", "000000000000FF03FEFFFF07FEFFFF070000000000042C76FFFF7FFFFFFF7FFF"),
  ("Xps", "003E000001000000000000000000000020000000010000000000000000000000"),
  ("Xsp", "003E000001000000000000000000000020000000010000000000000000000000"),
  ("Xwd", "000000000000FF03FEFFFF87FEFFFF070000000000042C76FFFF7FFFFFFF7FFF"),
  ("Xuc", "0000000010000000010000000100000000000000FFFFFFFFFFFFFFFFFFFFFFFF"),
  ("Common", "FFFFFFFFFFFFFFFF010000F8010000F8FFFFFFFFFFFBFFFB0000800000008000"),
  ("Latin", "0000000000000000FEFFFF07FEFFFF070000000000040004FFFF7FFFFFFF7FFF"),
]

const pcreEmptyProps* = [
  "Cn", "Co", "Cs", "Lm", "Lt", "M", "Mc", "Me", "Mn", "Nl", "Zl", "Zp",
  "Arabic", "Armenian", "Avestan", "Balinese", "Bamum", "Bassa_Vah", "Batak",
  "Bengali", "Bopomofo", "Brahmi", "Braille", "Buginese", "Buhid",
  "Canadian_Aboriginal", "Carian", "Caucasian_Albanian", "Chakma", "Cham",
  "Cherokee", "Coptic", "Cuneiform", "Cypriot", "Cyrillic", "Deseret",
  "Devanagari", "Duployan", "Egyptian_Hieroglyphs", "Elbasan", "Ethiopic",
  "Georgian", "Glagolitic", "Gothic", "Grantha", "Greek", "Gujarati",
  "Gurmukhi", "Han", "Hangul", "Hanunoo", "Hebrew", "Hiragana",
  "Imperial_Aramaic", "Inherited", "Inscriptional_Pahlavi",
  "Inscriptional_Parthian", "Javanese", "Kaithi", "Kannada", "Katakana",
  "Kayah_Li", "Kharoshthi", "Khmer", "Khojki", "Khudawadi", "Lao", "Lepcha",
  "Limbu", "Linear_A", "Linear_B", "Lisu", "Lycian", "Lydian", "Mahajani",
  "Malayalam", "Mandaic", "Manichaean", "Meetei_Mayek", "Mende_Kikakui",
  "Meroitic_Cursive", "Meroitic_Hieroglyphs", "Miao", "Modi", "Mongolian",
  "Mro", "Myanmar", "Nabataean", "New_Tai_Lue", "Nko", "Ogham", "Ol_Chiki",
  "Old_Italic", "Old_North_Arabian", "Old_Permic", "Old_Persian",
  "Old_South_Arabian", "Old_Turkic", "Oriya", "Osmanya", "Pahawh_Hmong",
  "Palmyrene", "Pau_Cin_Hau", "Phags_Pa", "Phoenician", "Psalter_Pahlavi",
  "Rejang", "Runic", "Samaritan", "Saurashtra", "Sharada", "Shavian",
  "Siddham", "Sinhala", "Sora_Sompeng", "Sundanese", "Syloti_Nagri",
  "Syriac", "Tagalog", "Tagbanwa", "Tai_Le", "Tai_Tham", "Tai_Viet", "Takri",
  "Tamil", "Telugu", "Thaana", "Thai", "Tibetan", "Tifinagh", "Tirhuta",
  "Ugaritic", "Vai", "Warang_Citi", "Yi"
]

const pcreUcpMaps* = [
  ("\\w", "000000000000FF03FEFFFF87FEFFFF070000000000042C76FFFF7FFFFFFF7FFF"),
  ("\\W", "FFFFFFFFFFFF00FC01000078010000F8FFFFFFFFFFFBD3890000800000008000"),
  ("\\s", "003E000001000000000000000000000020000000010000000000000000000000"),
  ("\\S", "FFC1FFFFFEFFFFFFFFFFFFFFFFFFFFFFDFFFFFFFFEFFFFFFFFFFFFFFFFFFFFFF"),
  ("[[:alpha:]]", "0000000000000000FEFFFF07FEFFFF070000000000042004FFFF7FFFFFFF7FFF"),
  ("[[:lower:]]", "000000000000000000000000FEFFFF07000000000000200000000080FFFF7FFF"),
  ("[[:upper:]]", "0000000000000000FEFFFF07000000000000000000000000FFFF7F7F00000000"),
  ("[[:alnum:]]", "000000000000FF03FEFFFF07FEFFFF070000000000042C76FFFF7FFFFFFF7FFF"),
  ("[[:blank:]]", "0002000001000000000000000000000000000000010000000000000000000000"),
  ("[[:graph:]]", "00000000FEFFFFFFFFFFFFFFFFFFFF7F00000000FEFFFFFFFFFFFFFFFFFFFFFF"),
  ("[[:print:]]", "00000000FFFFFFFFFFFFFFFFFFFFFF7F00000000FFFFFFFFFFFFFFFFFFFFFFFF"),
  ("[[:punct:]]", "00000000FEFF00FC010000F801000078000000008208C0880000000000000000"),
  ("[[:space:]]", "003E000001000000000000000000000020000000010000000000000000000000"),
  ("[[:word:]]", "000000000000FF03FEFFFF87FEFFFF070000000000042C76FFFF7FFFFFFF7FFF"),
  ("[[:^alpha:]]", "FFFFFFFFFFFFFFFF010000F8010000F8FFFFFFFFFFFBDFFB0000800000008000"),
]

proc decodeMap(h: string): set[char] =
  for k in 0 ..< 32:
    let v = parseHexInt(h[2 * k .. 2 * k + 1])
    for bit in 0 .. 7:
      if (v and (1 shl bit)) != 0: result.incl char(8 * k + bit)

proc pcrePropSet*(name: string): (bool, set[char]) =
  ## The byte set of `\p{name}`, or `(false, {})` for a name not read.
  for (n, h) in pcrePropMaps:
    if n == name: return (true, decodeMap(h))
  if name in pcreEmptyProps: return (true, {})
  (false, {})

proc pcreUcpSet*(cls: string): (bool, set[char]) =
  ## Under `(*UCP)`: the byte set of `\w \W \s \S` or `[[:name:]]`
  ## (`cls` spelled so), or `(false, {})` when UCP leaves it unchanged.
  for (n, h) in pcreUcpMaps:
    if n == cls: return (true, decodeMap(h))
  (false, {})
