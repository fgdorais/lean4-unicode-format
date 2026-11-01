/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnicodeFormat

open ScalarArray Unicode

/-- A string with every `step`-th Unicode scalar value. -/
def sampleChars (step : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:0x110000 / step + 1] do
    let n := i * step
    if h : n.isValidChar then
      s := s.push (Char.ofNatAux n h)
  return s

/-- Strings covering ASCII, the BMP on both sides of the surrogates, and the astral planes. -/
def samples : List String :=
  ["", "a", "Hello, world!", "café", "∀ε>0", "日本語", "\uD7FF\uE000\uFFFF", "😀", "a😀b",
    "𐀀" ++ (Char.ofNat 0x10FFFF).toString, "𝔸𝔹ℂ", sampleChars 97, sampleChars 1]

/-! UTF-16 encoding -/

#guard (toUTF16 "").size == 0
#guard (toUTF16 "abc").toList == [0x61, 0x62, 0x63]
#guard (toUTF16 "é∀").toList == [0xE9, 0x2200]
#guard (toUTF16 "😀").toList == [0xD83D, 0xDE00]
#guard (toUTF16 "𐀀").toList == [0xD800, 0xDC00]
#guard (toUTF16 (Char.ofNat 0x10FFFF).toString).toList == [0xDBFF, 0xDFFF]
#guard (toUTF16 "\uFFFF").toList == [0xFFFF]
#guard (toUTF16 (sampleChars 1)).size == 0x10000 - 0x800 + 2 * 0x100000

/-! UTF-16 round trips -/

#guard samples.all fun s => fromUTF16? (toUTF16 s) == some s
#guard samples.all fun s => fromUTF16! (toUTF16 s) == s
#guard samples.all fun s => fromUTF16Lossy (toUTF16 s) == s
#guard samples.all fun s => validateUTF16 (toUTF16 s)

/-! UTF-16 slices -/

#guard fromUTF16? (toUTF16 "a😀b")[1...3] == some "😀"
#guard fromUTF16? (toUTF16 "a😀b")[1...*] == some "😀b"
#guard fromUTF16? (toUTF16 "a😀b")[*...2] == none
#guard fromUTF16Lossy (toUTF16 "a😀b")[2...*] == "\uFFFDb"

/-! Ill-formed UTF-16 -/

/-- Code unit sequences with unpaired surrogates, and their lossy decodings. -/
def badUTF16 : List (List UInt16 × String) :=
  [([0xD800], "\uFFFD"),
   ([0xDC00], "\uFFFD"),
   ([0x61, 0xD83D], "a\uFFFD"),
   ([0xDE00, 0xD83D], "\uFFFD\uFFFD"),
   ([0xD83D, 0x61], "\uFFFDa"),
   ([0xD83D, 0xD83D, 0xDE00], "\uFFFD😀"),
   ([0xD83D, 0xDE00, 0xDE00], "😀\uFFFD"),
   ([0xDBFF, 0xDBFF], "\uFFFD\uFFFD")]

#guard badUTF16.all fun (a, _) => fromUTF16? a.toUInt16Array == none
#guard badUTF16.all fun (a, _) => !validateUTF16 a.toUInt16Array
#guard badUTF16.all fun (a, s) => fromUTF16Lossy a.toUInt16Array == s
#guard validateUTF16 [0xD83D, 0xDE00, 0x61].toUInt16Array

/-! UTF-32 -/

#guard (toUTF32 "").size == 0
#guard (toUTF32 "a😀").toList == [0x61, 0x1F600]
#guard (toUTF32 (sampleChars 1)).size == 0x110000 - 0x800
#guard samples.all fun s => fromUTF32? (toUTF32 s) == some s
#guard samples.all fun s => fromUTF32! (toUTF32 s) == s
#guard samples.all fun s => fromUTF32Lossy (toUTF32 s) == s
#guard samples.all fun s => validateUTF32 (toUTF32 s)
#guard samples.all fun s => (toUTF32 s).size == s.length
#guard fromUTF32? (toUTF32 "a😀b")[1...*] == some "😀b"

/-- Code unit sequences with values that are not scalar values, and their lossy decodings. -/
def badUTF32 : List (List UInt32 × String) :=
  [([0xD800], "\uFFFD"),
   ([0xDFFF], "\uFFFD"),
   ([0x110000], "\uFFFD"),
   ([0x61, 0xFFFFFFFF, 0x62], "a\uFFFDb")]

#guard badUTF32.all fun (a, _) => fromUTF32? a.toUInt32Array == none
#guard badUTF32.all fun (a, _) => !validateUTF32 a.toUInt32Array
#guard badUTF32.all fun (a, s) => fromUTF32Lossy a.toUInt32Array == s

/-! UTF-16 and UTF-32 agree -/

#guard samples.all fun s => fromUTF32? (toUTF32 (fromUTF16! (toUTF16 s))) == some s

/-! Encoding schemes -/

open EncodingScheme

/-- Every encoding scheme, with both byte orders for the schemes with a byte order mark. -/
def schemes : List EncodingScheme :=
  [utf8, utf8BOM, utf16BE, utf16LE, .utf16, .utf16 .little,
    utf32BE, utf32LE, .utf32, .utf32 .little]

#guard schemes.all fun e => samples.all fun s => e.decode? (e.encode s) == some s
#guard schemes.all fun e => samples.all fun s => e.decode! (e.encode s) == s
#guard schemes.all fun e => samples.all fun s => e.decodeLossy (e.encode s) == s
#guard schemes.all fun e => samples.all fun s => e.validate (e.encode s)
#guard schemes.all fun e => e.decode? ByteArray.empty == some ""

/-! Encoding scheme bytes -/

#guard (utf8.encode "﻿a").toList == [0xEF, 0xBB, 0xBF, 0x61]
#guard (utf8BOM.encode "a").toList == [0xEF, 0xBB, 0xBF, 0x61]
#guard (utf16BE.encode "a😀").toList == [0x00, 0x61, 0xD8, 0x3D, 0xDE, 0x00]
#guard (utf16LE.encode "a😀").toList == [0x61, 0x00, 0x3D, 0xD8, 0x00, 0xDE]
#guard (EncodingScheme.utf16.encode "a").toList == [0xFE, 0xFF, 0x00, 0x61]
#guard ((utf16 .little).encode "a").toList == [0xFF, 0xFE, 0x61, 0x00]
#guard (utf32BE.encode "😀").toList == [0x00, 0x01, 0xF6, 0x00]
#guard (utf32LE.encode "😀").toList == [0x00, 0xF6, 0x01, 0x00]
#guard (EncodingScheme.utf32.encode "a").toList == [0x00, 0x00, 0xFE, 0xFF, 0x00, 0x00, 0x00, 0x61]
#guard ((utf32 .little).encode "a").toList == [0xFF, 0xFE, 0x00, 0x00, 0x61, 0x00, 0x00, 0x00]

/-! Byte order marks -/

-- A mark is read only by the schemes with one, and only at the start.
#guard utf8.decode? [0xEF, 0xBB, 0xBF, 0x61].toByteArray == some "﻿a"
#guard utf8BOM.decode? [0xEF, 0xBB, 0xBF, 0x61].toByteArray == some "a"
#guard utf8BOM.decode? [0x61].toByteArray == some "a"
#guard utf8BOM.decode? [0xEF, 0xBB, 0xBF, 0xEF, 0xBB, 0xBF].toByteArray == some "﻿"
#guard utf16BE.decode? [0xFE, 0xFF, 0x00, 0x61].toByteArray == some "﻿a"
#guard utf16LE.decode? [0xFF, 0xFE, 0x61, 0x00].toByteArray == some "﻿a"
#guard EncodingScheme.utf16.decode? [0xFE, 0xFF, 0x00, 0x61].toByteArray == some "a"
#guard EncodingScheme.utf16.decode? [0xFF, 0xFE, 0x61, 0x00].toByteArray == some "a"
#guard EncodingScheme.utf16.decode? [0xFE, 0xFF, 0xFE, 0xFF].toByteArray == some "﻿"
#guard utf32BE.decode? [0x00, 0x00, 0xFE, 0xFF].toByteArray == some "﻿"
#guard EncodingScheme.utf32.decode? [0xFF, 0xFE, 0x00, 0x00, 0x61, 0x00, 0x00, 0x00].toByteArray ==
  some "a"

-- Without a mark, the byte order of the scheme, by default big-endian.
#guard EncodingScheme.utf16.decode? [0x00, 0x61].toByteArray == some "a"
#guard (utf16 .little).decode? [0x61, 0x00].toByteArray == some "a"
#guard (utf16 .little).decode? [0xFE, 0xFF, 0x00, 0x61].toByteArray == some "a"
#guard EncodingScheme.utf32.decode? [0x00, 0x00, 0x00, 0x61].toByteArray == some "a"
#guard (utf32 .little).decode? [0x61, 0x00, 0x00, 0x00].toByteArray == some "a"

/-! Ill-formed encoding scheme bytes -/

/-- Ill-formed bytes in a scheme, and their lossy decodings. -/
def badBytes : List (EncodingScheme × List UInt8 × String) :=
  [(utf8, [0x61, 0xFF], "a�"),
   (utf8BOM, [0xEF, 0xBB, 0xBF, 0xFF], "�"),
   (utf16BE, [0x00], "�"),
   (utf16BE, [0x00, 0x61, 0x00], "a�"),
   (utf16BE, [0xD8, 0x3D, 0x00, 0x61], "�a"),
   (utf16LE, [0x3D, 0xD8], "�"),
   (.utf16, [0xFE, 0xFF, 0xDE, 0x00], "�"),
   (.utf16, [0xFF, 0xFE, 0x61], "�"),
   (utf32BE, [0x00, 0x00, 0x00], "�"),
   (utf32BE, [0x00, 0x00, 0x00, 0x61, 0x00], "a�"),
   (utf32BE, [0x00, 0x00, 0xD8, 0x00], "�"),
   (utf32LE, [0x00, 0x00, 0x11, 0x00], "�"),
   (.utf32 .little, [0xFF, 0xFE, 0x00, 0x00, 0x00, 0xD8, 0x00, 0x00], "�")]

#guard badBytes.all fun (e, b, _) => e.decode? b.toByteArray == none
#guard badBytes.all fun (e, b, _) => !e.validate b.toByteArray
#guard badBytes.all fun (e, b, s) => e.decodeLossy b.toByteArray == s

/-! Transcoding -/

#guard schemes.all fun src => schemes.all fun dst => samples.dropLast.all fun s =>
  (src.transcode? dst (src.encode s)).map ByteArray.toList == some (dst.encode s).toList
#guard (utf16LE.transcode? utf8 [0x3D, 0xD8].toByteArray) == none
#guard (utf16LE.transcodeLossy utf8 [0x3D, 0xD8, 0x61, 0x00].toByteArray).toList ==
  [0xEF, 0xBF, 0xBD, 0x61]
