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

/-! Iterators -/

open Std

/-- The characters of a character iterator. -/
def str {α : Type} [Iterator α Id Char] [IteratorLoop α Id Id] (it : Iter (α := α) Char) :
    String :=
  it.fold String.push ""

/-- The tokens of an iterator, and the iterator where it stops. -/
partial def run {α β : Type} [Iterator α Id β] (it : Iter (α := α) β) (acc : Array β := #[]) :
    Array β × Iter (α := α) β :=
  match it.step with
  | ⟨.yield it' x, _⟩ => run it' (acc.push x)
  | ⟨.skip it', _⟩ => run it' acc
  | ⟨.done, _⟩ => (acc, it)

/-- The error where a strict decoding iterator stops, if any. -/
def stopError? {δ ι τ σ : Type} [Decoder δ τ σ] [Iterator ι Id τ] [Iterators.Productive ι Id]
    (it : Iter (α := DecodeIterator δ ι) σ) : Option DecodeError :=
  (run it).2.decodeError?

/-- The index in the underlying array of a scalar array slice iterator. -/
def idx16 (it : Iter (α := UInt16Array.SliceIterator) UInt16) : Nat := it.internalState.xs.start
def idx8 (it : Iter (α := UInt8Array.SliceIterator) UInt8) : Nat := it.internalState.xs.start

/-! UTF-16 iterators -/

#guard samples.all fun s => (UTF16.encode s.chars).toList == (toUTF16 s).toList
#guard samples.all fun s => str (UTF16.decode (toUTF16 s).iter) == s
#guard samples.all fun s => str (UTF16.decodeLossy (toUTF16 s).iter) == s
#guard badUTF16.all fun (a, s) => str (UTF16.decodeLossy a.toUInt16Array.iter) == s
#guard badUTF16.all fun (a, _) => stopError? (UTF16.decode a.toUInt16Array.iter) ==
  some DecodeError.unpairedSurrogate
#guard samples.all fun s => stopError? (UTF16.decode (toUTF16 s).iter) == none

-- A strict decoder stops at the unpaired surrogate, so its base is at the error.
#guard
  let (cs, it) := run (UTF16.decode [0x61, 0xD83D, 0xDE00, 0xD83D, 0x62].toUInt16Array.iter)
  String.ofList cs.toList == "a😀" && idx16 it.decodeBase == 3 &&
    it.decodeError? == some DecodeError.unpairedSurrogate

/-! UTF-32 iterators -/

#guard samples.all fun s => (UTF32.encode s.chars).toList == (toUTF32 s).toList
#guard samples.all fun s => str (UTF32.decode (toUTF32 s).iter) == s
#guard badUTF32.all fun (a, s) => str (UTF32.decodeLossy a.toUInt32Array.iter) == s
#guard badUTF32.all fun (a, _) => stopError? (UTF32.decode a.toUInt32Array.iter) ==
  some DecodeError.notScalarValue

/-! UTF-8 iterators -/

#guard samples.all fun s => (UTF8.encode s.chars).toList == s.toUTF8.toList
#guard samples.all fun s => str (UTF8.decode s.toUTF8.toUInt8Array.iter) == s
#guard samples.all fun s => stopError? (UTF8.decode s.toUTF8.toUInt8Array.iter) == none

/-- Ill-formed UTF-8, and its decoding with U+FFFD for each maximal subpart. -/
def badUTF8 : List (List UInt8 × String) :=
  -- The example of the Unicode Standard, Table 3-8.
  [([0x61, 0xF1, 0x80, 0x80, 0xE1, 0x80, 0xC2, 0x62, 0x80, 0x63, 0x80, 0xBF, 0x64],
     "a���b�c��d"),
   ([0x80], "�"),
   ([0xC0, 0xAF], "��"),
   ([0xC2], "�"),
   ([0xE0, 0x80, 0x80], "���"),
   ([0xE2, 0x88], "�"),
   ([0xE2, 0x88, 0x61], "�a"),
   ([0xED, 0xA0, 0x80], "���"),
   ([0xF0, 0x80, 0x80, 0x80], "����"),
   ([0xF4, 0x90, 0x80, 0x80], "����"),
   ([0xF5], "�"),
   ([0xFF, 0xFE], "��")]

#guard badUTF8.all fun (b, s) => str (UTF8.decodeLossy b.toUInt8Array.iter) == s
#guard badUTF8.all fun (b, _) => stopError? (UTF8.decode b.toUInt8Array.iter) ==
  some DecodeError.illFormedUTF8
#guard badUTF8.all fun (b, _) => String.fromUTF8? b.toByteArray == none

-- The maximal subpart E2 88 ends before 61.
#guard
  let (cs, it) := run (UTF8.decode [0x61, 0xE2, 0x88, 0x61].toUInt8Array.iter)
  cs == #['a'] && idx8 it.decodeBase == 1

/-! Byte order iterators -/

#guard samples.all fun s =>
  (ByteOrder.encode16 .big (UTF16.encode s.chars)).toList == (utf16BE.encode s).toList
#guard samples.all fun s =>
  (ByteOrder.encode16 .little (UTF16.encode s.chars)).toList == (utf16LE.encode s).toList
#guard samples.all fun s =>
  (ByteOrder.encode32 .big (UTF32.encode s.chars)).toList == (utf32BE.encode s).toList
#guard samples.all fun s =>
  (ByteOrder.encode32 .little (UTF32.encode s.chars)).toList == (utf32LE.encode s).toList
#guard samples.all fun s =>
  str (UTF16.decode (ByteOrder.decode16 .little (utf16LE.encode s).toUInt8Array.iter)) == s
#guard samples.all fun s =>
  str (UTF32.decode (ByteOrder.decode32 .big (utf32BE.encode s).toUInt8Array.iter)) == s

#guard (run (ByteOrder.decode16 .big [0x00, 0x61, 0x00].toUInt8Array.iter)).1 == #[0x61]
#guard stopError? (ByteOrder.decode16 .big [0x00, 0x61, 0x00].toUInt8Array.iter) ==
  some DecodeError.incompleteCodeUnit
#guard (ByteOrder.decode16Lossy .big [0x00, 0x61, 0x00].toUInt8Array.iter).toList ==
  [0x61, 0xFFFD]
#guard (ByteOrder.decode32Lossy .little [0x61, 0, 0, 0, 0x62, 0].toUInt8Array.iter).toList ==
  [0x61, 0xFFFD]
#guard str (UTF16.decodeLossy (ByteOrder.decode16Lossy .big [0xD8, 0x3D, 0x00].toUInt8Array.iter))
  == "��"

/-! Byte order marks -/

#guard
  let (o, it) := ByteOrder.readBOM16 .big [0xFF, 0xFE, 0x61, 0x00].toUInt8Array.iter
  o == .little && str (UTF16.decode (o.decode16 it)) == "a"
#guard
  let (o, it) := ByteOrder.readBOM16 .little [0x00, 0x61].toUInt8Array.iter
  o == .little && idx8 it == 0
#guard
  let (o, it) := ByteOrder.readBOM32 .big [0xFF, 0xFE, 0, 0, 0x61, 0, 0, 0].toUInt8Array.iter
  o == .little && str (UTF32.decode (o.decode32 it)) == "a"
#guard idx8 (UTF8.skipSignature [0xEF, 0xBB, 0xBF, 0x61].toUInt8Array.iter) == 3
#guard idx8 (UTF8.skipSignature [0xEF, 0xBB].toUInt8Array.iter) == 0

/-! Encoder boundaries -/

#guard
  let it := UTF16.encode "😀a".chars
  match it.step with
  | ⟨.yield it' u, _⟩ => u == 0xD83D && !it'.encodeBoundary && it'.encodeBase.toList == ['a']
  | _ => false

/-! Lossy UTF-8 in the encoding schemes follows maximal subparts -/

#guard badUTF8.all fun (b, s) => utf8.decodeLossy b.toByteArray == s
#guard badUTF8.all fun (b, s) => utf8BOM.decodeLossy ([0xEF, 0xBB, 0xBF] ++ b).toByteArray == s
#guard badUTF8.all fun (b, s) => (utf8.transcodeLossy utf16BE b.toByteArray).toList ==
  (utf16BE.encode s).toList
-- Unlike core, which replaces the run `ED A0 80` with a single U+FFFD. When the second test fails,
-- core follows maximal subparts (https://github.com/leanprover/lean4/issues/16145), and
-- `fromUTF8Lossy` in `EncodingScheme` can use it directly.
#guard utf8.decodeLossy [0xED, 0xA0, 0x80].toByteArray == "���"
#guard String.fromUTF8Lossy [0xED, 0xA0, 0x80].toByteArray == "�"
