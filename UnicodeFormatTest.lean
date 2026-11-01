/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnicodeFormat
import UnicodeFormatTest.Readme

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

#guard (UTF16.encode "").size == 0
#guard (UTF16.encode "abc").toList == [0x61, 0x62, 0x63]
#guard (UTF16.encode "é∀").toList == [0xE9, 0x2200]
#guard (UTF16.encode "😀").toList == [0xD83D, 0xDE00]
#guard (UTF16.encode "𐀀").toList == [0xD800, 0xDC00]
#guard (UTF16.encode (Char.ofNat 0x10FFFF).toString).toList == [0xDBFF, 0xDFFF]
#guard (UTF16.encode "\uFFFF").toList == [0xFFFF]
#guard (UTF16.encode (sampleChars 1)).size == 0x10000 - 0x800 + 2 * 0x100000

/-! UTF-16 round trips -/

#guard samples.all fun s => UTF16.decode? (UTF16.encode s) == some s
#guard samples.all fun s => UTF16.decode! (UTF16.encode s) == s
#guard samples.all fun s => UTF16.decodeLossy (UTF16.encode s) == s
#guard samples.all fun s => UTF16.validate (UTF16.encode s)

/-! UTF-16 slices -/

#guard UTF16.decode? (UTF16.encode "a😀b")[1...3] == some "😀"
#guard UTF16.decode? (UTF16.encode "a😀b")[1...*] == some "😀b"
#guard UTF16.decode? (UTF16.encode "a😀b")[*...2] == none
#guard UTF16.decodeLossy (UTF16.encode "a😀b")[2...*] == "\uFFFDb"

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

#guard badUTF16.all fun (a, _) => UTF16.decode? a.toUInt16Array == none
#guard badUTF16.all fun (a, _) => !UTF16.validate a.toUInt16Array
#guard badUTF16.all fun (a, s) => UTF16.decodeLossy a.toUInt16Array == s
#guard UTF16.validate [0xD83D, 0xDE00, 0x61].toUInt16Array

/-! UTF-32 -/

#guard (UTF32.encode "").size == 0
#guard (UTF32.encode "a😀").toList == [0x61, 0x1F600]
#guard (UTF32.encode (sampleChars 1)).size == 0x110000 - 0x800
#guard samples.all fun s => UTF32.decode? (UTF32.encode s) == some s
#guard samples.all fun s => UTF32.decode! (UTF32.encode s) == s
#guard samples.all fun s => UTF32.decodeLossy (UTF32.encode s) == s
#guard samples.all fun s => UTF32.validate (UTF32.encode s)
#guard samples.all fun s => (UTF32.encode s).size == s.length
#guard UTF32.decode? (UTF32.encode "a😀b")[1...*] == some "😀b"

/-- Code unit sequences with values that are not scalar values, and their lossy decodings. -/
def badUTF32 : List (List UInt32 × String) :=
  [([0xD800], "\uFFFD"),
   ([0xDFFF], "\uFFFD"),
   ([0x110000], "\uFFFD"),
   ([0x61, 0xFFFFFFFF, 0x62], "a\uFFFDb")]

#guard badUTF32.all fun (a, _) => UTF32.decode? a.toUInt32Array == none
#guard badUTF32.all fun (a, _) => !UTF32.validate a.toUInt32Array
#guard badUTF32.all fun (a, s) => UTF32.decodeLossy a.toUInt32Array == s

/-! UTF-16 and UTF-32 agree -/

#guard samples.all fun s => UTF32.decode? (UTF32.encode (UTF16.decode! (UTF16.encode s))) == some s

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
  [(utf8, [0x61, 0xFF], "a\uFFFD"),
   (utf8BOM, [0xEF, 0xBB, 0xBF, 0xFF], "\uFFFD"),
   (utf16BE, [0x00], "\uFFFD"),
   (utf16BE, [0x00, 0x61, 0x00], "a\uFFFD"),
   (utf16BE, [0xD8, 0x3D, 0x00, 0x61], "\uFFFDa"),
   (utf16LE, [0x3D, 0xD8], "\uFFFD"),
   (.utf16, [0xFE, 0xFF, 0xDE, 0x00], "\uFFFD"),
   (.utf16, [0xFF, 0xFE, 0x61], "\uFFFD"),
   (utf32BE, [0x00, 0x00, 0x00], "\uFFFD"),
   (utf32BE, [0x00, 0x00, 0x00, 0x61, 0x00], "a\uFFFD"),
   (utf32BE, [0x00, 0x00, 0xD8, 0x00], "\uFFFD"),
   (utf32LE, [0x00, 0x00, 0x11, 0x00], "\uFFFD"),
   (.utf32 .little, [0xFF, 0xFE, 0x00, 0x00, 0x00, 0xD8, 0x00, 0x00], "\uFFFD")]

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
    (it : Iter (α := DecodeIterator δ ι) σ) : Option DecodeError.Kind :=
  (run it).2.decodeError?

/-- The index in the underlying array of a scalar array slice iterator. -/
def idx16 (it : Iter (α := UInt16Array.SliceIterator) UInt16) : Nat := it.toUInt16Slice.start
def idx8 (it : Iter (α := UInt8Array.SliceIterator) UInt8) : Nat := it.toUInt8Slice.start

/-! UTF-16 iterators -/

#guard samples.all fun s => (UTF16.encodeIter s.chars).toList == (UTF16.encode s).toList
#guard samples.all fun s => str (UTF16.decodeIter (UTF16.encode s).iter) == s
#guard samples.all fun s => str (UTF16.decodeIterLossy (UTF16.encode s).iter) == s
#guard badUTF16.all fun (a, s) => str (UTF16.decodeIterLossy a.toUInt16Array.iter) == s
#guard badUTF16.all fun (a, _) => stopError? (UTF16.decodeIter a.toUInt16Array.iter) ==
  some DecodeError.Kind.unpairedSurrogate
#guard samples.all fun s => stopError? (UTF16.decodeIter (UTF16.encode s).iter) == none

-- A strict decoder stops at the unpaired surrogate, so its base is at the error.
#guard
  let (cs, it) := run (UTF16.decodeIter [0x61, 0xD83D, 0xDE00, 0xD83D, 0x62].toUInt16Array.iter)
  String.ofList cs.toList == "a😀" && idx16 it.decodeBase == 3 &&
    it.decodeError? == some DecodeError.Kind.unpairedSurrogate

/-! UTF-32 iterators -/

#guard samples.all fun s => (UTF32.encodeIter s.chars).toList == (UTF32.encode s).toList
#guard samples.all fun s => str (UTF32.decodeIter (UTF32.encode s).iter) == s
#guard badUTF32.all fun (a, s) => str (UTF32.decodeIterLossy a.toUInt32Array.iter) == s
#guard badUTF32.all fun (a, _) => stopError? (UTF32.decodeIter a.toUInt32Array.iter) ==
  some DecodeError.Kind.notScalarValue

/-! UTF-8 iterators -/

#guard samples.all fun s => (UTF8.encodeIter s.chars).toList == s.toUTF8.toList
#guard samples.all fun s => str (UTF8.decodeIter s.toUTF8.toUInt8Array.iter) == s
#guard samples.all fun s => stopError? (UTF8.decodeIter s.toUTF8.toUInt8Array.iter) == none

/-- Ill-formed UTF-8, and its decoding with U+FFFD for each maximal subpart. -/
def badUTF8 : List (List UInt8 × String) :=
  -- The example of the Unicode Standard, Table 3-8.
  [([0x61, 0xF1, 0x80, 0x80, 0xE1, 0x80, 0xC2, 0x62, 0x80, 0x63, 0x80, 0xBF, 0x64],
     "a\uFFFD\uFFFD\uFFFDb\uFFFDc\uFFFD\uFFFDd"),
   ([0x80], "\uFFFD"),
   ([0xC0, 0xAF], "\uFFFD\uFFFD"),
   ([0xC2], "\uFFFD"),
   ([0xE0, 0x80, 0x80], "\uFFFD\uFFFD\uFFFD"),
   ([0xE2, 0x88], "\uFFFD"),
   ([0xE2, 0x88, 0x61], "\uFFFDa"),
   ([0xED, 0xA0, 0x80], "\uFFFD\uFFFD\uFFFD"),
   ([0xF0, 0x80, 0x80, 0x80], "\uFFFD\uFFFD\uFFFD\uFFFD"),
   ([0xF0, 0x9F, 0x61], "\uFFFDa"),
   ([0xF0, 0x9F, 0x98, 0x61], "\uFFFDa"),
   ([0xF0, 0x9F, 0x98], "\uFFFD"),
   ([0xF0, 0x9F, 0x98, 0xF0, 0x9F, 0x98, 0x80], "\uFFFD😀"),
   ([0xF4, 0x90, 0x80, 0x80], "\uFFFD\uFFFD\uFFFD\uFFFD"),
   ([0xF5], "\uFFFD"),
   ([0xFF, 0xFE], "\uFFFD\uFFFD")]

#guard badUTF8.all fun (b, s) => str (UTF8.decodeIterLossy b.toUInt8Array.iter) == s
#guard badUTF8.all fun (b, _) => stopError? (UTF8.decodeIter b.toUInt8Array.iter) ==
  some DecodeError.Kind.illFormedUTF8
#guard badUTF8.all fun (b, _) => String.fromUTF8? b.toByteArray == none

-- The maximal subpart E2 88 ends before 61.
#guard
  let (cs, it) := run (UTF8.decodeIter [0x61, 0xE2, 0x88, 0x61].toUInt8Array.iter)
  cs == #['a'] && idx8 it.decodeBase == 1

/-! Decoding over an iterator that skips -/

-- `filter` skips, so decoding goes through the loop of `nextToken` over `skip` steps.
#guard str (UTF8.decodeIter ([0x61, 0, 0xC3, 0, 0xA9, 0x62].toUInt8Array.iter.filter (· != 0))) ==
  "aéb"
#guard
  let b := (List.replicate 100000 (0 : UInt8) ++ [0x61]).toUInt8Array
  str (UTF8.decodeIter (b.iter.filter (· != 0))) == "a"

/-! Finding ill-formed input ahead -/

#guard samples.all fun s => (UTF8.decodeIter s.toUTF8.toUInt8Array.iter).decodeFailure?.isNone
#guard
  match (UTF8.decodeIter [0x61, 0xE2, 0x88, 0x61, 0x80].toUInt8Array.iter).decodeFailure? with
  | some (k, it) => k == .illFormedUTF8 && idx8 it.decodeBase == 1 && !it.decodeIsLossy
  | none => false
-- From a lossy iterator, the first ill-formed input ahead, and the iterator there stays lossy.
#guard
  match (UTF16.decodeIterLossy [0x61, 0xD83D, 0xDE00, 0xDE00].toUInt16Array.iter).decodeFailure? with
  | some (k, it) => k == .unpairedSurrogate && idx16 it.decodeBase == 3 && it.decodeIsLossy
  | none => false
-- The failure ahead is where a strict iterator stops.
#guard badUTF16.all fun (a, _) =>
  let it := UTF16.decodeIter a.toUInt16Array.iter
  (it.decodeFailure?.map fun (k, f) => (k, idx16 f.decodeBase)) ==
    some ((run it).2.decodeError?.get!, idx16 (run it).2.decodeBase)

/-! Byte order iterators -/

#guard samples.all fun s =>
  (ByteOrder.encodeIter16 .big (UTF16.encodeIter s.chars)).toList == (utf16BE.encode s).toList
#guard samples.all fun s =>
  (ByteOrder.encodeIter16 .little (UTF16.encodeIter s.chars)).toList == (utf16LE.encode s).toList
#guard samples.all fun s =>
  (ByteOrder.encodeIter32 .big (UTF32.encodeIter s.chars)).toList == (utf32BE.encode s).toList
#guard samples.all fun s =>
  (ByteOrder.encodeIter32 .little (UTF32.encodeIter s.chars)).toList == (utf32LE.encode s).toList
#guard samples.all fun s =>
  str (UTF16.decodeIter (ByteOrder.decodeIter16 .little (utf16LE.encode s).toUInt8Array.iter)) == s
#guard samples.all fun s =>
  str (UTF32.decodeIter (ByteOrder.decodeIter32 .big (utf32BE.encode s).toUInt8Array.iter)) == s

#guard (run (ByteOrder.decodeIter16 .big [0x00, 0x61, 0x00].toUInt8Array.iter)).1 == #[0x61]
#guard stopError? (ByteOrder.decodeIter16 .big [0x00, 0x61, 0x00].toUInt8Array.iter) ==
  some DecodeError.Kind.incompleteCodeUnit
#guard (ByteOrder.decodeIter16Lossy .big [0x00, 0x61, 0x00].toUInt8Array.iter).toList ==
  [0x61, 0xFFFD]
#guard (ByteOrder.decodeIter32Lossy .little [0x61, 0, 0, 0, 0x62, 0].toUInt8Array.iter).toList ==
  [0x61, 0xFFFD]
#guard
  let it := ByteOrder.decodeIter16Lossy .big [0xD8, 0x3D, 0x00].toUInt8Array.iter
  str (UTF16.decodeIterLossy it) == "\uFFFD\uFFFD"

/-! Byte order marks -/

#guard
  let (o, it) := ByteOrder.readBOM16 .big [0xFF, 0xFE, 0x61, 0x00].toUInt8Array.iter
  o == .little && str (UTF16.decodeIter (o.decodeIter16 it)) == "a"
#guard
  let (o, it) := ByteOrder.readBOM16 .little [0x00, 0x61].toUInt8Array.iter
  o == .little && idx8 it == 0
#guard
  let (o, it) := ByteOrder.readBOM32 .big [0xFF, 0xFE, 0, 0, 0x61, 0, 0, 0].toUInt8Array.iter
  o == .little && str (UTF32.decodeIter (o.decodeIter32 it)) == "a"
#guard idx8 (UTF8.skipSignature [0xEF, 0xBB, 0xBF, 0x61].toUInt8Array.iter) == 3
#guard idx8 (UTF8.skipSignature [0xEF, 0xBB].toUInt8Array.iter) == 0

/-! Encoder boundaries -/

#guard
  let it := UTF16.encodeIter "😀a".chars
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
#guard utf8.decodeLossy [0xED, 0xA0, 0x80].toByteArray == "\uFFFD\uFFFD\uFFFD"
#guard String.fromUTF8Lossy [0xED, 0xA0, 0x80].toByteArray == "\uFFFD"

/-! Detection -/

#guard detect? [0xEF, 0xBB, 0xBF, 0x61].toByteArray == some utf8BOM
#guard detect? [0xFE, 0xFF, 0x00, 0x61].toByteArray == some (utf16 .big)
#guard detect? [0xFF, 0xFE, 0x61, 0x00].toByteArray == some (utf16 .little)
#guard detect? [0x00, 0x00, 0xFE, 0xFF].toByteArray == some (utf32 .big)
#guard detect? [0xFF, 0xFE, 0x00, 0x00].toByteArray == some (utf32 .little)
#guard detect? [0x61, 0x62].toByteArray == none
#guard detect? ByteArray.empty == none
-- Decoding in the detected scheme skips the mark, except for UTF-16LE text that starts with U+0000.
#guard schemes.all fun e => samples.all fun s =>
  match e with
  | utf8BOM | .utf16 .big | .utf32 _ =>
    let b := e.encode s
    (detect? b).bind (·.decode? b) == some s
  | .utf16 .little =>
    let b := e.encode s
    s.startsWith "\u0000" || (detect? b).bind (·.decode? b) == some s
  | _ => true
#guard detect? ((utf16 .little).encode "\u0000a") == some (utf32 .little)

/-! Names -/

#guard schemes.all fun e => (ofName? e.name).isSome
#guard schemes.all fun e => (ofName? e.name).map name == some e.name
#guard ofName? "utf-8" == some utf8
#guard ofName? "UTF-16LE" == some utf16LE
#guard ofName? "Utf-16" == some (utf16 .big)
#guard ofName? "csUTF32BE" == some utf32BE
#guard ofName? "UTF8" == none
#guard ofName? "latin1" == none

/-! Error positions -/

/-- The error of a decoding, if any. -/
def err? {α : Type} : Except DecodeError α → Option DecodeError
  | .ok _ => none
  | .error e => some e

#guard err? (UTF16.decode [0x61, 0xD83D, 0x62].toUInt16Array) ==
  some ⟨.unpairedSurrogate, 1⟩
#guard err? (UTF16.decode [0x61, 0xD83D, 0xDE00, 0xDE00].toUInt16Array) ==
  some ⟨.unpairedSurrogate, 3⟩
#guard toString DecodeError.Kind.illFormedUTF8 == "ill-formed UTF-8"
#guard (err? (UTF16.decode [0x61, 0xD83D, 0x62].toUInt16Array)).map toString ==
  some "unpaired surrogate at index 1"
#guard (err? (utf32LE.decode [0x61, 0, 0].toByteArray)).map toString ==
  some "incomplete code unit at index 0"
-- Positions are indices in the slice.
#guard err? (UTF16.decode ([0x61, 0x62, 0xDC00].toUInt16Array[1...*])) ==
  some ⟨.unpairedSurrogate, 1⟩
#guard err? (UTF32.decode [0x61, 0x62, 0x110000].toUInt32Array) == some ⟨.notScalarValue, 2⟩
#guard samples.all fun s => err? (UTF16.decode (UTF16.encode s)) == none
#guard samples.all fun s => err? (UTF32.decode (UTF32.encode s)) == none

/-! UTF-8 -/

#guard samples.all fun s => UTF8.decode? (UTF8.encode s) == some s
#guard samples.all fun s => UTF8.validate (UTF8.encode s)
#guard err? (UTF8.decode [0x61, 0xE2, 0x88, 0x61].toByteArray) == some ⟨.illFormedUTF8, 1⟩
#guard err? (UTF8.decode [0x61, 0x62, 0xFF].toByteArray) == some ⟨.illFormedUTF8, 2⟩
#guard badUTF8.all fun (b, s) => UTF8.decodeLossy b.toByteArray == s
#guard badUTF8.all fun (b, _) => !UTF8.validate b.toByteArray

/-! Encoding scheme error positions, in bytes -/

#guard err? (utf8BOM.decode [0xEF, 0xBB, 0xBF, 0x61, 0xFF].toByteArray) ==
  some ⟨.illFormedUTF8, 4⟩
#guard err? (utf16BE.decode [0x00, 0x61, 0xD8, 0x3D].toByteArray) ==
  some ⟨.unpairedSurrogate, 2⟩
#guard err? (utf16BE.decode [0x00, 0x61, 0x00].toByteArray) == some ⟨.incompleteCodeUnit, 2⟩
-- An unpaired surrogate before an incomplete code unit is the first error.
#guard err? (utf16LE.decode [0x3D, 0xD8, 0x61].toByteArray) == some ⟨.unpairedSurrogate, 0⟩
#guard err? (EncodingScheme.utf16.decode [0xFE, 0xFF, 0x00, 0x61, 0xD8, 0x3D].toByteArray) ==
  some ⟨.unpairedSurrogate, 4⟩
#guard err? ((utf32 .little).decode [0xFF, 0xFE, 0, 0, 0, 0xD8, 0, 0].toByteArray) ==
  some ⟨.notScalarValue, 4⟩
#guard err? (utf32BE.decode [0, 0, 0, 0x61, 0, 0].toByteArray) == some ⟨.incompleteCodeUnit, 4⟩
#guard schemes.all fun e => samples.all fun s => err? (e.decode (e.encode s)) == none
#guard badBytes.all fun (e, b, _) => (err? (e.decode b.toByteArray)).isSome

/-! Transcoding with errors -/

#guard (utf8.transcode utf16BE (UTF8.encode "a😀")).toOption.map ByteArray.toList ==
  some (utf16BE.encode "a😀").toList
#guard err? (utf16LE.transcode utf8 [0x61, 0x00, 0x3D, 0xD8].toByteArray) ==
  some ⟨.unpairedSurrogate, 2⟩
