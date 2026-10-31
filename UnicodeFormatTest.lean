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
