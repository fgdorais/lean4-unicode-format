/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import UnicodeFormat.Iterator.UTF32

/-!
# UTF-32

Each code point is a single code unit. A code unit that is a surrogate in D800–DFFF or above
10FFFF is ill-formed.

Decoding uses the decoder of `UTF32.decodeIter`. `decode` reports the position of the first
ill-formed code unit, as an index in the slice.
-/

open ScalarArray Std

namespace Unicode.UTF32

/-- The UTF-32 code unit of `c`, as a one-element array. -/
public def encodeChar (c : Char) : UInt32Array := UInt32Array.mk #[c.val]

/-- The UTF-32 encoding of `s`. -/
public def encode (s : String) : UInt32Array := (s.chars.map Char.val).toUInt32Array

/-- Decodes the UTF-32 code units of `s`, or returns an error with the index in `s` of the first
code unit that is not a scalar value. -/
public def decode (s : UInt32Array.Slice) : Except DecodeError String :=
  match Decoder.foldUntilError ({} : UTF32) String.push "" s.iter with
  | (r, none) => .ok r
  | (_, some (k, it)) => .error ⟨k, it.toUInt32Slice.start - s.start⟩

/-- Decodes the UTF-32 code units of `s`, or returns `none` if `s` has a code unit that is not a
Unicode scalar value. -/
public def decode? (s : UInt32Array.Slice) : Option String := (decode s).toOption

/-- Decodes the UTF-32 code units of `s`, panicking if `s` has a code unit that is not a Unicode
scalar value. -/
public def decode! (s : UInt32Array.Slice) : String :=
  match decode s with
  | .ok r => r
  | .error _ => panic! "invalid UTF-32 string"

/-- Decodes the UTF-32 code units of `s`, replacing each code unit that is not a Unicode scalar
value with U+FFFD. -/
public def decodeLossy (s : UInt32Array.Slice) : String :=
  Decoder.foldLossy ({} : UTF32) String.push "" s.iter

/-- Whether `s` is well-formed UTF-32, that is, every code unit is a Unicode scalar value. -/
public def validate (s : UInt32Array.Slice) : Bool := s.all (·.isValidChar)

end Unicode.UTF32
