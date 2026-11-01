/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt16
public import UnicodeFormat.Iterator.UTF16

/-!
# UTF-16

A code point below U+10000 is a single code unit. A code point from U+10000 to U+10FFFF is a
surrogate pair: a high surrogate in D800–DBFF carrying the top ten bits of `c - 0x10000`, then a
low surrogate in DC00–DFFF carrying the bottom ten bits. A surrogate that is not part of such a
pair is ill-formed.

Decoding goes through `UTF16.decodeIter`; `decode` reports the position of the first unpaired
surrogate, as an index in the slice.
-/

open ScalarArray Std

namespace Unicode.UTF16

/-- Appends the UTF-16 encoding of `c`. -/
@[inline] private def push (a : UInt16Array) (c : Char) : UInt16Array :=
  if c.val < 0x10000 then
    a.push c.val.toUInt16
  else
    let v := c.val - 0x10000
    (a.push ((v >>> 10).toUInt16 + 0xD800)).push ((v &&& 0x3FF).toUInt16 + 0xDC00)

/-- The UTF-16 encoding of `s`. -/
public def encode (s : String) : UInt16Array :=
  -- A character takes at least as many UTF-8 bytes as UTF-16 code units.
  s.chars.fold push (.emptyWithCapacity s.utf8ByteSize)

/-- Decodes the UTF-16 code units of `s`, or returns the first unpaired surrogate and its index
in `s`. -/
public def decode (s : UInt16Array.Slice) : Except DecodeError String :=
  match Decoder.foldUntilError ({} : UTF16) String.push "" s.iter with
  | (r, none) => .ok r
  | (_, some (k, it)) => .error ⟨k, it.internalState.xs.start - s.start⟩

/-- Decodes the UTF-16 code units of `s`, or returns `none` if `s` has an unpaired surrogate. -/
public def decode? (s : UInt16Array.Slice) : Option String := (decode s).toOption

/-- Decodes the UTF-16 code units of `s`, panicking if `s` has an unpaired surrogate. -/
public def decode! (s : UInt16Array.Slice) : String :=
  match decode s with
  | .ok r => r
  | .error _ => panic! "invalid UTF-16 string"

/-- Decodes the UTF-16 code units of `s`, replacing each unpaired surrogate with U+FFFD. -/
public def decodeLossy (s : UInt16Array.Slice) : String :=
  Decoder.foldLossy ({} : UTF16) String.push "" s.iter

/-- Whether `s` is well-formed UTF-16, that is, has no unpaired surrogate. -/
public def validate (s : UInt16Array.Slice) : Bool :=
  (Decoder.foldUntilError ({} : UTF16) (fun _ _ => ()) () s.iter).2.isNone

end Unicode.UTF16
