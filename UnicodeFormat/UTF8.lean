/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.Conversions
public import UnicodeFormat.Iterator.UTF8

/-!
# UTF-8

The well-formed byte sequences are those of the Unicode Standard, Table 3-7. Encoding, strict
decoding and validation are core's, which are fast. Ill-formed input goes through
`UTF8.decodeIter`: `decode` reports the byte offset of the first maximal subpart of an ill-formed
byte sequence, and `decodeLossy` replaces each maximal subpart with U+FFFD, following the
recommended practice of the Standard, Section 3.9. Core's `String.fromUTF8Lossy` replaces each run
of ill-formed bytes instead, so it can give fewer U+FFFD.
-/

open ScalarArray Std

namespace Unicode.UTF8

/-- The UTF-8 encoding of `s`. -/
public def encode (s : String) : ByteArray := s.toUTF8

/-- Decodes the UTF-8 bytes of `b`, or returns the first maximal subpart of an ill-formed byte
sequence and its byte offset. -/
public def decode (b : ByteArray) : Except DecodeError String :=
  match String.fromUTF8? b with
  | some s => .ok s
  | none =>
    match Decoder.foldUntilError ({} : UTF8) (fun _ _ => ()) () b.toUInt8Array.iter with
    | (_, some (k, it)) => .error ⟨k, it.internalState.xs.start⟩
    -- Unreachable: core and `UTF8.decodeIter` accept the same byte sequences.
    | (_, none) => .error ⟨.illFormedUTF8, b.size⟩

/-- Decodes the UTF-8 bytes of `b`, or returns `none` if `b` is ill-formed. -/
public def decode? (b : ByteArray) : Option String := String.fromUTF8? b

/-- Decodes the UTF-8 bytes of `b`, panicking if `b` is ill-formed. -/
public def decode! (b : ByteArray) : String := String.fromUTF8! b

/-- Decodes the UTF-8 bytes of `b`, replacing each maximal subpart of an ill-formed byte sequence
with U+FFFD. -/
-- Well-formed input takes core's fast path; only ill-formed input goes through the iterator, until
-- core follows maximal subparts too: https://github.com/leanprover/lean4/issues/16145
public def decodeLossy (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => Decoder.foldLossy ({} : UTF8) String.push "" b.toUInt8Array.iter

/-- Whether `b` is well-formed UTF-8. -/
public def validate (b : ByteArray) : Bool := b.validateUTF8

end Unicode.UTF8
