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

Decoding uses the decoder of `UTF16.decodeIter`. `decode` reports the position of the first
unpaired surrogate, as an index in the slice.
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

/-- The UTF-16 code units of `c`: one for a character of the BMP, two for a surrogate pair. -/
public def encodeChar (c : Char) : UInt16Array := push (.emptyWithCapacity 2) c

/-- The UTF-16 encoding of `s`. -/
public def encode (s : String) : UInt16Array :=
  -- A character takes at least as many UTF-8 bytes as UTF-16 code units.
  s.chars.fold push (.emptyWithCapacity s.utf8ByteSize)

/-- One decoding step, with the proof that it advances. -/
private inductive Step (it : Iter (α := UInt16Array.SliceIterator) UInt16) where
  | yield (rest : Iter (α := UInt16Array.SliceIterator) UInt16) (h : Advanced rest it) (c : Char)
  | error (kind : DecodeError.Kind) (rest : Iter (α := UInt16Array.SliceIterator) UInt16)
  | done

/--
Folds `f` over the characters of `it` up to the first ill-formed code unit, and returns the result
with the kind of error and the iterator after that code unit, if any. Unlike
`Decoder.foldUntilError`, which returns the iterator at the ill-formed input, it does not keep the
iterator before each step, so the compiler updates it in place. The ill-formed input is always one
code unit, so the iterator after it tells where it is.
-/
@[specialize]
private def foldUntilError {γ : Type} (f : γ → Char → γ) (acc : γ)
    (it : Iter (α := UInt16Array.SliceIterator) UInt16) :
    γ × Option (DecodeError.Kind × Iter (α := UInt16Array.SliceIterator) UInt16) :=
  match (decodeChar it (fun rest h c => .yield rest h c) (fun k rest _ => .error k rest)
      (fun _ => .done) : Step it) with
  | .yield rest _ c => foldUntilError f (f acc c) rest
  | .error k rest => (acc, some (k, rest))
  | .done => (acc, none)
termination_by it.finitelyManySteps
decreasing_by assumption

/-- Decodes the UTF-16 code units of `s`, or returns an error with the index in `s` of the first
unpaired surrogate. -/
public def decode (s : UInt16Array.Slice) : Except DecodeError String :=
  match foldUntilError String.push "" s.iter with
  | (r, none) => .ok r
  | (_, some (k, it)) => .error ⟨k, it.toUInt16Slice.start - 1 - s.start⟩

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
  (foldUntilError (fun _ _ => ()) () s.iter).2.isNone

end Unicode.UTF16
