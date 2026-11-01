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

/-- One decoding step, with the proof that it advances. -/
private inductive Step (it : Iter (α := UInt32Array.SliceIterator) UInt32) where
  | yield (rest : Iter (α := UInt32Array.SliceIterator) UInt32) (h : Advanced rest it) (c : Char)
  | error (kind : DecodeError.Kind) (rest : Iter (α := UInt32Array.SliceIterator) UInt32)
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
    (it : Iter (α := UInt32Array.SliceIterator) UInt32) :
    γ × Option (DecodeError.Kind × Iter (α := UInt32Array.SliceIterator) UInt32) :=
  match (decodeChar it (fun rest h c => .yield rest h c) (fun k rest _ => .error k rest)
      (fun _ => .done) : Step it) with
  | .yield rest _ c => foldUntilError f (f acc c) rest
  | .error k rest => (acc, some (k, rest))
  | .done => (acc, none)
termination_by it.finitelyManySteps
decreasing_by assumption

/-- Decodes the UTF-32 code units of `s`, or returns an error with the index in `s` of the first
code unit that is not a scalar value. -/
public def decode (s : UInt32Array.Slice) : Except DecodeError String :=
  match foldUntilError String.push "" s.iter with
  | (r, none) => .ok r
  | (_, some (k, it)) => .error ⟨k, it.toUInt32Slice.start - 1 - s.start⟩

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
