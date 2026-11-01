/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Iterator.Basic

/-! # UTF-32 iterators

`UTF32.decodeIter` reads characters from UTF-32 code units, and `UTF32.encodeIter` writes them back.
A code unit that is a surrogate or above U+10FFFF is ill-formed.
-/

namespace Unicode
open Std

/-- The UTF-32 encoding form, as a decoder from code units and an encoder to code units. -/
public structure UTF32 where
  deriving Inhabited

namespace UTF32

variable {ι : Type} [Iterator ι Id UInt32] [Iterators.Productive ι Id]

/--
Decodes one character from the UTF-32 code units of `it`. Calls `yield` with the character and the
iterator after it, `error` with the iterator after a code unit that is not a scalar value, or
`done` at the end of the input.
-/
@[inline]
public def decodeChar {β : Type} (it : Iter (α := ι) UInt32)
    (yield : (rest : Iter (α := ι) UInt32) → Advanced rest it → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt32) → Advanced rest it → β)
    (done : Unit → β) : β :=
  nextToken it (fun r h u =>
    if hu : u.isValidChar then yield r h ⟨u, hu⟩ else error .notScalarValue r h) done

public instance : Decoder UTF32 UInt32 Char where
  replacement _ := '\uFFFD'
  decode _ it := decodeChar it

public instance : Encoder UTF32 Char UInt32 where
  length _ _ := 1
  unit _ c _ := c.val

/-- Decodes the UTF-32 code units of `it`, stopping at the first that is not a scalar value. -/
@[inline]
public def decodeIter (it : Iter (α := ι) UInt32) : Iter (α := DecodeIterator UTF32 ι) Char :=
  Decoder.iter {} it

/-- Decodes the UTF-32 code units of `it`, replacing each that is not a scalar value with
U+FFFD. -/
@[inline]
public def decodeIterLossy (it : Iter (α := ι) UInt32) : Iter (α := DecodeIterator UTF32 ι) Char :=
  Decoder.iterLossy {} it

/-- Encodes the characters of `it` as UTF-32 code units. -/
@[inline]
public def encodeIter (it : Iter (α := ι) Char) : Iter (α := EncodeIterator UTF32 ι) UInt32 :=
  Encoder.iter {} it

end UTF32

end Unicode
