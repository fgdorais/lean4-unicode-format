/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Iterator.Basic

/-! # UTF-16 iterators

`UTF16.decodeIter` reads characters from UTF-16 code units, and `UTF16.encodeIter` writes them
back. An unpaired surrogate is ill-formed. A high surrogate reads its low surrogate by looking
ahead; when there is none, only the high surrogate is ill-formed, and lossy decoding goes on from
the next code unit.
-/

namespace Unicode
open Std

/-- The UTF-16 encoding form, as a decoder from code units and an encoder to code units. -/
public structure UTF16 where
  deriving Inhabited

namespace UTF16

variable {ι : Type} [Iterator ι Id UInt16] [Iterators.Productive ι Id]

/-- Whether `u` is a high surrogate, the first code unit of a pair. -/
@[inline] private def isHigh (u : UInt16) : Bool := u &&& 0xFC00 == 0xD800

/-- Whether `u` is a low surrogate, the second code unit of a pair. -/
@[inline] private def isLow (u : UInt16) : Bool := u &&& 0xFC00 == 0xDC00

/--
Calls `error` with the iterator after the unpaired high surrogate at `it`. It steps `it` again rather
than reuse the iterator after the surrogate, which keeps that iterator out of the path that decodes a
surrogate pair, where the compiler then updates it in place.
-/
@[inline]
private def unpaired {β : Type} (it : Iter (α := ι) UInt16)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt16) → Advanced rest it → β)
    (done : Unit → β) : β :=
  nextToken it (fun r h _ => error .unpairedSurrogate r h) done

/--
Decodes one character from the UTF-16 code units of `it`. Calls `yield` with the character and the
iterator after it, `error` with the iterator after an unpaired surrogate, or `done` at the end of
the input.
-/
@[inline]
public def decodeChar {β : Type} (it : Iter (α := ι) UInt16)
    (yield : (rest : Iter (α := ι) UInt16) → Advanced rest it → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt16) → Advanced rest it → β)
    (done : Unit → β) : β :=
  nextToken it (fun r₁ h₁ u =>
    if isHigh u then
      nextToken r₁
        (fun r₂ h₂ v =>
          if isLow v then
            yield r₂ (h₂.trans h₁)
              (Char.ofNat (0x10000 + (u.toNat &&& 0x3FF) * 0x400 + (v.toNat &&& 0x3FF)))
          else
            unpaired it error done)
        (fun _ => unpaired it error done)
    else if isLow u then
      error .unpairedSurrogate r₁ h₁
    else
      yield r₁ h₁ (Char.ofNat u.toNat))
    done

public instance : Decoder UTF16 UInt16 Char where
  replacement _ := '\uFFFD'
  decode _ it := decodeChar it

public instance : Encoder UTF16 Char UInt16 where
  length _ c := if c.val < 0x10000 then 1 else 2
  unit _ c i :=
    if c.val < 0x10000 then c.val.toUInt16
    else if i = 0 then ((c.val - 0x10000) >>> 10).toUInt16 + 0xD800
    else ((c.val - 0x10000) &&& 0x3FF).toUInt16 + 0xDC00

/--
Decodes the UTF-16 code units of `it`, stopping at the first unpaired surrogate.

A `for` loop or fold over the result ends at ill-formed input just as at the end of the input. To
tell them apart, check `it.decodeError?` on the iterator where decoding stopped, find the first
ill-formed input ahead with `it.decodeFailure?`, or decode with `decodeIterLossy` instead.
-/
@[inline]
public def decodeIter (it : Iter (α := ι) UInt16) : Iter (α := DecodeIterator UTF16 ι) Char :=
  Decoder.iter {} it

/-- Decodes the UTF-16 code units of `it`, replacing each unpaired surrogate with U+FFFD. -/
@[inline]
public def decodeIterLossy (it : Iter (α := ι) UInt16) : Iter (α := DecodeIterator UTF16 ι) Char :=
  Decoder.iterLossy {} it

/-- Encodes the characters of `it` as UTF-16 code units. -/
@[inline]
public def encodeIter (it : Iter (α := ι) Char) : Iter (α := EncodeIterator UTF16 ι) UInt16 :=
  Encoder.iter {} it

end UTF16

end Unicode
