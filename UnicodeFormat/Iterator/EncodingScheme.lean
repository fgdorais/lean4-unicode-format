/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.EncodingScheme
public import UnicodeFormat.Iterator.Bytes

/-! # Encoding scheme iterators

An encoding scheme is a decoder from bytes to characters and an encoder from characters to bytes,
in one layer. `EncodingScheme.decodeIter e` reads the byte order mark or signature of `e`, if it
has one, then decodes the characters after it; `EncodingScheme.encodeIter e` writes the mark, then
the characters. Positions are byte offsets in the input, `it.decodeBase.toUInt8Slice.start` for a
byte slice, and ill-formed input of every kind is reported by the one decoder: an incomplete code
unit at the end as well as an unpaired surrogate or a code unit that is not a scalar value.

As a decoder, `e` decodes the characters after the mark: `utf8BOM` decodes as `utf8`, and
`utf16 o` and `utf32 o` decode in byte order `o`. `decodeIter` gives `utf16 o` and `utf32 o` the
byte order that the mark tells.
-/

namespace Unicode
open Std

namespace EncodingScheme

section Decode

variable {ι : Type} [Iterator ι Id UInt8] [Iterators.Productive ι Id]

/--
Calls `error` with the iterator after the unpaired high surrogate at `it`. It reads `it` again
rather than reuse the iterator after the surrogate, which keeps that iterator out of the path that
decodes a surrogate pair, where the compiler then updates it in place.
-/
@[inline]
private def unpaired {β : Type} (o : ByteOrder) (it : Iter (α := ι) UInt8)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  ByteOrder.readUInt16 o it (fun r h _ => error .unpairedSurrogate r h) error done

/-- Decodes one character from the UTF-16 code units in byte order `o` at `it`. -/
@[inline]
private def decodeChar16 {β : Type} (o : ByteOrder) (it : Iter (α := ι) UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest it → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  ByteOrder.readUInt16 o it
    (fun r₁ h₁ u =>
      if u &&& 0xFC00 == 0xD800 then
        ByteOrder.readUInt16 o r₁
          (fun r₂ h₂ v =>
            if v &&& 0xFC00 == 0xDC00 then
              yield r₂ (h₂.trans h₁)
                (Char.ofNat (0x10000 + (u.toNat &&& 0x3FF) * 0x400 + (v.toNat &&& 0x3FF)))
            else unpaired o it error done)
          (fun _ _ _ => unpaired o it error done)
          (fun _ => unpaired o it error done)
      else if u &&& 0xFC00 == 0xDC00 then error .unpairedSurrogate r₁ h₁
      else yield r₁ h₁ (Char.ofNat u.toNat))
    error done

/-- Decodes one character from the UTF-32 code units in byte order `o` at `it`. -/
@[inline]
private def decodeChar32 {β : Type} (o : ByteOrder) (it : Iter (α := ι) UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest it → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  ByteOrder.readUInt32 o it
    (fun r h u =>
      if hu : u.toNat.isValidChar then yield r h ⟨u, by simpa [UInt32.isValidChar] using hu⟩
      else error .notScalarValue r h)
    error done

/--
Decodes one character from the bytes of `it` in scheme `e`, after any byte order mark or signature.
Calls `yield` with the character and the iterator after it, `error` with the iterator after the
ill-formed input, or `done` at the end of the input.
-/
@[inline]
public def decodeChar {β : Type} (e : EncodingScheme) (it : Iter (α := ι) UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest it → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  match e with
  | utf8 | utf8BOM => UTF8.decodeChar it yield error done
  | utf16BE => decodeChar16 .big it yield error done
  | utf16LE => decodeChar16 .little it yield error done
  | utf16 o => decodeChar16 o it yield error done
  | utf32BE => decodeChar32 .big it yield error done
  | utf32LE => decodeChar32 .little it yield error done
  | utf32 o => decodeChar32 o it yield error done

end Decode

end EncodingScheme

public instance : Decoder EncodingScheme UInt8 Char where
  replacement _ := '\uFFFD'
  decode e it := EncodingScheme.decodeChar e it

public instance : Encoder EncodingScheme Char UInt8 where
  length e c := match e with
    | .utf8 | .utf8BOM => c.utf8Size
    | .utf16BE | .utf16LE | .utf16 _ => if c.val < 0x10000 then 2 else 4
    | .utf32BE | .utf32LE | .utf32 _ => 4
  unit e c i :=
    let u16 o :=
      let j := i.toUInt32
      o.byte16 (Encoder.unit ({} : UTF16) c (j >>> 1).toNat) (j &&& 1).toNat
    match e with
    | .utf8 | .utf8BOM => Encoder.unit ({} : UTF8) c i
    | .utf16BE => u16 .big
    | .utf16LE => u16 .little
    | .utf16 o => u16 o
    | .utf32BE => ByteOrder.big.byte32 c.val i
    | .utf32LE => ByteOrder.little.byte32 c.val i
    | .utf32 o => o.byte32 c.val i

namespace EncodingScheme

section Iterators

variable {ι : Type} [Iterator ι Id UInt8] [Iterators.Productive ι Id]

/-- The scheme to decode the bytes after the mark at `it` with, and the iterator after the mark. -/
private def start (e : EncodingScheme) (it : Iter (α := ι) UInt8) :
    EncodingScheme × Iter (α := ι) UInt8 :=
  match e with
  | utf8BOM => (utf8BOM, UTF8.skipSignature it)
  | utf16 o => let (o, it) := ByteOrder.readBOM16 o it; (utf16 o, it)
  | utf32 o => let (o, it) := ByteOrder.readBOM32 o it; (utf32 o, it)
  | e => (e, it)

/--
Decodes the bytes of `it` in scheme `e`, stopping at the first ill-formed input. A byte order mark
or signature of `e` at the start is skipped, and for `utf16 o` and `utf32 o` the mark tells the byte
order; without one, the byte order is `o`.

A `for` loop or fold over the result ends at ill-formed input just as at the end of the input. To
tell them apart, fold with `decodeFold`, which also returns the iterator where decoding stopped, and
check `decodeError?` there, find the first ill-formed input ahead with `decodeFailure?`, or decode
with `decodeIterLossy` instead.
-/
public def decodeIter (e : EncodingScheme) (it : Iter (α := ι) UInt8) :
    Iter (α := DecodeIterator EncodingScheme ι) Char :=
  let (e, it) := e.start it
  Decoder.iter e it

/-- Decodes the bytes of `it` in scheme `e` like `decodeIter`, replacing each ill-formed input
with U+FFFD. -/
public def decodeIterLossy (e : EncodingScheme) (it : Iter (α := ι) UInt8) :
    Iter (α := DecodeIterator EncodingScheme ι) Char :=
  let (e, it) := e.start it
  Decoder.iterLossy e it

end Iterators

/-- Whether `e` starts with a byte order mark or signature. -/
private def hasMark : EncodingScheme → Bool
  | utf8BOM | utf16 _ | utf32 _ => true
  | _ => false

/-- Encodes the characters of `it` as bytes in scheme `e`, starting with the byte order mark or
signature of `e` if it has one. -/
@[inline]
public def encodeIter {ι : Type} (e : EncodingScheme) (it : Iter (α := ι) Char) :
    Iter (α := EncodeIterator EncodingScheme ι) UInt8 :=
  -- The mark is the pending encoding of U+FEFF.
  ⟨⟨e, it, '\uFEFF', 0, if e.hasMark then Encoder.length e '\uFEFF' else 0⟩⟩

end EncodingScheme

end Unicode
