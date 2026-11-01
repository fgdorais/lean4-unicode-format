/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Iterator.Basic

/-! # Byte order iterators

The encoding schemes UTF-16BE, UTF-16LE, UTF-32BE and UTF-32LE serialize code units as bytes.
`ByteOrder.decodeIter16` reads UTF-16 code units from bytes and `ByteOrder.encodeIter16` writes
them, and likewise `decodeIter32` and `encodeIter32` for UTF-32. Bytes that end in the middle of a
code unit are ill-formed; lossy decoding replaces that code unit with 0xFFFD, which decodes to
U+FFFD.

The UTF-16 and UTF-32 schemes start with a byte order mark: `ByteOrder.readBOM16` and `readBOM32`
read it, and give the byte order it tells and the iterator after it.
-/

namespace Unicode
open Std

/-- Code units of 2 bytes, in byte order `order`. -/
public structure Bytes16 where
  /-- The byte order. -/
  order : ByteOrder
  deriving Inhabited

/-- Code units of 4 bytes, in byte order `order`. -/
public structure Bytes32 where
  /-- The byte order. -/
  order : ByteOrder
  deriving Inhabited

namespace ByteOrder

/-- The shift that brings byte `i` of a code unit of `n` bytes into the low byte. -/
@[inline]
private def shift (o : ByteOrder) (n i : Nat) : Nat :=
  match o with
  | .big => 8 * (n - 1 - i)
  | .little => 8 * i

/-- Byte `i` of the UTF-16 code unit `u` in byte order `o`. -/
@[inline]
public def byte16 (o : ByteOrder) (u : UInt16) (i : Nat) : UInt8 :=
  (u >>> (o.shift 2 i).toUInt16).toUInt8

/-- Byte `i` of the UTF-32 code unit `u` in byte order `o`. -/
@[inline]
public def byte32 (o : ByteOrder) (u : UInt32) (i : Nat) : UInt8 :=
  (u >>> (o.shift 4 i).toUInt32).toUInt8

section Read

variable {ι : Type} [Iterator ι Id UInt8] [Iterators.Productive ι Id]

/--
Reads one UTF-16 code unit from the bytes of `it` in byte order `o`. Calls `yield` with the code
unit and the iterator after it, `error` with the iterator after an incomplete code unit at the end
of the input, or `done` at the end of the input.
-/
@[inline]
public def readUInt16 {β : Type} (o : ByteOrder) (it : Iter (α := ι) UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest it → UInt16 → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  nextToken it (fun r₁ h₁ b₀ =>
    nextToken r₁
      (fun r₂ h₂ b₁ =>
        yield r₂ (h₂.trans h₁) <| match o with
          | .big => b₀.toUInt16 <<< 8 ||| b₁.toUInt16
          | .little => b₁.toUInt16 <<< 8 ||| b₀.toUInt16)
      (fun _ => error .incompleteCodeUnit r₁ h₁))
    done

/--
Reads one UTF-32 code unit from the bytes of `it` in byte order `o`. Calls `yield` with the code
unit and the iterator after it, `error` with the iterator after an incomplete code unit at the end
of the input, or `done` at the end of the input.
-/
@[inline]
public def readUInt32 {β : Type} (o : ByteOrder) (it : Iter (α := ι) UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest it → UInt32 → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  nextToken it (fun r₁ h₁ b₀ =>
    nextToken r₁ (fun r₂ h₂ b₁ =>
      nextToken r₂ (fun r₃ h₃ b₂ =>
        nextToken r₃
          (fun r₄ h₄ b₃ =>
            yield r₄ (h₄.trans (h₃.trans (h₂.trans h₁))) <| match o with
              | .big =>
                b₀.toUInt32 <<< 24 ||| b₁.toUInt32 <<< 16 ||| b₂.toUInt32 <<< 8 ||| b₃.toUInt32
              | .little =>
                b₃.toUInt32 <<< 24 ||| b₂.toUInt32 <<< 16 ||| b₁.toUInt32 <<< 8 ||| b₀.toUInt32)
          (fun _ => error .incompleteCodeUnit r₃ (h₃.trans (h₂.trans h₁))))
        (fun _ => error .incompleteCodeUnit r₂ (h₂.trans h₁)))
      (fun _ => error .incompleteCodeUnit r₁ h₁))
    done

end Read

end ByteOrder

public instance : Decoder Bytes16 UInt8 UInt16 where
  replacement _ := 0xFFFD
  decode d it := d.order.readUInt16 it

public instance : Decoder Bytes32 UInt8 UInt32 where
  replacement _ := 0xFFFD
  decode d it := d.order.readUInt32 it

public instance : Encoder Bytes16 UInt16 UInt8 where
  length _ _ := 2
  unit d := d.order.byte16

public instance : Encoder Bytes32 UInt32 UInt8 where
  length _ _ := 4
  unit d := d.order.byte32

namespace ByteOrder

variable {ι : Type}

/-- Decodes the bytes of `it` as UTF-16 code units in byte order `o`, stopping at an incomplete
code unit. -/
@[inline]
public def decodeIter16 (o : ByteOrder) (it : Iter (α := ι) UInt8) :
    Iter (α := DecodeIterator Bytes16 ι) UInt16 :=
  Decoder.iter ⟨o⟩ it

/-- Decodes the bytes of `it` as UTF-16 code units in byte order `o`, replacing an incomplete code
unit with 0xFFFD. -/
@[inline]
public def decodeIter16Lossy (o : ByteOrder) (it : Iter (α := ι) UInt8) :
    Iter (α := DecodeIterator Bytes16 ι) UInt16 :=
  Decoder.iterLossy ⟨o⟩ it

/-- Encodes the UTF-16 code units of `it` as bytes in byte order `o`. -/
@[inline]
public def encodeIter16 (o : ByteOrder) (it : Iter (α := ι) UInt16) :
    Iter (α := EncodeIterator Bytes16 ι) UInt8 :=
  Encoder.iter ⟨o⟩ it

/-- Decodes the bytes of `it` as UTF-32 code units in byte order `o`, stopping at an incomplete
code unit. -/
@[inline]
public def decodeIter32 (o : ByteOrder) (it : Iter (α := ι) UInt8) :
    Iter (α := DecodeIterator Bytes32 ι) UInt32 :=
  Decoder.iter ⟨o⟩ it

/-- Decodes the bytes of `it` as UTF-32 code units in byte order `o`, replacing an incomplete code
unit with 0xFFFD. -/
@[inline]
public def decodeIter32Lossy (o : ByteOrder) (it : Iter (α := ι) UInt8) :
    Iter (α := DecodeIterator Bytes32 ι) UInt32 :=
  Decoder.iterLossy ⟨o⟩ it

/-- Encodes the UTF-32 code units of `it` as bytes in byte order `o`. -/
@[inline]
public def encodeIter32 (o : ByteOrder) (it : Iter (α := ι) UInt32) :
    Iter (α := EncodeIterator Bytes32 ι) UInt8 :=
  Encoder.iter ⟨o⟩ it

section BOM

variable [Iterator ι Id UInt8] [Iterators.Productive ι Id]

/-- The byte order given by the UTF-16 byte order mark at `it`, or `o` if there is none, and the
iterator after the mark. -/
public def readBOM16 (o : ByteOrder) (it : Iter (α := ι) UInt8) :
    ByteOrder × Iter (α := ι) UInt8 :=
  nextToken it (fun r₁ _ b₀ =>
    nextToken r₁ (fun r₂ _ b₁ =>
      if b₀ == 0xFE && b₁ == 0xFF then (.big, r₂)
      else if b₀ == 0xFF && b₁ == 0xFE then (.little, r₂)
      else (o, it))
      (fun _ => (o, it)))
    (fun _ => (o, it))

/-- The byte order given by the UTF-32 byte order mark at `it`, or `o` if there is none, and the
iterator after the mark. -/
public def readBOM32 (o : ByteOrder) (it : Iter (α := ι) UInt8) :
    ByteOrder × Iter (α := ι) UInt8 :=
  nextToken it (fun r₁ _ b₀ =>
    nextToken r₁ (fun r₂ _ b₁ =>
      nextToken r₂ (fun r₃ _ b₂ =>
        nextToken r₃ (fun r₄ _ b₃ =>
          if b₀ == 0x00 && b₁ == 0x00 && b₂ == 0xFE && b₃ == 0xFF then (.big, r₄)
          else if b₀ == 0xFF && b₁ == 0xFE && b₂ == 0x00 && b₃ == 0x00 then (.little, r₄)
          else (o, it))
          (fun _ => (o, it)))
        (fun _ => (o, it)))
      (fun _ => (o, it)))
    (fun _ => (o, it))

end BOM

end ByteOrder

end Unicode
