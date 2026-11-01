/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Iterator.Basic

/-! # UTF-8 iterators

`UTF8.decodeIter` reads characters from UTF-8 bytes, and `UTF8.encodeIter` writes them back. The
well-formed byte sequences are those of the Unicode Standard, Table 3-7. Ill-formed input is a
*maximal subpart*: the longest prefix of a well-formed sequence that it starts with, or a single
byte if none. Lossy decoding replaces each maximal subpart with U+FFFD, following the recommended
practice of the Standard, Section 3.9.

`UTF8.skipSignature` skips the bytes EF BB BF that sometimes start UTF-8 data.
-/

namespace Unicode
open Std

/-- The UTF-8 encoding form, as a decoder from bytes and an encoder to bytes. -/
public structure UTF8 where
  deriving Inhabited

namespace UTF8

variable {ι : Type} [Iterator ι Id UInt8] [Iterators.Productive ι Id]

/--
Reads the `n` continuation bytes of a sequence that started at `start`, from `cur` on. The first
must be from `lo` to `hi`, the others from 0x80 to 0xBF. `acc` holds the bits read so far. On a
byte out of range, or at the end of the input, the maximal subpart ends at `cur`.
-/
@[specialize]
private def continuation {β : Type} (start cur : Iter (α := ι) UInt8) (hcur : Advanced cur start)
    (acc : UInt32) (n : Nat) (lo hi : UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest start → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest start → β) : β :=
  match n with
  | 0 => yield cur hcur (Char.ofNat acc.toNat)
  | n + 1 =>
    nextToken cur
      (fun r h b =>
        if lo ≤ b && b ≤ hi then
          continuation start r (h.trans hcur) (acc <<< 6 ||| (b &&& 0x3F).toUInt32) n 0x80 0xBF
            yield error
        else
          error .illFormedUTF8 cur hcur)
      (fun _ => error .illFormedUTF8 cur hcur)

/--
Decodes one character from the UTF-8 bytes of `it`. Calls `yield` with the character and the
iterator after it, `error` with the iterator after a maximal subpart of an ill-formed byte
sequence, or `done` at the end of the input.
-/
@[inline]
public def decodeChar {β : Type} (it : Iter (α := ι) UInt8)
    (yield : (rest : Iter (α := ι) UInt8) → Advanced rest it → Char → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) UInt8) → Advanced rest it → β)
    (done : Unit → β) : β :=
  nextToken it (fun r h b =>
    let c := continuation it r h
    if b < 0x80 then yield r h (Char.ofNat b.toNat)
    else if b < 0xC2 then error .illFormedUTF8 r h
    else if b < 0xE0 then c (b &&& 0x1F).toUInt32 1 0x80 0xBF yield error
    else if b < 0xF0 then
      c (b &&& 0x0F).toUInt32 2 (if b == 0xE0 then 0xA0 else 0x80)
        (if b == 0xED then 0x9F else 0xBF) yield error
    else if b < 0xF5 then
      c (b &&& 0x07).toUInt32 3 (if b == 0xF0 then 0x90 else 0x80)
        (if b == 0xF4 then 0x8F else 0xBF) yield error
    else error .illFormedUTF8 r h)
    done

end UTF8

public instance : Decoder UTF8 UInt8 Char where
  replacement _ := '\uFFFD'
  decode _ it := UTF8.decodeChar it

public instance : Encoder UTF8 Char UInt8 where
  length _ c := c.utf8Size
  unit _ c i :=
    let n := c.utf8Size
    if n = 1 then c.val.toUInt8
    else if i = 0 then ((0xFF00 >>> n.toUInt32) ||| (c.val >>> (6 * (n - 1)).toUInt32)).toUInt8
    else (0x80 ||| ((c.val >>> (6 * (n - 1 - i)).toUInt32) &&& 0x3F)).toUInt8

namespace UTF8

variable {ι : Type}

/-- Decodes the UTF-8 bytes of `it`, stopping at the first ill-formed byte sequence. -/
@[inline]
public def decodeIter (it : Iter (α := ι) UInt8) : Iter (α := DecodeIterator UTF8 ι) Char :=
  Decoder.iter {} it

/-- Decodes the UTF-8 bytes of `it`, replacing each maximal subpart of an ill-formed byte sequence
with U+FFFD. -/
@[inline]
public def decodeIterLossy (it : Iter (α := ι) UInt8) : Iter (α := DecodeIterator UTF8 ι) Char :=
  Decoder.iterLossy {} it

/-- Encodes the characters of `it` as UTF-8 bytes. -/
@[inline]
public def encodeIter (it : Iter (α := ι) Char) : Iter (α := EncodeIterator UTF8 ι) UInt8 :=
  Encoder.iter {} it

variable [Iterator ι Id UInt8] [Iterators.Productive ι Id]

/-- The iterator after the UTF-8 signature EF BB BF at `it`, or `it` if there is none. -/
public def skipSignature (it : Iter (α := ι) UInt8) : Iter (α := ι) UInt8 :=
  nextToken it (fun r₁ _ b₀ =>
    nextToken r₁ (fun r₂ _ b₁ =>
      nextToken r₂ (fun r₃ _ b₂ =>
        if b₀ == 0xEF && b₁ == 0xBB && b₂ == 0xBF then r₃ else it)
        (fun _ => it))
      (fun _ => it))
    (fun _ => it)

end UTF8

end Unicode
