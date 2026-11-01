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
Calls `k` with the iterator after the first `n + 1` bytes of `it`, or `done` if there are fewer.
Decoding uses it on ill-formed input to step from the start of the sequence again, rather than keep
the iterator at the end of the maximal subpart alive: the compiler then updates the iterator in
place on well-formed input.
-/
@[specialize]
private def skip {β : Type} (it : Iter (α := ι) UInt8) (n : Nat)
    (k : (rest : Iter (α := ι) UInt8) → Advanced rest it → β) (done : Unit → β) : β :=
  match n with
  | 0 => nextToken it (fun r h _ => k r h) done
  | n + 1 => nextToken it (fun r h _ => skip r n (fun r' h' => k r' (h'.trans h)) done) done

/--
Reads one continuation byte at `cur`, which must be from `lo` to `hi`. Calls `k` with the iterator
after it and `acc` with its bits, or `fail` on a byte out of range or at the end of the input, where
the maximal subpart ends at `cur`. Not recursive, so that it is inlined, for each of the at most
three continuation bytes.
-/
@[inline]
private def continuation {β : Type} (start cur : Iter (α := ι) UInt8) (hcur : Advanced cur start)
    (acc : UInt32) (lo hi : UInt8)
    (k : (rest : Iter (α := ι) UInt8) → Advanced rest start → UInt32 → β) (fail : Unit → β) : β :=
  nextToken cur
    (fun r h b =>
      if lo ≤ b && b ≤ hi then k r (h.trans hcur) (acc <<< 6 ||| (b &&& 0x3F).toUInt32)
      else fail ())
    fail

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
  -- On ill-formed input, `skip it n` steps over the maximal subpart of `n + 1` bytes again, so `done`
  -- is unreachable there.
  nextToken it (fun r h b =>
    let c := continuation it
    if b < 0x80 then yield r h (Char.ofNat b.toNat)
    else if b < 0xC2 then skip it 0 (error .illFormedUTF8) done
    else if b < 0xE0 then
      c r h (b &&& 0x1F).toUInt32 0x80 0xBF (fun r h acc => yield r h (Char.ofNat acc.toNat))
        (fun _ => skip it 0 (error .illFormedUTF8) done)
    else if b < 0xF0 then
      c r h (b &&& 0x0F).toUInt32 (if b == 0xE0 then 0xA0 else 0x80)
        (if b == 0xED then 0x9F else 0xBF)
        (fun r h acc => c r h acc 0x80 0xBF (fun r h acc => yield r h (Char.ofNat acc.toNat))
          (fun _ => skip it 1 (error .illFormedUTF8) done))
        (fun _ => skip it 0 (error .illFormedUTF8) done)
    else if b < 0xF5 then
      c r h (b &&& 0x07).toUInt32 (if b == 0xF0 then 0x90 else 0x80)
        (if b == 0xF4 then 0x8F else 0xBF)
        (fun r h acc =>
          c r h acc 0x80 0xBF
            (fun r h acc => c r h acc 0x80 0xBF (fun r h acc => yield r h (Char.ofNat acc.toNat))
              (fun _ => skip it 2 (error .illFormedUTF8) done))
            (fun _ => skip it 1 (error .illFormedUTF8) done))
        (fun _ => skip it 0 (error .illFormedUTF8) done)
    else skip it 0 (error .illFormedUTF8) done)
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

/--
Decodes the UTF-8 bytes of `it`, stopping at the first ill-formed byte sequence.

A `for` loop or fold over the result ends at ill-formed input just as at the end of the input. To
tell them apart, fold with `decodeFold`, which also returns the iterator where decoding stopped, and
check `decodeError?` there, find the first ill-formed input ahead with `decodeFailure?`, or decode
with `decodeIterLossy` instead.
-/
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

section Signature

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

end Signature

end UTF8

end Unicode
