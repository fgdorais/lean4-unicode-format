/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Basic
public import UnicodeFormat.UTF16
public import UnicodeFormat.UTF32
import ScalarArray.Bytes

/-!
# Encoding schemes

An encoding scheme serializes the code units of an encoding form as bytes (Unicode Standard,
Section 3.10). UTF-16BE and UTF-32BE put the most significant byte of each code unit first,
UTF-16LE and UTF-32LE the least significant byte. In these four schemes, a leading U+FEFF is a
character like any other. The UTF-16 and UTF-32 schemes start with the byte order mark U+FEFF,
which tells the byte order of the rest and is not part of the text. UTF-8 has no byte order, but
its data sometimes starts with U+FEFF as a signature.

A byte sequence whose size is not a multiple of the code unit size is ill-formed: lossy decoding
replaces the incomplete code unit at the end with U+FFFD.
-/

open ScalarArray

namespace Unicode

/-- A Unicode encoding scheme. -/
public inductive EncodingScheme where
  /-- UTF-8, where a leading U+FEFF is a character. -/
  | utf8
  /-- UTF-8 with a signature: encoding writes a leading U+FEFF and decoding skips one. -/
  | utf8BOM
  /-- UTF-16 in big-endian byte order. -/
  | utf16BE
  /-- UTF-16 in little-endian byte order. -/
  | utf16LE
  /--
  UTF-16 with a byte order mark. Encoding writes the mark, then the code units in byte order
  `order`. Decoding follows the mark, or reads in byte order `order` if there is none; the Standard
  calls for big-endian, the default.
  -/
  | utf16 (order : ByteOrder := .big)
  /-- UTF-32 in big-endian byte order. -/
  | utf32BE
  /-- UTF-32 in little-endian byte order. -/
  | utf32LE
  /--
  UTF-32 with a byte order mark. Encoding writes the mark, then the code units in byte order
  `order`. Decoding follows the mark, or reads in byte order `order` if there is none; the Standard
  calls for big-endian, the default.
  -/
  | utf32 (order : ByteOrder := .big)
  deriving Inhabited, DecidableEq, Repr

namespace EncodingScheme

/-! Code units and bytes -/

/-- The bytes of the UTF-16 code units `a` in byte order `o`. -/
private def toBytes16 (o : ByteOrder) (a : UInt16Array) : ByteArray :=
  match o with
  | .big => a.toBytesBE
  | .little => a.toBytesLE

/-- The bytes of the UTF-32 code units `a` in byte order `o`. -/
private def toBytes32 (o : ByteOrder) (a : UInt32Array) : ByteArray :=
  match o with
  | .big => a.toBytesBE
  | .little => a.toBytesLE

/-- All the bytes of `b`, without copying. -/
private def bytes (b : ByteArray) : UInt8Array.Slice := b.toUInt8Array

/-- The UTF-16 code units of `s` in byte order `o`, or `none` if `s` has an odd size. -/
private def ofBytes16? (o : ByteOrder) (s : UInt8Array.Slice) : Option UInt16Array :=
  match o with
  | .big => UInt16Array.Slice.ofBytesBE? s
  | .little => UInt16Array.Slice.ofBytesLE? s

/-- The UTF-32 code units of `s` in byte order `o`, or `none` if the size of `s` is not a multiple
of 4. -/
private def ofBytes32? (o : ByteOrder) (s : UInt8Array.Slice) : Option UInt32Array :=
  match o with
  | .big => UInt32Array.Slice.ofBytesBE? s
  | .little => UInt32Array.Slice.ofBytesLE? s

/-- `s` without the incomplete code unit of size `n` at its end, if there is one. -/
private def dropPartial (s : UInt8Array.Slice) (n : Nat) : UInt8Array.Slice :=
  s.array.toSlice s.start (s.stop - s.size % n)

/-- U+FFFD if `s` ends with an incomplete code unit of size `n`. -/
private def partialUnit (s : UInt8Array.Slice) (n : Nat) : String :=
  if s.size % n == 0 then "" else "\uFFFD"

/-! Byte order marks -/

/-- Whether `b` starts with the bytes `m`. -/
private def startsWith (b : ByteArray) (m : List UInt8) : Bool :=
  m.length ≤ b.size && m.zipIdx.all fun (x, i) => b[i]! == x

/-- The byte order given by the UTF-16 byte order mark of `b`, or `o` if there is none, and the
bytes after the mark. -/
private def readBOM16 (o : ByteOrder) (b : ByteArray) : ByteOrder × UInt8Array.Slice :=
  if startsWith b [0xFE, 0xFF] then (.big, b.toUInt8Array[2...*])
  else if startsWith b [0xFF, 0xFE] then (.little, b.toUInt8Array[2...*])
  else (o, bytes b)

/-- The byte order given by the UTF-32 byte order mark of `b`, or `o` if there is none, and the
bytes after the mark. -/
private def readBOM32 (o : ByteOrder) (b : ByteArray) : ByteOrder × UInt8Array.Slice :=
  if startsWith b [0x00, 0x00, 0xFE, 0xFF] then (.big, b.toUInt8Array[4...*])
  else if startsWith b [0xFF, 0xFE, 0x00, 0x00] then (.little, b.toUInt8Array[4...*])
  else (o, bytes b)

/-- `b` without its UTF-8 signature, if it has one. -/
-- Copies, since core's UTF-8 decoders only read a whole `ByteArray`.
private def dropSignature (b : ByteArray) : ByteArray :=
  if startsWith b [0xEF, 0xBB, 0xBF] then b.extract 3 b.size else b

/-! Encoding and decoding -/

/-- The encoding of `s` in the scheme `e`. -/
public def encode (e : EncodingScheme) (s : String) : ByteArray :=
  match e with
  | utf8 => s.toUTF8
  | utf8BOM => ("\uFEFF" ++ s).toUTF8
  | utf16BE => toBytes16 .big (toUTF16 s)
  | utf16LE => toBytes16 .little (toUTF16 s)
  | utf16 o => toBytes16 o (toUTF16 ("\uFEFF" ++ s))
  | utf32BE => toBytes32 .big (toUTF32 s)
  | utf32LE => toBytes32 .little (toUTF32 s)
  | utf32 o => toBytes32 o (toUTF32 ("\uFEFF" ++ s))

/-- Decodes `b` in the scheme `e`, or returns `none` if `b` is ill-formed. -/
public def decode? (e : EncodingScheme) (b : ByteArray) : Option String :=
  match e with
  | utf8 => String.fromUTF8? b
  | utf8BOM => String.fromUTF8? (dropSignature b)
  | utf16BE => ofBytes16? .big (bytes b) >>= (fromUTF16? ·)
  | utf16LE => ofBytes16? .little (bytes b) >>= (fromUTF16? ·)
  | utf16 o => let (o, b) := readBOM16 o b; ofBytes16? o b >>= (fromUTF16? ·)
  | utf32BE => ofBytes32? .big (bytes b) >>= (fromUTF32? ·)
  | utf32LE => ofBytes32? .little (bytes b) >>= (fromUTF32? ·)
  | utf32 o => let (o, b) := readBOM32 o b; ofBytes32? o b >>= (fromUTF32? ·)

/-- Decodes `b` in the scheme `e`, panicking if `b` is ill-formed. -/
public def decode! (e : EncodingScheme) (b : ByteArray) : String :=
  match e.decode? b with
  | some s => s
  | none => panic! "ill-formed encoded string"

/-- Decodes the code units of `s` in byte order `o` lossily, with U+FFFD for an incomplete code
unit at the end. -/
private def decodeLossy16 (o : ByteOrder) (s : UInt8Array.Slice) : String :=
  fromUTF16Lossy ((ofBytes16? o (dropPartial s 2)).getD {}) ++ partialUnit s 2

/-- Decodes the code units of `s` in byte order `o` lossily, with U+FFFD for an incomplete code
unit at the end. -/
private def decodeLossy32 (o : ByteOrder) (s : UInt8Array.Slice) : String :=
  fromUTF32Lossy ((ofBytes32? o (dropPartial s 4)).getD {}) ++ partialUnit s 4

/-- Decodes `b` in the scheme `e`, replacing each ill-formed code unit with U+FFFD. -/
public def decodeLossy (e : EncodingScheme) (b : ByteArray) : String :=
  match e with
  | utf8 => String.fromUTF8Lossy b
  | utf8BOM => String.fromUTF8Lossy (dropSignature b)
  | utf16BE => decodeLossy16 .big (bytes b)
  | utf16LE => decodeLossy16 .little (bytes b)
  | utf16 o => let (o, b) := readBOM16 o b; decodeLossy16 o b
  | utf32BE => decodeLossy32 .big (bytes b)
  | utf32LE => decodeLossy32 .little (bytes b)
  | utf32 o => let (o, b) := readBOM32 o b; decodeLossy32 o b

/-- Whether `b` is well-formed in the scheme `e`. -/
public def validate (e : EncodingScheme) (b : ByteArray) : Bool :=
  match e with
  | utf8 => b.validateUTF8
  | utf8BOM => (dropSignature b).validateUTF8
  | utf16BE => (ofBytes16? .big (bytes b)).any (validateUTF16 ·)
  | utf16LE => (ofBytes16? .little (bytes b)).any (validateUTF16 ·)
  | utf16 o => let (o, b) := readBOM16 o b; (ofBytes16? o b).any (validateUTF16 ·)
  | utf32BE => (ofBytes32? .big (bytes b)).any (validateUTF32 ·)
  | utf32LE => (ofBytes32? .little (bytes b)).any (validateUTF32 ·)
  | utf32 o => let (o, b) := readBOM32 o b; (ofBytes32? o b).any (validateUTF32 ·)

/-- Converts `b` from the scheme `src` to the scheme `dst`, or returns `none` if `b` is ill-formed
in `src`. -/
public def transcode? (src dst : EncodingScheme) (b : ByteArray) : Option ByteArray :=
  (src.decode? b).map dst.encode

/-- Converts `b` from the scheme `src` to the scheme `dst`, replacing each ill-formed code unit
with U+FFFD. -/
public def transcodeLossy (src dst : EncodingScheme) (b : ByteArray) : ByteArray :=
  dst.encode (src.decodeLossy b)

end EncodingScheme

end Unicode
