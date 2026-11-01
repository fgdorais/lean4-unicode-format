/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Basic
public import UnicodeFormat.UTF8
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
replaces the incomplete code unit at the end with U+FFFD. Lossy UTF-8 decoding replaces each maximal
subpart of an ill-formed byte sequence with U+FFFD, following the recommended practice of the
Standard, Section 3.9, like `UTF8.decodeLossy`. Core's `String.fromUTF8Lossy` replaces each run of
ill-formed bytes instead, so it can give fewer U+FFFD.

`decode` reports the first ill-formed input with its byte offset, counting the byte order mark or
signature.

`detect?` finds the scheme of bytes that start with a byte order mark or signature, and `name` and
`ofName?` convert to and from the IANA charset names of the schemes.
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
  | utf8 => UTF8.encode s
  | utf8BOM => UTF8.encode ("\uFEFF" ++ s)
  | utf16BE => toBytes16 .big (UTF16.encode s)
  | utf16LE => toBytes16 .little (UTF16.encode s)
  | utf16 o => toBytes16 o (UTF16.encode ("\uFEFF" ++ s))
  | utf32BE => toBytes32 .big (UTF32.encode s)
  | utf32LE => toBytes32 .little (UTF32.encode s)
  | utf32 o => toBytes32 o (UTF32.encode ("\uFEFF" ++ s))

/-- The byte offset in the input of the start of `s`, the bytes after a mark. -/
private def offset (s : UInt8Array.Slice) : Nat := s.start

/-- Decodes the code units of `s` in byte order `o`, or returns the first error, at its byte offset
in the input. -/
private def decode16 (o : ByteOrder) (s : UInt8Array.Slice) : Except DecodeError String :=
  match UTF16.decode ((ofBytes16? o (dropPartial s 2)).getD {}) with
  | .ok r =>
    if s.size % 2 == 0 then .ok r
    else .error ⟨.incompleteCodeUnit, offset s + (s.size - s.size % 2)⟩
  | .error e => .error ⟨e.kind, offset s + 2 * e.pos⟩

/-- Decodes the code units of `s` in byte order `o`, or returns the first error, at its byte offset
in the input. -/
private def decode32 (o : ByteOrder) (s : UInt8Array.Slice) : Except DecodeError String :=
  match UTF32.decode ((ofBytes32? o (dropPartial s 4)).getD {}) with
  | .ok r =>
    if s.size % 4 == 0 then .ok r
    else .error ⟨.incompleteCodeUnit, offset s + (s.size - s.size % 4)⟩
  | .error e => .error ⟨e.kind, offset s + 4 * e.pos⟩

/-- Decodes `b` in the scheme `e`, or returns the first ill-formed input with its byte offset in
`b`. -/
public def decode (e : EncodingScheme) (b : ByteArray) : Except DecodeError String :=
  match e with
  | utf8 => UTF8.decode b
  | utf8BOM =>
    if startsWith b [0xEF, 0xBB, 0xBF] then
      (UTF8.decode (b.extract 3 b.size)).mapError fun e => { e with pos := e.pos + 3 }
    else UTF8.decode b
  | utf16BE => decode16 .big (bytes b)
  | utf16LE => decode16 .little (bytes b)
  | utf16 o => let (o, s) := readBOM16 o b; decode16 o s
  | utf32BE => decode32 .big (bytes b)
  | utf32LE => decode32 .little (bytes b)
  | utf32 o => let (o, s) := readBOM32 o b; decode32 o s

/-- Decodes `b` in the scheme `e`, or returns `none` if `b` is ill-formed. -/
public def decode? (e : EncodingScheme) (b : ByteArray) : Option String := (e.decode b).toOption

/-- Decodes `b` in the scheme `e`, panicking if `b` is ill-formed. -/
public def decode! (e : EncodingScheme) (b : ByteArray) : String :=
  match e.decode b with
  | .ok s => s
  | .error _ => panic! "ill-formed encoded string"

/-- Decodes the code units of `s` in byte order `o` lossily, with U+FFFD for an incomplete code
unit at the end. -/
private def decodeLossy16 (o : ByteOrder) (s : UInt8Array.Slice) : String :=
  UTF16.decodeLossy ((ofBytes16? o (dropPartial s 2)).getD {}) ++ partialUnit s 2

/-- Decodes the code units of `s` in byte order `o` lossily, with U+FFFD for an incomplete code
unit at the end. -/
private def decodeLossy32 (o : ByteOrder) (s : UInt8Array.Slice) : String :=
  UTF32.decodeLossy ((ofBytes32? o (dropPartial s 4)).getD {}) ++ partialUnit s 4

/-- Decodes `b` in the scheme `e`, replacing each ill-formed code unit with U+FFFD, or in UTF-8 each
maximal subpart of an ill-formed byte sequence. -/
public def decodeLossy (e : EncodingScheme) (b : ByteArray) : String :=
  match e with
  | utf8 => UTF8.decodeLossy b
  | utf8BOM => UTF8.decodeLossy (dropSignature b)
  | utf16BE => decodeLossy16 .big (bytes b)
  | utf16LE => decodeLossy16 .little (bytes b)
  | utf16 o => let (o, b) := readBOM16 o b; decodeLossy16 o b
  | utf32BE => decodeLossy32 .big (bytes b)
  | utf32LE => decodeLossy32 .little (bytes b)
  | utf32 o => let (o, b) := readBOM32 o b; decodeLossy32 o b

/-- Whether `b` is well-formed in the scheme `e`. -/
public def validate (e : EncodingScheme) (b : ByteArray) : Bool :=
  match e with
  | utf8 => UTF8.validate b
  | utf8BOM => UTF8.validate (dropSignature b)
  | utf16BE => (ofBytes16? .big (bytes b)).any (UTF16.validate ·)
  | utf16LE => (ofBytes16? .little (bytes b)).any (UTF16.validate ·)
  | utf16 o => let (o, b) := readBOM16 o b; (ofBytes16? o b).any (UTF16.validate ·)
  | utf32BE => (ofBytes32? .big (bytes b)).any (UTF32.validate ·)
  | utf32LE => (ofBytes32? .little (bytes b)).any (UTF32.validate ·)
  | utf32 o => let (o, b) := readBOM32 o b; (ofBytes32? o b).any (UTF32.validate ·)

/-- Converts `b` from the scheme `src` to the scheme `dst`, or returns the first ill-formed input
in `src` with its byte offset in `b`. -/
public def transcode (src dst : EncodingScheme) (b : ByteArray) : Except DecodeError ByteArray :=
  (src.decode b).map dst.encode

/-- Converts `b` from the scheme `src` to the scheme `dst`, or returns `none` if `b` is ill-formed
in `src`. -/
public def transcode? (src dst : EncodingScheme) (b : ByteArray) : Option ByteArray :=
  (src.transcode dst b).toOption

/-- Converts `b` from the scheme `src` to the scheme `dst`, replacing each ill-formed code unit
with U+FFFD, or in UTF-8 each maximal subpart of an ill-formed byte sequence. -/
public def transcodeLossy (src dst : EncodingScheme) (b : ByteArray) : ByteArray :=
  dst.encode (src.decodeLossy b)

/-! Detection and names -/

/--
The scheme given by the byte order mark or UTF-8 signature at the start of `b`, if there is one:
`utf8BOM`, `utf16 o` or `utf32 o`, so decoding `b` in that scheme skips the mark. The bytes
FF FE 00 00 start both UTF-32LE with a byte order mark and UTF-16LE with a byte order mark followed
by U+0000; they are taken as UTF-32LE, as is usual.
-/
public def detect? (b : ByteArray) : Option EncodingScheme :=
  if startsWith b [0xEF, 0xBB, 0xBF] then some utf8BOM
  else if startsWith b [0x00, 0x00, 0xFE, 0xFF] then some (utf32 .big)
  else if startsWith b [0xFF, 0xFE, 0x00, 0x00] then some (utf32 .little)
  else if startsWith b [0xFE, 0xFF] then some (utf16 .big)
  else if startsWith b [0xFF, 0xFE] then some (utf16 .little)
  else none

/--
The IANA charset name of the scheme `e`: `"UTF-8"`, `"UTF-16BE"`, `"UTF-16LE"`, `"UTF-16"`,
`"UTF-32BE"`, `"UTF-32LE"` or `"UTF-32"`. UTF-8 with a signature has no name of its own, and the
names of the UTF-16 and UTF-32 schemes do not tell the byte order of `utf16 o` and `utf32 o`.
-/
public def name (e : EncodingScheme) : String :=
  match e with
  | utf8 | utf8BOM => "UTF-8"
  | utf16BE => "UTF-16BE"
  | utf16LE => "UTF-16LE"
  | utf16 _ => "UTF-16"
  | utf32BE => "UTF-32BE"
  | utf32LE => "UTF-32LE"
  | utf32 _ => "UTF-32"

/--
The scheme with the IANA charset name or alias `s`, ignoring ASCII case: `UTF-8`, `UTF-16BE`,
`UTF-16LE`, `UTF-16`, `UTF-32BE`, `UTF-32LE` and `UTF-32`, and their aliases `csUTF8`,
`csUTF16BE` and so on. `UTF-8` is `utf8`, and `UTF-16` and `UTF-32` are `utf16 .big` and
`utf32 .big`, which read a byte order mark if there is one.

The labels of the WHATWG Encoding Standard are not names here: some of them conflict with IANA
names, such as `utf-16`, which WHATWG takes as UTF-16LE, and WHATWG decoding follows a byte order
mark whatever the label.
-/
public def ofName? (s : String) : Option EncodingScheme :=
  match s.toLower with
  | "utf-8" | "csutf8" => some utf8
  | "utf-16be" | "csutf16be" => some utf16BE
  | "utf-16le" | "csutf16le" => some utf16LE
  | "utf-16" | "csutf16" => some (utf16 .big)
  | "utf-32be" | "csutf32be" => some utf32BE
  | "utf-32le" | "csutf32le" => some utf32LE
  | "utf-32" | "csutf32" => some (utf32 .big)
  | _ => none

end EncodingScheme

end Unicode
