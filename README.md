# Lean 4 / Unicode Format

UTF-8, UTF-16 and UTF-32 encoding and decoding of Lean strings, with the code units of UTF-16 and
UTF-32 stored in the unboxed `UInt16Array` and `UInt32Array` of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). `Unicode.UTF8`,
`Unicode.UTF16` and `Unicode.UTF32` each provide `encode`, `decode`, `decode?`, `decode!`,
`decodeLossy` and `validate`. Decoding is either strict, failing on ill-formed input with its
position, or lossy, replacing it with U+FFFD.

The Unicode encoding schemes serialize these as bytes: UTF-8, UTF-16BE, UTF-16LE, UTF-32BE and
UTF-32LE, the UTF-16 and UTF-32 schemes with a byte order mark, and UTF-8 with a signature.
`Unicode.EncodingScheme` encodes, decodes, validates and converts between them, detects a scheme
from its byte order mark, and converts to and from IANA charset names.

The same conversions are also iterator transformers over pure `Std.Iter` iterators, for streaming
and parsing: `UTF8.decodeIter`, `UTF16.decodeIter` and `UTF32.decodeIter` decode code units to
characters and `encodeIter` encodes them back, `EncodingScheme.decodeIter` and `encodeIter` do the
same for the bytes of an encoding scheme, including its byte order mark, and a strict decoder stops
at the first ill-formed input with the error and its position.

## The Lean4 / Unicode family

This library is one of a small family of Lean 4 Unicode libraries. Each one has a narrow job, so
you only depend on what you need.

| Library | What it is for |
| --- | --- |
| [UnicodeBasic](https://github.com/fgdorais/lean4-unicode-basic) | The foundation. Fast lookups of commonly used character properties such as general category, case mappings, numeric values, scripts and names, from compact precompiled tables. Start here. |
| [UnicodeData](https://github.com/fgdorais/lean4-unicode-data) | Direct access to the Unicode Character Database files themselves, such as `UnicodeData.txt`, `PropList.txt`, `CaseFolding.txt` and `SpecialCasing.txt`. Heavier than UnicodeBasic, but complete, and handy for properties UnicodeBasic does not cover or for checking it against the source. |
| **UnicodeFormat** (this library) | Encoding and decoding: UTF-8, UTF-16 and UTF-32, the byte-level encoding schemes with byte order marks, strict and lossy decoding, and streaming iterators. |
| [UnicodeLemmas](https://github.com/fgdorais/lean4-unicode-lemmas) | Proofs about UnicodeBasic properties, such as the fact that every cased character is alphabetic. |
| [UnicodeExtra](https://github.com/fgdorais/lean4-unicode-extra) | Unicode algorithms on whole strings that are too large or too specialized for UnicodeBasic, built on top of it. |

## Installation

Add the following dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "UnicodeFormat"
git = "https://github.com/fgdorais/lean4-unicode-format.git"
rev = "main" # or any specific revision
```

Or this dependency to your project's `lakefile.lean`:

```lean4
require UnicodeFormat from git
  "https://github.com/fgdorais/lean4-unicode-format.git" @ "main"
```

## Usage

```lean4
import UnicodeFormat

open Unicode

-- The UTF-16 code units of a string, and back.
#eval (UTF16.encode "a😀").toList        -- [97, 55357, 56832]
#eval UTF16.decode? (UTF16.encode "a😀") -- some "a😀"

-- Ill-formed input is reported with its position, here in bytes.
#eval EncodingScheme.utf16LE.decode [0x61, 0x00, 0x3D, 0xD8, 0x62, 0x00].toByteArray
-- Except.error { kind := Unicode.DecodeError.Kind.unpairedSurrogate, pos := 2 }

-- Lossy decoding replaces each maximal subpart of ill-formed UTF-8 with U+FFFD.
#eval UTF8.decodeLossy [0x61, 0xED, 0xA0, 0x80, 0x62].toByteArray -- "a���b"

-- Schemes from byte order marks and from IANA charset names.
#eval EncodingScheme.detect? [0xFF, 0xFE, 0x68, 0x00].toByteArray -- some (utf16 .little)
#eval (EncodingScheme.ofName? "utf-16le").map (·.encode "hi")      -- some [104, 0, 105, 0]

-- Decoding iterators, for streaming and parsing.
#eval (UTF8.decodeIter "añb".toUTF8.toUInt8Array.iter).toList     -- ['a', 'ñ', 'b']
#eval (EncodingScheme.utf16.decodeIter [0xFF, 0xFE, 0x68, 0x00].toUInt8Array.iter).toList -- ['h']
```

## Documentation

The documentation of the latest release is at
[www.dorais.org/lean4-unicode-format/doc](https://www.dorais.org/lean4-unicode-format/doc/). Each
release also has its documentation attached on GitHub.

You can also generate the documentation locally with `lake build UnicodeFormat:docs` in the `docs`
directory.

-----

* The `Lean 4 / Unicode Format` library is copyright © 2026 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
