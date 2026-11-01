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
characters and `encodeIter` encodes them back, `ByteOrder.decodeIter16` and its relatives convert
between bytes and code units, and a strict decoder stops at the first
ill-formed input with the error and its position.

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

## Documentation

You can generate documentation locally using `lake build UnicodeFormat:docs` in the `docs` directory.

-----

* The `Lean 4 / Unicode Format` library is copyright © 2026 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
