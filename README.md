# Lean 4 / UTF

UTF-16 and UTF-32 encoding and decoding of Lean strings, stored in the unboxed `UInt16Array` and
`UInt32Array` of [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Decoding
is either strict, failing on ill-formed input, or lossy, replacing it with U+FFFD.
