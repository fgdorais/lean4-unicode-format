/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32

/-!
# UTF-32

Each code point is a single code unit. A code unit that is a surrogate in D800–DFFF or above
10FFFF is ill-formed. The names follow core's `String.toUTF8` and `String.fromUTF8?`.
-/

open ScalarArray

namespace String

/-- The UTF-32 encoding of `s`. -/
public def toUTF32 (s : String) : UInt32Array := (s.chars.map Char.val).toUInt32Array

/-- Decodes UTF-32, running `bad` for each ill-formed code unit. -/
@[specialize] private def decodeUTF32 [Monad m] (s : UInt32Array.Slice) (bad : m Char) : m String := do
  let mut r := ""
  for u in s do
    r := r.push (← if h : u.isValidChar then pure ⟨u, h⟩ else bad)
  return r

/-- Decodes UTF-32, or returns `none` if `s` has a code unit that is not a Unicode scalar value. -/
public def fromUTF32? (s : UInt32Array.Slice) : Option String := decodeUTF32 s none

/-- Decodes UTF-32, panicking if `s` has a code unit that is not a Unicode scalar value. -/
public def fromUTF32! (s : UInt32Array.Slice) : String :=
  match fromUTF32? s with
  | some r => r
  | none => panic! "invalid UTF-32 string"

/-- Decodes UTF-32, replacing each code unit that is not a Unicode scalar value with U+FFFD. -/
public def fromUTF32Lossy (s : UInt32Array.Slice) : String :=
  Id.run <| decodeUTF32 s (pure '�')

/-- Whether `s` is well-formed UTF-32, that is, every code unit is a Unicode scalar value. -/
public def validateUTF32 (s : UInt32Array.Slice) : Bool := s.all (·.isValidChar)

end String
