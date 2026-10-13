/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt16

/-!
# UTF-16

A code point below U+10000 is a single code unit. A code point from U+10000 to U+10FFFF is a
surrogate pair: a high surrogate in D800–DBFF carrying the top ten bits of `c - 0x10000`, then a
low surrogate in DC00–DFFF carrying the bottom ten bits. A surrogate that is not part of such a
pair is ill-formed. The names follow core's `String.toUTF8` and `String.fromUTF8?`.
-/

open ScalarArray

namespace String

/-- Appends the UTF-16 encoding of `c`. -/
@[inline] private def pushUTF16 (a : UInt16Array) (c : Char) : UInt16Array :=
  if c.val < 0x10000 then
    a.push c.val.toUInt16
  else
    let v := c.val - 0x10000
    (a.push ((v >>> 10).toUInt16 + 0xD800)).push ((v &&& 0x3FF).toUInt16 + 0xDC00)

/-- The UTF-16 encoding of `s`. -/
public def toUTF16 (s : String) : UInt16Array :=
  -- A character takes at least as many UTF-8 bytes as UTF-16 code units.
  s.chars.fold pushUTF16 (.emptyWithCapacity s.utf8ByteSize)

/-- Decodes UTF-16, running `bad` for each ill-formed code unit. -/
@[specialize] private def decodeUTF16 [Monad m] (s : UInt16Array.Slice) (bad : m Char) : m String := do
  let mut r := ""
  -- The high surrogate waiting for its low surrogate.
  let mut hi : Option UInt16 := none
  for u in s do
    if let some h := hi then
      hi := none
      if u &&& 0xFC00 == 0xDC00 then
        r := r.push (Char.ofNat (0x10000 + (h.toNat &&& 0x3FF) * 0x400 + (u.toNat &&& 0x3FF)))
        continue
      r := r.push (← bad)
    if u &&& 0xFC00 == 0xD800 then
      hi := some u
    else if u &&& 0xFC00 == 0xDC00 then
      r := r.push (← bad)
    else
      r := r.push (Char.ofNat u.toNat)
  if hi.isSome then
    r := r.push (← bad)
  return r

/-- Decodes UTF-16, or returns `none` if `s` has an unpaired surrogate. -/
public def fromUTF16? (s : UInt16Array.Slice) : Option String := decodeUTF16 s none

/-- Decodes UTF-16, panicking if `s` has an unpaired surrogate. -/
public def fromUTF16! (s : UInt16Array.Slice) : String :=
  match fromUTF16? s with
  | some r => r
  | none => panic! "invalid UTF-16 string"

/-- Decodes UTF-16, replacing each unpaired surrogate with U+FFFD. -/
public def fromUTF16Lossy (s : UInt16Array.Slice) : String :=
  Id.run <| decodeUTF16 s (pure '\uFFFD')

/-- Whether `s` is well-formed UTF-16, that is, has no unpaired surrogate. -/
public def validateUTF16 (s : UInt16Array.Slice) : Bool := Id.run do
  -- Whether the previous code unit is a high surrogate.
  let mut hi := false
  for u in s do
    if hi != (u &&& 0xFC00 == 0xDC00) then
      return false
    hi := u &&& 0xFC00 == 0xD800
  return !hi

end String
