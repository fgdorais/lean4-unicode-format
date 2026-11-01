/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! # Basic definitions -/

namespace Unicode

/-- The order of the bytes of a code unit wider than a byte. -/
public inductive ByteOrder where
  /-- Big-endian: the most significant byte first. -/
  | big
  /-- Little-endian: the least significant byte first. -/
  | little
  deriving Inhabited, DecidableEq, Repr

end Unicode
