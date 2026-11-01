/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnicodeFormat

/-! The examples of the README. -/

open Unicode

#guard (UTF16.encode "a😀").toList == [97, 55357, 56832]
#guard UTF16.decode? (UTF16.encode "a😀") == some "a😀"
#guard match EncodingScheme.utf16LE.decode [0x61, 0x00, 0x3D, 0xD8, 0x62, 0x00].toByteArray with
  | .error e => e == ⟨.unpairedSurrogate, 2⟩
  | .ok _ => false
#guard UTF8.decodeLossy [0x61, 0xED, 0xA0, 0x80, 0x62].toByteArray == "a\uFFFD\uFFFD\uFFFDb"
#guard EncodingScheme.detect? [0xFF, 0xFE, 0x68, 0x00].toByteArray == some (.utf16 .little)
#guard ((EncodingScheme.ofName? "utf-16le").map (·.encode "hi")).map ByteArray.toList ==
  some [104, 0, 105, 0]
#guard (UTF8.decodeIter "añb".toUTF8.toUInt8Array.iter).toList == ['a', 'ñ', 'b']
