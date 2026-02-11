import Std

namespace Compiler.Hex

def hexCharToNat? (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if ('a' ≤ c ∧ c ≤ 'f') then
    some (10 + c.toNat - 'a'.toNat)
  else if ('A' ≤ c ∧ c ≤ 'F') then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

def parseHexNat? (s : String) : Option Nat :=
  let s := if s.startsWith "0x" then s.drop 2 else s
  if s.isEmpty then
    none
  else
    s.data.foldl (fun acc c =>
      match acc, hexCharToNat? c with
      | some n, some d => some (n * 16 + d)
      | _, _ => none
    ) (some 0)

def stringToNat (s : String) : Nat :=
  s.data.foldl (fun acc c => acc * 256 + c.toNat) 0

def addressToNat (addr : String) : Nat :=
  match parseHexNat? addr with
  | some n => n
  | none => stringToNat addr % (2^160)

end Compiler.Hex
