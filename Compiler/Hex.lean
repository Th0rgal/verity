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
  if s.startsWith "0x" then
    let hexPart := s.drop 2
    if hexPart.isEmpty then
      none
    else
      hexPart.data.foldl (fun acc c =>
        match acc, hexCharToNat? c with
        | some n, some d => some (n * 16 + d)
        | _, _ => none
      ) (some 0)
  else
    none  -- Only parse as hex if it has "0x" prefix

def stringToNat (s : String) : Nat :=
  s.data.foldl (fun acc c => acc * 256 + c.toNat) 0

def addressToNat (addr : String) : Nat :=
  match parseHexNat? addr with
  | some n => n
  | none => stringToNat addr % (2^160)

end Compiler.Hex
