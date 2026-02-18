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

-- Normalize address to lowercase for consistent comparison
def normalizeAddress (addr : String) : String :=
  addr.map Char.toLower

def addressToNat (addr : String) : Nat :=
  match parseHexNat? addr with
  | some n => n % (2^160)
  | none => stringToNat addr % (2^160)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)

/-- Convert a Nat to a zero-padded hex string (e.g. selector → "0x12345678") -/
def natToHex (n : Nat) (digits : Nat := 8) : String :=
  let rec go (val : Nat) (acc : List Char) : List Char :=
    if val = 0 then acc
    else go (val / 16) (hexDigit (val % 16) :: acc)
  let raw := go n []
  let padded := List.replicate (digits - raw.length) '0' ++ raw
  "0x" ++ String.mk padded

end Compiler.Hex
