import Compiler.Constants

namespace Compiler.Proofs.YulGeneration

open Compiler.Constants

def selectorWord (selector : Nat) : Nat :=
  (selector % selectorModulus) * (2 ^ selectorShift)

def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    let wordOffset := offset - 4
    if wordOffset % 32 != 0 then
      0
    else
      let idx := wordOffset / 32
      calldata.getD idx 0 % evmModulus

end Compiler.Proofs.YulGeneration
