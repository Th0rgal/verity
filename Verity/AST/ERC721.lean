/-
  Verity.AST.ERC721: initial AST bridge scaffold.

  This file establishes the AST/denotation seam for ERC721 foundation work.
-/

import Verity.Denote
import Verity.Examples.ERC721

namespace Verity.AST.ERC721

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.ERC721 (balanceOf)

/-- AST for `balanceOf(addr)`: return mapping slot3[addr]. -/
def balanceOfAST : Stmt :=
  .bindUint "x" (.mapping 3 (.varAddr "addr"))
    (.ret (.var "x"))

/-- `balanceOf` AST denotes to the EDSL `balanceOf` function. -/
theorem balanceOf_equiv (addr : Address) :
    denoteUint emptyEnv (fun s => if s == "addr" then addr else 0) balanceOfAST
    = balanceOf addr := by
  rfl

end Verity.AST.ERC721
