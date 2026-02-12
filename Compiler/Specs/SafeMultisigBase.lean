/-
  Compiler.Specs.SafeMultisigBase (Scaffold)

  Minimal ContractSpec placeholder for the Safe base contract.
  This will be replaced with a faithful spec that mirrors the
  latest Safe base contract from safe-smart-account.
-/

import Compiler.ContractSpec

namespace Compiler.Specs.SafeMultisigBase

open Compiler.ContractSpec

/-- Placeholder Safe Multisig base spec. -/
def safeMultisigBaseSpec : ContractSpec := {
  name := "SafeMultisigBase"
  fields := [
    { name := "owner0", ty := FieldType.address },
    { name := "threshold", ty := FieldType.uint256 }
  ]
  constructor := some {
    params := [
      { name := "initialOwner", ty := ParamType.address },
      { name := "initialThreshold", ty := ParamType.uint256 }
    ]
    body := [
      Stmt.setStorage "owner0" (Expr.constructorArg 0),
      Stmt.setStorage "threshold" (Expr.constructorArg 1)
    ]
  }
  functions := [
    { name := "getThreshold"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "threshold")
      ]
    }
  ]
}

end Compiler.Specs.SafeMultisigBase
