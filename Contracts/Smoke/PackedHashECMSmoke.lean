import Contracts.Common
import Compiler.Modules.Hashing

namespace Contracts.Smoke

open Verity hiding pure bind

verity_contract PackedHashECMSmoke where
  storage

  function hashAddressAmount (who : Address, amount : Uint256) : Bytes32 := do
    let digest ← ecmCall
      (fun resultVar => Compiler.Modules.Hashing.abiEncodePackedStaticSegmentsModule resultVar [20, 32])
      [addressToWord who, amount]
    return digest

  function hashLowByteAmount (value : Uint256, amount : Uint256) : Bytes32 := do
    let digest ← ecmCall
      (fun resultVar => Compiler.Modules.Hashing.abiEncodePackedStaticSegmentsModule resultVar [1, 32])
      [value, amount]
    return digest

  function sha256AddressAmount (who : Address, amount : Uint256) : Bytes32 := do
    let digest ← ecmCall
      (fun resultVar => Compiler.Modules.Hashing.sha256PackedStaticSegmentsModule resultVar [20, 32])
      [addressToWord who, amount]
    return digest

example :
    PackedHashECMSmoke.hashAddressAmount_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          (Compiler.Modules.Hashing.abiEncodePackedStaticSegmentsModule "digest" [20, 32])
          [ Compiler.CompilationModel.Expr.param "who"
          , Compiler.CompilationModel.Expr.param "amount"
          ]
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "digest")
      ] := rfl

example :
    PackedHashECMSmoke.hashLowByteAmount_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          (Compiler.Modules.Hashing.abiEncodePackedStaticSegmentsModule "digest" [1, 32])
          [ Compiler.CompilationModel.Expr.param "value"
          , Compiler.CompilationModel.Expr.param "amount"
          ]
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "digest")
      ] := rfl

example :
    PackedHashECMSmoke.sha256AddressAmount_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          (Compiler.Modules.Hashing.sha256PackedStaticSegmentsModule "digest" [20, 32])
          [ Compiler.CompilationModel.Expr.param "who"
          , Compiler.CompilationModel.Expr.param "amount"
          ]
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "digest")
      ] := rfl

end Contracts.Smoke
