import Compiler.Codegen
import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness

namespace Compiler.SimpleStorageNativeWitness

open Compiler.Proofs.IRGeneration

/-- Computed native lowering witness for the generated `simpleStorage` runtime.

This file is deliberately outside `Compiler/Proofs`: the executable computation
packages a concrete artifact, while theorem modules consume only the resulting
equality. -/
theorem lowerRuntimeContractNative_ok :
    ∃ nativeContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul simpleStorageIRContract).runtimeCode = .ok nativeContract := by
  have hOk :
      (match
          Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
            (Compiler.emitYul simpleStorageIRContract).runtimeCode with
        | .ok _ => true
        | .error _ => false) = true := by
    native_decide
  cases hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul simpleStorageIRContract).runtimeCode with
  | ok nativeContract =>
      exact ⟨nativeContract, rfl⟩
  | error _ =>
      have := hOk
      rw [hLower] at this
      cases this

noncomputable def nativeContract : EvmYul.Yul.Ast.YulContract :=
  Classical.choose lowerRuntimeContractNative_ok

theorem lowerRuntimeContractNative_eq :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul simpleStorageIRContract).runtimeCode =
        .ok nativeContract :=
  Classical.choose_spec lowerRuntimeContractNative_ok

end Compiler.SimpleStorageNativeWitness
