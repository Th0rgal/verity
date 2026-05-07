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

/-- The concrete lowered native contract for `simpleStorage`.

Keeping this definition executable lets downstream concrete proofs reduce the
generated dispatcher instead of reasoning through an opaque `Classical.choose`
witness. The accompanying theorem below proves that the fallback arm is not
used for the generated runtime. -/
def nativeContract : EvmYul.Yul.Ast.YulContract :=
  match
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul simpleStorageIRContract).runtimeCode with
  | .ok nativeContract => nativeContract
  | .error _ => { dispatcher := .Block [], functions := ∅ }

@[simp] theorem lowerRuntimeContractNative_eq :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul simpleStorageIRContract).runtimeCode =
        .ok nativeContract :=
  by
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
    | ok lowered =>
        unfold nativeContract
        rw [hLower]
    | error err =>
        rw [hLower] at hOk
        cases hOk

end Compiler.SimpleStorageNativeWitness
