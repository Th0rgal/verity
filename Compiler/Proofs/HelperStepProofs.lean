import Compiler.Proofs.IRGeneration.GenericInduction
import Compiler.Proofs.IRGeneration.SourceSemantics

/-!
# Helper Step Interface Proofs (Phase 1)

This module provides the infrastructure for constructing
`CompiledStmtStepWithHelpersAndHelperIR` witnesses for each of the four
helper-surface statement families:

1. Direct void helper calls (`Stmt.internalCall`)
2. Direct helper call with return binding (`Stmt.internalCallAssign`)
3. Expression-position helper calls (expr containing `Expr.internalCall`)
4. Structural helper transport (`Stmt.ite` / `Stmt.forEach` with helpers)

## Architecture

The four narrow step interfaces are already defined and assembled in
`GenericInduction.lean`. The assembly chain is:

```
StmtListDirectInternalHelperCallStepInterface
  + StmtListDirectInternalHelperAssignStepInterface
  → StmtListDirectInternalHelperStepInterface
    + StmtListExprInternalHelperStepInterface
    + StmtListStructuralInternalHelperStepInterface
    → StmtListInternalHelperSurfaceStepInterface
      + StmtListResidualHelperSurfaceStepInterface
      → StmtListHelperSurfaceStepInterface
        + StmtListHelperFreeStepInterface
        + StmtListHelperFreeCompiledCallsDisjoint
        → StmtListGenericWithHelpersAndHelperIR
```

## Proof strategy for each interface

### Direct void calls (`StmtListDirectInternalHelperCallStepInterface`)

Target: `Stmt.internalCall calleeName args` where
`stmtTouchesDirectInternalHelperCallSurface stmt = true`.

1. **compileOk**: `compileStmt` produces a Yul call expression statement.
2. **preserves**: Source `execStmtWithHelpers` dispatches to
   `interpretInternalFunctionFuel`; IR `execIRStmtsWithInternals` dispatches
   through `evalIRCallWithInternals`; bridge via summary postcondition.

### Direct assign calls (`StmtListDirectInternalHelperAssignStepInterface`)

Same as void calls plus return-value binding in source and Yul let-binding.

### Expression-position helpers (`StmtListExprInternalHelperStepInterface`)

Key: `InternalHelperSummaryPreservesWorldOnSuccess` ensures the helper
doesn't modify world state on success.

### Structural transport (`StmtListStructuralInternalHelperStepInterface`)

For `Stmt.ite` / `Stmt.forEach`: inductive — each branch satisfies the
list-level witness.
-/

namespace Compiler.Proofs.HelperStepProofs

open Compiler
open Compiler.CompilationModel
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-- For helper-surface-closed statement lists, the four narrow helper-step
interfaces are all trivially satisfied. This is the entry point for contracts
that do not use internal helpers at all. -/
theorem allHelperInterfacesSatisfied_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts ∧
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts ∧
    StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts ∧
    StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts :=
  ⟨stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed hsurface,
   stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed hsurface,
   stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed hsurface,
   stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed hsurface⟩

/-- Full assembly from the four narrow interfaces plus helper-free and residual
interfaces into the whole-statement-list-level witness. This is the top-level
composition theorem that the function-level proof consumes. -/
theorem fullHelperAwareListWitness_of_allInterfaces
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    hhelperFree hcall hassign hexpr hstruct hresidual hlegacy hnoInternalFunctions

/-- Convenience alias: full assembly using the disjoint-calls variant (for
contracts where the IR contract has internal functions but compiled IR calls
are disjoint from the internal table). Unlike the legacy-compatible variant,
this does not require `runtimeContract.internalFunctions = []`. -/
theorem fullHelperAwareListWitness_of_allInterfaces_disjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    hhelperFree
    (stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
      (stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
        (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
          hcall hassign)
        hexpr hstruct)
      hresidual)
    hdisjoint

/-- Fast-path for helper-free contracts: if the statement list doesn't touch
the helper surface at all, all five interfaces are vacuously satisfied and we
can go straight to the whole-list proof with just the helper-free step interface
and legacy compatibility. -/
theorem helperFreeContractWitness
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  let ⟨hcall, hassign, hexpr, hstruct⟩ :=
    allHelperInterfacesSatisfied_of_helperSurfaceClosed hsurface
  fullHelperAwareListWitness_of_allInterfaces
    hhelperFree hcall hassign hexpr hstruct
    (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed hsurface)
    hlegacy hnoInternalFunctions

/-- Fast-path using disjoint-calls variant for helper-free contracts with
non-empty internal function tables. -/
theorem helperFreeContractWitness_disjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  let ⟨hcall, hassign, hexpr, hstruct⟩ :=
    allHelperInterfacesSatisfied_of_helperSurfaceClosed hsurface
  fullHelperAwareListWitness_of_allInterfaces_disjoint
    hhelperFree hcall hassign hexpr hstruct
    (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed hsurface)
    hdisjoint

end Compiler.Proofs.HelperStepProofs
