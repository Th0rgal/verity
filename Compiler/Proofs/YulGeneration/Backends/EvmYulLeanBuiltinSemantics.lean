import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

/-- Native EVMYulLean-backed builtin evaluation with full execution context.

This is the native-default builtin surface used by public IR/Yul proof entry
points. Environment-only opcodes are handled directly from the context; all
ordinary, storage, calldata, and helper builtins are routed through
`evalBuiltinCallViaEvmYulLean`. -/
def evalBuiltinCallWithEvmYulLeanContext
    (storage : IRStorageSlot → IRStorageWord)
    (sender : Nat)
    (msgValue : Nat)
    (thisAddress : Nat)
    (blockTimestamp : Nat)
    (blockNumber : Nat)
    (chainId : Nat)
    (blobBaseFee : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  let toWord (x : Nat) : Nat := x % Compiler.Constants.evmModulus
  if func = "caller" then
    match argVals with
    | [] => some sender
    | _ => none
  else if func = "address" then
    match argVals with
    | [] => some (toWord thisAddress)
    | _ => none
  else if func = "callvalue" then
    match argVals with
    | [] => some (toWord msgValue)
    | _ => none
  else if func = "timestamp" then
    match argVals with
    | [] => some (toWord blockTimestamp)
    | _ => none
  else if func = "number" then
    match argVals with
    | [] => some (toWord blockNumber)
    | _ => none
  else if func = "chainid" then
    match argVals with
    | [] => some (toWord chainId)
    | _ => none
  else if func = "blobbasefee" then
    match argVals with
    | [] => some (toWord blobBaseFee)
    | _ => none
  else if func = "calldatasize" then
    match argVals with
    | [] => some (toWord (4 + calldata.length * 32))
    | _ => none
  else
    evalBuiltinCallViaEvmYulLean storage sender selector calldata func argVals

def evalBuiltinCallWithEvmYulLean
    (storage : IRStorageSlot → IRStorageWord)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  evalBuiltinCallWithEvmYulLeanContext storage sender 0 0 0 0 0 0 selector calldata func argVals

end Compiler.Proofs.YulGeneration.Backends
