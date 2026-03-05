import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

def isLowLevelCallName (name : String) : Bool :=
  ["call", "staticcall", "delegatecall", "callcode"].contains name

def interopBuiltinCallNames : List String :=
  ["stop", "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "not",
   "lt", "gt", "slt", "sgt", "eq", "iszero", "and", "or", "xor", "byte", "shl", "shr", "sar",
   "addmod", "mulmod", "signextend",
   "keccak256", "pop",
   "mload", "mstore", "mstore8", "sload", "sstore", "tload", "tstore", "msize", "gas", "pc",
   "address", "balance", "selfbalance", "origin", "caller", "callvalue", "gasprice",
   "blockhash", "coinbase", "timestamp", "number", "difficulty", "prevrandao", "gaslimit",
   "chainid", "basefee", "blobbasefee", "blobhash",
   "calldataload", "calldatasize", "calldatacopy", "codesize", "codecopy",
   "extcodesize", "extcodecopy", "extcodehash",
   "returndatasize", "returndatacopy", "mcopy",
   "create", "create2", "return", "revert", "selfdestruct", "invalid",
   "log0", "log1", "log2", "log3", "log4"]

def isInteropBuiltinCallName (name : String) : Bool :=
  (isLowLevelCallName name) || interopBuiltinCallNames.contains name

/-- Returns true for special entrypoint names (fallback/receive) that are not
    dispatched via selector. Used by Selector.computeSelectors, ABI.lean, and
    CompilationModel.compile to consistently filter these from selector-dispatched
    external functions. -/
def isInteropEntrypointName (name : String) : Bool :=
  ["fallback", "receive"].contains name

def firstDuplicateSelector (selectors : List Nat) : Option Nat :=
  let rec go (seen : List Nat) : List Nat → Option Nat
    | [] => none
    | sel :: rest =>
      if seen.contains sel then
        some sel
      else
        go (sel :: seen) rest
  go [] selectors

def selectorNames (spec : CompilationModel) (selectors : List Nat) (sel : Nat) : List String :=
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  (externalFns.zip selectors).foldl (fun acc (fn, s) =>
    if s == sel then acc ++ [fn.name] else acc
  ) []

end Compiler.CompilationModel
