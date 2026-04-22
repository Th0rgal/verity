import Compiler.Yul.Ast
import Compiler.Constants
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Calldata
import EvmYul.Yul.Ast
import EvmYul.UInt256
import Mathlib.Data.Finmap

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul

abbrev AdapterError := String

def lowerExpr : YulExpr → EvmYul.Yul.Ast.Expr
  | .lit n => .Lit (EvmYul.UInt256.ofNat n)
  | .hex n => .Lit (EvmYul.UInt256.ofNat n)
  | .str s => .Var s
  | .ident name => .Var name
  | .call func args => .Call (.inr func) (args.map lowerExpr)

mutual
partial def lowerStmts : List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | [] => pure []
  | stmt :: rest => do
      let stmts' ← lowerStmtGroup stmt
      let rest' ← lowerStmts rest
      pure (stmts' ++ rest')

/-- Lower a single Verity YulStmt to one or more EVMYulLean Stmts.
    Most cases produce exactly one statement; `for_` with init produces
    init stmts followed by the loop (EVMYulLean `For` has no init block). -/
partial def lowerStmtGroup : YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | .comment _ => pure [.Block []]
  | .let_ name value => pure [.Let [name] (some (lowerExpr value))]
  | .letMany names value => pure [.Let names (some (lowerExpr value))]
  | .assign name value =>
      -- EVMYulLean has no Assign; re-bind via Let (Yul semantics: assignment to
      -- existing variable is equivalent to re-declaration in the same scope).
      pure [.Let [name] (some (lowerExpr value))]
  | .expr e => pure [.ExprStmtCall (lowerExpr e)]
  | .leave => pure [.Leave]
  | .if_ cond body => do
      let body' ← lowerStmts body
      pure [.If (lowerExpr cond) body']
  | .for_ init cond post body => do
      let init' ← lowerStmts init
      let post' ← lowerStmts post
      let body' ← lowerStmts body
      -- EVMYulLean For has no init block; emit init stmts before the loop.
      pure (init' ++ [.For (lowerExpr cond) post' body'])
  | .switch expr cases defaultCase => do
      let lowerCase := fun ((tag, block) : Nat × List YulStmt) => do
        let block' ← lowerStmts block
        pure (EvmYul.UInt256.ofNat tag, block')
      let cases' ← cases.mapM lowerCase
      let default' ← lowerStmts (defaultCase.getD [])
      pure [.Switch (lowerExpr expr) cases' default']
  | .block stmts => do
      let stmts' ← lowerStmts stmts
      pure [.Block stmts']
  | .funcDef _name _params _rets body => do
      let body' ← lowerStmts body
      -- Lower to a Block containing the function body. EVMYulLean's
      -- FunctionDefinition is a separate type (not a Stmt constructor);
      -- for adapter coverage we emit the body as an inlined block.
      -- Full function-definition lowering requires YulContract.functions
      -- integration (tracked separately).
      pure [.Block body']

/-- Backward-compatible single-statement lowering (wraps lowerStmtGroup). -/
partial def lowerStmt : YulStmt → Except AdapterError EvmYul.Yul.Ast.Stmt
  | stmt => do
      let stmts ← lowerStmtGroup stmt
      pure (.Block stmts)

end

def lowerProgram (stmts : List YulStmt) : Except AdapterError EvmYul.Yul.Ast.Stmt := do
  let stmts' ← lowerStmts stmts
  pure (.Block stmts')

/-! ## Native EVMYulLean runtime lowering

The historical `lowerExpr` path above is intentionally preserved because the
existing bridge/report machinery reasons about the old structural adapter.
The native runtime path below is the #1737 migration entry point: it lowers
known Yul builtins to EVMYulLean primops (`.inl`) and leaves user/helper calls
as Yul function calls (`.inr`).
-/

/-- Map runtime Yul builtin names to native EVMYulLean primops.

This is broader than `lookupPrimOp`: it includes effectful/runtime operations
needed by `EvmYul.Yul.exec`, while unknown names remain user/helper functions.
-/
def lookupRuntimePrimOp : String → Option (EvmYul.Operation .Yul)
  | "stop"           => some .STOP
  | "add"            => some .ADD
  | "sub"            => some .SUB
  | "mul"            => some .MUL
  | "div"            => some .DIV
  | "sdiv"           => some .SDIV
  | "mod"            => some .MOD
  | "smod"           => some .SMOD
  | "addmod"         => some .ADDMOD
  | "mulmod"         => some .MULMOD
  | "exp"            => some .EXP
  | "signextend"     => some .SIGNEXTEND
  | "lt"             => some .LT
  | "gt"             => some .GT
  | "slt"            => some .SLT
  | "sgt"            => some .SGT
  | "eq"             => some .EQ
  | "iszero"         => some .ISZERO
  | "and"            => some .AND
  | "or"             => some .OR
  | "xor"            => some .XOR
  | "not"            => some .NOT
  | "byte"           => some .BYTE
  | "shl"            => some .SHL
  | "shr"            => some .SHR
  | "sar"            => some .SAR
  | "keccak256"      => some .KECCAK256
  | "address"        => some .ADDRESS
  | "balance"        => some .BALANCE
  | "origin"         => some .ORIGIN
  | "caller"         => some .CALLER
  | "callvalue"      => some .CALLVALUE
  | "calldataload"   => some .CALLDATALOAD
  | "calldatacopy"   => some .CALLDATACOPY
  | "calldatasize"   => some .CALLDATASIZE
  | "codesize"       => some .CODESIZE
  | "codecopy"       => some .CODECOPY
  | "gasprice"       => some .GASPRICE
  | "extcodesize"    => some .EXTCODESIZE
  | "extcodecopy"    => some .EXTCODECOPY
  | "extcodehash"    => some .EXTCODEHASH
  | "returndatasize" => some .RETURNDATASIZE
  | "returndatacopy" => some .RETURNDATACOPY
  | "blockhash"      => some .BLOCKHASH
  | "coinbase"       => some .COINBASE
  | "timestamp"      => some .TIMESTAMP
  | "number"         => some .NUMBER
  | "gaslimit"       => some .GASLIMIT
  | "chainid"        => some .CHAINID
  | "blobbasefee"    => some .BLOBBASEFEE
  | "selfbalance"    => some .SELFBALANCE
  | "mload"          => some .MLOAD
  | "mstore"         => some .MSTORE
  | "mstore8"        => some .MSTORE8
  | "sload"          => some .SLOAD
  | "sstore"         => some .SSTORE
  | "tload"          => some .TLOAD
  | "tstore"         => some .TSTORE
  | "msize"          => some .MSIZE
  | "gas"            => some .GAS
  | "pop"            => some .POP
  | "log0"           => some .LOG0
  | "log1"           => some .LOG1
  | "log2"           => some .LOG2
  | "log3"           => some .LOG3
  | "log4"           => some .LOG4
  | "return"         => some .RETURN
  | "revert"         => some .REVERT
  | "call"           => some .CALL
  | "staticcall"     => some .STATICCALL
  | "delegatecall"   => some .DELEGATECALL
  | "callcode"       => some .CALLCODE
  | _                => none

def lowerExprNative : YulExpr → EvmYul.Yul.Ast.Expr
  | .lit n => .Lit (EvmYul.UInt256.ofNat n)
  | .hex n => .Lit (EvmYul.UInt256.ofNat n)
  | .str s => .Var s
  | .ident name => .Var name
  | .call func args =>
      let loweredArgs := args.map lowerExprNative
      match lookupRuntimePrimOp func with
      | some prim => .Call (.inl prim) loweredArgs
      | none => .Call (.inr func) loweredArgs

@[simp] theorem lowerExprNative_call_runtimePrimOp
    (func : String)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (hOp : lookupRuntimePrimOp func = some op) :
    lowerExprNative (.call func args) =
      .Call (.inl op) (args.map lowerExprNative) := by
  simp [lowerExprNative, hOp]

@[simp] theorem lowerExprNative_call_userFunction
    (func : String)
    (args : List YulExpr)
    (hOp : lookupRuntimePrimOp func = none) :
    lowerExprNative (.call func args) =
      .Call (.inr func) (args.map lowerExprNative) := by
  simp [lowerExprNative, hOp]

mutual
partial def lowerStmtsNative :
    List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | stmts => do
      let (lowered, _) ← lowerStmtsNativeWithSwitchIds 0 stmts
      pure lowered

partial def lowerStmtsNativeWithSwitchIds
    (nextSwitchId : Nat) :
    List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt × Nat)
  | [] => pure ([], nextSwitchId)
  | stmt :: rest => do
      let (stmts', nextSwitchId) ←
        lowerStmtGroupNativeWithSwitchIds nextSwitchId stmt
      let (rest', nextSwitchId) ←
        lowerStmtsNativeWithSwitchIds nextSwitchId rest
      pure (stmts' ++ rest', nextSwitchId)

/-- Lower a statement for native `EvmYul.Yul.exec`.

Top-level function definitions are intentionally rejected here; callers that
need executable contracts should use `lowerRuntimeContractNative`, which places
them in `YulContract.functions`.
-/
partial def lowerStmtGroupNative :
    YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | stmt => do
      let (lowered, _) ← lowerStmtGroupNativeWithSwitchIds 0 stmt
      pure lowered

partial def lowerStmtGroupNativeWithSwitchIds
    (nextSwitchId : Nat) :
    YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt × Nat)
  | .comment _ => pure ([.Block []], nextSwitchId)
  | .let_ name value => pure ([.Let [name] (some (lowerExprNative value))], nextSwitchId)
  | .letMany names value => pure ([.Let names (some (lowerExprNative value))], nextSwitchId)
  | .assign name value => pure ([.Let [name] (some (lowerExprNative value))], nextSwitchId)
  | .expr e => pure ([.ExprStmtCall (lowerExprNative e)], nextSwitchId)
  | .leave => pure ([.Leave], nextSwitchId)
  | .if_ cond body => do
      let (body', nextSwitchId) ← lowerStmtsNativeWithSwitchIds nextSwitchId body
      pure ([.If (lowerExprNative cond) body'], nextSwitchId)
  | .for_ init cond post body => do
      let (init', nextSwitchId) ← lowerStmtsNativeWithSwitchIds nextSwitchId init
      let (post', nextSwitchId) ← lowerStmtsNativeWithSwitchIds nextSwitchId post
      let (body', nextSwitchId) ← lowerStmtsNativeWithSwitchIds nextSwitchId body
      pure (init' ++ [.For (lowerExprNative cond) post' body'], nextSwitchId)
  | .switch expr cases defaultCase => do
      -- EVMYulLean's `Switch` executor currently evaluates the default branch
      -- before selecting a case. Lower to lazy `if` guards so generated
      -- dispatchers do not revert on matched selectors.
      let discrName := s!"__verity_native_switch_discr_{nextSwitchId}"
      let nextSwitchId := nextSwitchId + 1
      let lowerCase := fun (nextSwitchId : Nat) ((tag, block) : Nat × List YulStmt) => do
        let (block', nextSwitchId) ←
          lowerStmtsNativeWithSwitchIds nextSwitchId block
        pure ((tag, block'), nextSwitchId)
      let (cases', nextSwitchId) ← cases.foldlM
        (fun (acc, nextSwitchId) c => do
          let (case', nextSwitchId) ← lowerCase nextSwitchId c
          pure (acc ++ [case'], nextSwitchId))
        ([], nextSwitchId)
      let (default', nextSwitchId) ← lowerStmtsNativeWithSwitchIds nextSwitchId (defaultCase.getD [])
      let discr := EvmYul.Yul.Ast.Expr.Var discrName
      let matchExpr (tag : Nat) : EvmYul.Yul.Ast.Expr :=
        .Call (.inl (EvmYul.Operation.EQ : EvmYul.Operation .Yul))
          [discr, .Lit (EvmYul.UInt256.ofNat tag)]
      let anyMatch :=
        cases'.foldr
          (fun (entry : Nat × List EvmYul.Yul.Ast.Stmt) acc =>
            .Call (.inl (EvmYul.Operation.OR : EvmYul.Operation .Yul))
              [matchExpr entry.fst, acc])
          (.Lit (EvmYul.UInt256.ofNat 0))
      let defaultGuard :=
        .Call (.inl (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)) [anyMatch]
      let caseIfs := cases'.map (fun (tag, body) => .If (matchExpr tag) body)
      let defaultIf := if default'.isEmpty then [] else [.If defaultGuard default']
      pure ([.Let [discrName] (some (lowerExprNative expr))] ++ caseIfs ++ defaultIf,
        nextSwitchId)
  | .block stmts => do
      let (stmts', nextSwitchId) ← lowerStmtsNativeWithSwitchIds nextSwitchId stmts
      pure ([.Block stmts'], nextSwitchId)
  | .funcDef name _ _ _ =>
      throw s!"native EVMYulLean statement lowering cannot inline function definition '{name}'; use lowerRuntimeContractNative"
end

def lowerFunctionDefinitionNative (params rets : List String) (body : List YulStmt) :
    Except AdapterError EvmYul.Yul.Ast.FunctionDefinition := do
  let body' ← lowerStmtsNative body
  pure (.Def params rets body')

abbrev NativeFunctionMap :=
  Finmap (fun (_ : EvmYul.Yul.Ast.YulFunctionName) =>
    EvmYul.Yul.Ast.FunctionDefinition)

private def insertNativeFunction
    (functions : NativeFunctionMap)
    (name : String) (definition : EvmYul.Yul.Ast.FunctionDefinition) :
    Except AdapterError NativeFunctionMap :=
  if functions.lookup name |>.isSome then
    throw s!"duplicate native Yul function definition '{name}'"
  else
    pure (functions.insert name definition)

partial def lowerRuntimeContractNativeAux
    (stmts : List YulStmt)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (functionsAcc : NativeFunctionMap) :
    Except AdapterError (List EvmYul.Yul.Ast.Stmt × NativeFunctionMap) := do
  match stmts with
  | [] => pure (dispatcherAcc.reverse, functionsAcc)
  | .funcDef name params rets body :: rest =>
      let definition ← lowerFunctionDefinitionNative params rets body
      let functionsAcc ← insertNativeFunction functionsAcc name definition
      lowerRuntimeContractNativeAux rest dispatcherAcc functionsAcc
  | stmt :: rest =>
      let lowered ← lowerStmtGroupNative stmt
      lowerRuntimeContractNativeAux rest (lowered.reverse ++ dispatcherAcc) functionsAcc

/-- Lower generated runtime Yul into an executable EVMYulLean contract shape. -/
def lowerRuntimeContractNative (stmts : List YulStmt) :
    Except AdapterError EvmYul.Yul.Ast.YulContract := do
  let emptyFunctions : NativeFunctionMap := ∅
  let (dispatcher, functions) ←
    lowerRuntimeContractNativeAux stmts [] emptyFunctions
  pure {
    dispatcher := .Block dispatcher,
    functions := functions
  }

/-- Map a Verity builtin name to the corresponding EVMYulLean PrimOp.
    Returns `none` for Verity-specific helpers (e.g. `mappingSlot`) that
    have no direct EVMYulLean counterpart. -/
def lookupPrimOp : String → Option (EvmYul.Operation .Yul)
  -- Unsigned arithmetic
  | "add"            => some .ADD
  | "sub"            => some .SUB
  | "mul"            => some .MUL
  | "div"            => some .DIV
  | "mod"            => some .MOD
  | "addmod"         => some .ADDMOD
  | "mulmod"         => some .MULMOD
  | "exp"            => some .EXP
  -- Signed arithmetic
  | "sdiv"           => some .SDIV
  | "smod"           => some .SMOD
  -- Comparison
  | "lt"             => some .LT
  | "gt"             => some .GT
  | "slt"            => some .SLT
  | "sgt"            => some .SGT
  | "eq"             => some .EQ
  | "iszero"         => some .ISZERO
  -- Bitwise / byte extraction
  | "byte"           => some .BYTE
  | "and"            => some .AND
  | "or"             => some .OR
  | "xor"            => some .XOR
  | "not"            => some .NOT
  | "shl"            => some .SHL
  | "shr"            => some .SHR
  | "sar"            => some .SAR
  | "signextend"     => some .SIGNEXTEND
  -- Environment
  | "address"        => some .ADDRESS
  | "caller"         => some .CALLER
  | "callvalue"      => some .CALLVALUE
  | "calldataload"   => some .CALLDATALOAD
  | "calldatasize"   => some .CALLDATASIZE
  -- Block information
  | "timestamp"      => some .TIMESTAMP
  | "number"         => some .NUMBER
  | "chainid"        => some .CHAINID
  | "blobbasefee"    => some .BLOBBASEFEE
  -- Storage
  | "sload"          => some .SLOAD
  | _                => none

/-- Evaluate a pure arithmetic/comparison/bitwise builtin via EVMYulLean
    UInt256 operations. This covers the overlap set of builtins where both
    Verity and EVMYulLean define equivalent semantics.

    State-dependent builtins (sload, caller, calldataload) and Verity-specific
    helpers (mappingSlot) are not handled here — they require full Yul state
    reconstruction and are delegated to the Verity path.

    Returns `none` for unsupported or state-dependent builtins. -/
def evalPureBuiltinViaEvmYulLean
    (func : String)
    (argVals : List Nat) : Option Nat :=
  let u := EvmYul.UInt256.ofNat
  let toNat := EvmYul.UInt256.toNat
  match func, argVals with
  -- Unsigned arithmetic
  | "add", [a, b]          => some (toNat (EvmYul.UInt256.add (u a) (u b)))
  | "sub", [a, b]          => some (toNat (EvmYul.UInt256.sub (u a) (u b)))
  | "mul", [a, b]          => some (toNat (EvmYul.UInt256.mul (u a) (u b)))
  | "div", [a, b]          => some (toNat (EvmYul.UInt256.div (u a) (u b)))
  | "mod", [a, b]          => some (toNat (EvmYul.UInt256.mod (u a) (u b)))
  | "addmod", [a, b, n]    => some (toNat (EvmYul.UInt256.addMod (u a) (u b) (u n)))
  | "mulmod", [a, b, n]    => some (toNat (EvmYul.UInt256.mulMod (u a) (u b) (u n)))
  | "exp", [a, b]          => some (toNat (EvmYul.UInt256.exp (u a) (u b)))
  -- Signed arithmetic
  | "sdiv", [a, b]         => some (toNat (EvmYul.UInt256.sdiv (u a) (u b)))
  | "smod", [a, b]         => some (toNat (EvmYul.UInt256.smod (u a) (u b)))
  -- Unsigned comparison
  | "lt",  [a, b]          => some (if (u a) < (u b) then 1 else 0)
  | "gt",  [a, b]          => some (if (u b) < (u a) then 1 else 0)
  | "eq",  [a, b]          => some (if a % EvmYul.UInt256.size = b % EvmYul.UInt256.size then 1 else 0)
  | "iszero", [a]          => some (if a % EvmYul.UInt256.size = 0 then 1 else 0)
  -- Signed comparison
  | "slt", [a, b]          => some (toNat (EvmYul.UInt256.slt (u a) (u b)))
  | "sgt", [a, b]          => some (toNat (EvmYul.UInt256.sgt (u a) (u b)))
  -- Bitwise / byte extraction
  | "byte", [i, x]         => some (toNat (EvmYul.UInt256.byteAt (u i) (u x)))
  | "and", [a, b]          => some (toNat (EvmYul.UInt256.land (u a) (u b)))
  | "or",  [a, b]          => some (toNat (EvmYul.UInt256.lor (u a) (u b)))
  | "xor", [a, b]          => some (toNat (EvmYul.UInt256.xor (u a) (u b)))
  | "not", [a]             => some (toNat (EvmYul.UInt256.lnot (u a)))
  | "shl", [s, v]          => some (toNat (EvmYul.UInt256.shiftLeft (u v) (u s)))
  | "shr", [s, v]          => some (toNat (EvmYul.UInt256.shiftRight (u v) (u s)))
  | "sar", [s, v]          => some (toNat (EvmYul.UInt256.sar (u s) (u v)))
  | "signextend", [b, v]   => some (toNat (EvmYul.UInt256.signextend (u b) (u v)))
  | _, _                    => none

/-- Full builtin bridge: delegates pure arithmetic/comparison/bitwise builtins
    to EVMYulLean UInt256 operations. `calldataload` is handled directly because
    its observable semantics depend only on the selector and calldata already
    available at this boundary. `sload` is handled via
    `abstractLoadStorageOrMapping`, the shared Verity/Phase-2 storage-read
    helper whose EVMYulLean-state correspondence is witnessed by
    `storageLookup_projectStorage` in `EvmYulLeanStateBridge.lean` (projecting
    the abstract `storage : Nat → Nat` into EVMYulLean's `Storage` recovers the
    same value). `mappingSlot` is bridged by routing through
    `abstractMappingSlot` — the same keccak-faithful Solidity mapping-slot
    derivation used by Verity's `evalBuiltinCallWithContext`; both backends
    ultimately compute `keccak256(abi.encode(key, baseSlot))`. Remaining
    context-dependent builtins (`caller`, `address`, `timestamp`, ...) are
    routed at the `evalBuiltinCallWithBackendContext` level. -/
def evalBuiltinCallViaEvmYulLean
    (storage : Nat → Nat)
    (_sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  match func, argVals with
  | "calldataload", [offset] => some (Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset)
  | "sload", [slot] => some (storage slot)
  | "mappingSlot", [base, key] => some (Compiler.Proofs.abstractMappingSlot base key)
  | _, _ => evalPureBuiltinViaEvmYulLean func argVals

end Compiler.Proofs.YulGeneration.Backends
