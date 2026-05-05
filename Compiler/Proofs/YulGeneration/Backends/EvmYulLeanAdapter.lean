import Compiler.Yul.Ast
import Compiler.Constants
import Compiler.Proofs.IRGeneration.IRStorageWord
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Calldata
import EvmYul.Yul.Ast
import EvmYul.UInt256
import Mathlib.Data.Finmap

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul
open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

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

/-- EVMYulLean's Yul AST represents both declaration-style bindings and
    reassignment-style bindings with `Stmt.Let`; its interpreter updates the
    `VarStore` by inserting the target name, replacing any previous binding.
    Keep this helper named so the native assignment boundary is explicit. -/
def lowerAssignNative (name : String) (value : YulExpr) : EvmYul.Yul.Ast.Stmt :=
  .Let [name] (some (lowerExprNative value))

/-- Build a native EVMYulLean primitive call expression.

This is public because the native dispatcher proof reasons directly about the
guard expressions introduced by `lowerNativeSwitchBlock`. -/
def nativePrimCall
    (op : EvmYul.Operation .Yul) (args : List EvmYul.Yul.Ast.Expr) :
    EvmYul.Yul.Ast.Expr :=
  .Call (.inl op) args

/-! ### Native switch temporary freshness -/

partial def yulExprIdentifierNames : YulExpr → List String
  | .lit _ | .hex _ => []
  | .str name | .ident name => [name]
  | .call _ args => args.foldl (fun acc arg => acc ++ yulExprIdentifierNames arg) []

mutual
  partial def yulStmtIdentifierNames : YulStmt → List String
    | .comment _ | .leave => []
    | .let_ name value => name :: yulExprIdentifierNames value
    | .letMany names value => names ++ yulExprIdentifierNames value
    | .assign name value => name :: yulExprIdentifierNames value
    | .expr e => yulExprIdentifierNames e
    | .if_ cond body => yulExprIdentifierNames cond ++ yulStmtsIdentifierNames body
    | .for_ init cond post body =>
        yulStmtsIdentifierNames init ++
          yulExprIdentifierNames cond ++
          yulStmtsIdentifierNames post ++
          yulStmtsIdentifierNames body
    | .switch discr cases defaultBody =>
        yulExprIdentifierNames discr ++
          cases.foldl (fun acc (_, body) => acc ++ yulStmtsIdentifierNames body) [] ++
          yulStmtsIdentifierNames (defaultBody.getD [])
    | .block stmts => yulStmtsIdentifierNames stmts
    | .funcDef name params rets body => name :: params ++ rets ++ yulStmtsIdentifierNames body

  partial def yulStmtsIdentifierNames (stmts : List YulStmt) : List String :=
    stmts.foldl (fun acc stmt => acc ++ yulStmtIdentifierNames stmt) []
end

def collectYulStmtWriteNames
    (writeStmt : YulStmt → List String) : List YulStmt → List String
  | [] => []
  | stmt :: rest => writeStmt stmt ++ collectYulStmtWriteNames writeStmt rest

partial def yulStmtWriteNames : YulStmt → List String
  | .comment _ | .expr _ | .leave => []
  | .let_ name _ => [name]
  | .letMany names _ => names
  | .assign name _ => [name]
  | .if_ _ body => collectYulStmtWriteNames yulStmtWriteNames body
  | .for_ init _ post body =>
      collectYulStmtWriteNames yulStmtWriteNames init ++
        collectYulStmtWriteNames yulStmtWriteNames post ++
        collectYulStmtWriteNames yulStmtWriteNames body
  | .switch _ cases defaultBody =>
      cases.foldl
          (fun acc (_, body) =>
            acc ++ collectYulStmtWriteNames yulStmtWriteNames body) [] ++
        collectYulStmtWriteNames yulStmtWriteNames (defaultBody.getD [])
  | .block stmts => collectYulStmtWriteNames yulStmtWriteNames stmts
  | .funcDef _ params rets body =>
      params ++ rets ++ collectYulStmtWriteNames yulStmtWriteNames body

def yulStmtsWriteNames (stmts : List YulStmt) : List String :=
  collectYulStmtWriteNames yulStmtWriteNames stmts

def collectNativeStmtWriteNames
    (writeStmt : EvmYul.Yul.Ast.Stmt → List String) :
    List EvmYul.Yul.Ast.Stmt → List String
  | [] => []
  | stmt :: rest =>
      writeStmt stmt ++ collectNativeStmtWriteNames writeStmt rest

partial def nativeStmtWriteNames : EvmYul.Yul.Ast.Stmt → List String
  | .Block stmts => collectNativeStmtWriteNames nativeStmtWriteNames stmts
  | .Let names _ => names
  | .ExprStmtCall _ | .Continue | .Break | .Leave => []
  | .Switch _ cases defaultBody =>
      cases.foldl
          (fun acc (_, body) =>
            acc ++ collectNativeStmtWriteNames nativeStmtWriteNames body) [] ++
        collectNativeStmtWriteNames nativeStmtWriteNames defaultBody
  | .For _ post body =>
      collectNativeStmtWriteNames nativeStmtWriteNames post ++
        collectNativeStmtWriteNames nativeStmtWriteNames body
  | .If _ body => collectNativeStmtWriteNames nativeStmtWriteNames body

def nativeStmtsWriteNames (stmts : List EvmYul.Yul.Ast.Stmt) : List String :=
  collectNativeStmtWriteNames nativeStmtWriteNames stmts

def nativeSwitchDiscrTempName (switchId : Nat) : String :=
  s!"__verity_native_switch_discr_{switchId}"

def nativeSwitchMatchedTempName (switchId : Nat) : String :=
  s!"__verity_native_switch_matched_{switchId}"

def nativeSwitchTempsFreshForWrites
    (switchId : Nat)
    (writeNames : List String) : Prop :=
  nativeSwitchDiscrTempName switchId ∉ writeNames ∧
    nativeSwitchMatchedTempName switchId ∉ writeNames

def nativeSwitchTempsFreshForSourceBodies
    (switchId : Nat)
    (cases' : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt)) : Prop :=
  (∀ tag body,
      (tag, body) ∈ cases' →
        nativeSwitchTempsFreshForWrites switchId (yulStmtsWriteNames body)) ∧
    (∀ body,
      defaultBody = some body →
        nativeSwitchTempsFreshForWrites switchId (yulStmtsWriteNames body))

def nativeSwitchTempsFreshForNativeBodies
    (switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) : Prop :=
  (∀ tag body,
      (tag, body) ∈ cases' →
        nativeSwitchTempsFreshForWrites switchId (nativeStmtsWriteNames body)) ∧
    nativeSwitchTempsFreshForWrites switchId (nativeStmtsWriteNames defaultBody)

partial def freshNativeSwitchId (reservedNames : List String) (candidate : Nat) : Nat :=
  let discrName := nativeSwitchDiscrTempName candidate
  let matchedName := nativeSwitchMatchedTempName candidate
  if reservedNames.contains discrName || reservedNames.contains matchedName then
    freshNativeSwitchId reservedNames (candidate + 1)
  else
    candidate

def lowerNativeSwitchBlock
    (expr : YulExpr)
    (switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (default' : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.Stmt :=
  let discrName := nativeSwitchDiscrTempName switchId
  let matchedName := nativeSwitchMatchedTempName switchId
  let discr := EvmYul.Yul.Ast.Expr.Var discrName
  let matched := EvmYul.Yul.Ast.Expr.Var matchedName
  let matchExpr (tag : Nat) : EvmYul.Yul.Ast.Expr :=
    nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
      [discr, .Lit (EvmYul.UInt256.ofNat tag)]
  let unmatched : EvmYul.Yul.Ast.Expr :=
    nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul) [matched]
  let guardedMatch (tag : Nat) : EvmYul.Yul.Ast.Expr :=
    nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
      [unmatched, matchExpr tag]
  let defaultGuard :=
    nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul) [matched]
  let markMatched := lowerAssignNative matchedName (.lit 1)
  let caseIfs := cases'.map (fun (tag, body) => .If (guardedMatch tag) (markMatched :: body))
  let defaultIf := if default'.isEmpty then [] else [.If defaultGuard default']
  .Block ([ .Let [discrName] (some (lowerExprNative expr))
          , .Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))) ] ++
         caseIfs ++ defaultIf)

/-- Native switch lowering expands to a lazy guarded block instead of using
    EVMYulLean's eager `.Switch` form. The native/EVMYulLean dispatcher proof
    should consume this shape directly: the first statement evaluates the
    discriminator once, each case is guarded by `iszero(matched) && discr == tag`,
    and the optional default runs only if no case marked the switch matched. -/
theorem lowerNativeSwitchBlock_eq
    (expr : YulExpr)
    (switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (default' : List EvmYul.Yul.Ast.Stmt) :
    lowerNativeSwitchBlock expr switchId cases' default' =
      (let discrName := nativeSwitchDiscrTempName switchId
       let matchedName := nativeSwitchMatchedTempName switchId
       let discr := EvmYul.Yul.Ast.Expr.Var discrName
       let matched := EvmYul.Yul.Ast.Expr.Var matchedName
       let matchExpr := fun tag =>
         nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
           [discr, .Lit (EvmYul.UInt256.ofNat tag)]
       let unmatched :=
         nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul) [matched]
       let guardedMatch := fun tag =>
         nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
           [unmatched, matchExpr tag]
       let defaultGuard :=
         nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul) [matched]
       let markMatched := lowerAssignNative matchedName (.lit 1)
       let caseIfs := cases'.map (fun (tag, body) => .If (guardedMatch tag) (markMatched :: body))
       let defaultIf := if default'.isEmpty then [] else [.If defaultGuard default']
       .Block ([ .Let [discrName] (some (lowerExprNative expr))
               , .Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))) ] ++
              caseIfs ++ defaultIf)) := by
  rfl

mutual
def lowerStmtsNativeWithSwitchIds
    (reservedNames : List String)
    (nextSwitchId : Nat) :
    List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt × Nat)
  | [] => pure ([], nextSwitchId)
  | stmt :: rest => do
      let (stmts', nextSwitchId) ←
        lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt
      let (rest', nextSwitchId) ←
        lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId rest
      pure (stmts' ++ rest', nextSwitchId)
termination_by stmts => sizeOf stmts
decreasing_by all_goals simp_wf; all_goals omega

def lowerSwitchCasesNativeWithSwitchIds
    (reservedNames : List String)
    (nextSwitchId : Nat) :
    List (Nat × List YulStmt) →
      Except AdapterError (List (Nat × List EvmYul.Yul.Ast.Stmt) × Nat)
  | [] => pure ([], nextSwitchId)
  | (tag, block) :: rest => do
      let (block', nextSwitchId) ←
        lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId block
      let (rest', nextSwitchId) ←
        lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId rest
      pure ((tag, block') :: rest', nextSwitchId)
termination_by cases => sizeOf cases
decreasing_by all_goals simp_wf; all_goals omega

def lowerStmtGroupNativeWithSwitchIds
    (reservedNames : List String)
    (nextSwitchId : Nat) :
    YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt × Nat)
  | .comment _ => pure ([.Block []], nextSwitchId)
  | .let_ name value => pure ([.Let [name] (some (lowerExprNative value))], nextSwitchId)
  | .letMany names value => pure ([.Let names (some (lowerExprNative value))], nextSwitchId)
  | .assign name value => pure ([lowerAssignNative name value], nextSwitchId)
  | .expr e => pure ([.ExprStmtCall (lowerExprNative e)], nextSwitchId)
  | .leave => pure ([.Leave], nextSwitchId)
  | .if_ cond body => do
      let (body', nextSwitchId) ← lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId body
      pure ([.If (lowerExprNative cond) body'], nextSwitchId)
  | .for_ init cond post body => do
      let (init', nextSwitchId) ← lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId init
      let (post', nextSwitchId) ← lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId post
      let (body', nextSwitchId) ← lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId body
      pure (init' ++ [.For (lowerExprNative cond) post' body'], nextSwitchId)
  | .switch expr cases defaultCase => do
      -- EVMYulLean's `Switch` executor currently evaluates the default branch
      -- before selecting a case. Lower to lazy `if` guards with an explicit
      -- match flag so exactly one non-halting branch can execute. Generate
      -- temporary names outside the source identifier surface to avoid
      -- shadowing user-visible Yul variables.
      let switchId := freshNativeSwitchId reservedNames nextSwitchId
      let nextSwitchId := switchId + 1
      let (cases', nextSwitchId) ←
        lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId cases
      let (default', nextSwitchId) ←
        match defaultCase with
        | some defaultBody =>
            lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId defaultBody
        | none => pure ([], nextSwitchId)
      pure ([lowerNativeSwitchBlock expr switchId cases' default'], nextSwitchId)
  | .block stmts => do
      let (stmts', nextSwitchId) ← lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts
      pure ([.Block stmts'], nextSwitchId)
  | .funcDef name _ _ _ =>
      throw s!"native EVMYulLean statement lowering cannot inline function definition '{name}'; use lowerRuntimeContractNative"
termination_by stmt => sizeOf stmt
decreasing_by all_goals simp_wf; all_goals omega
end

def lowerStmtsNative :
    List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | stmts => do
      let (lowered, _) ←
        lowerStmtsNativeWithSwitchIds (yulStmtsIdentifierNames stmts) 0 stmts
      pure lowered

@[simp] theorem lowerStmtsNativeWithSwitchIds_nil
    (reservedNames : List String)
    (nextSwitchId : Nat) :
    lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId [] =
      .ok ([], nextSwitchId) :=
  lowerStmtsNativeWithSwitchIds.eq_1 reservedNames nextSwitchId

/-- Statement-list native lowering exposes a stable head/tail equation.

This is the statement-level analogue of the top-level runtime partition
equations below: future native/EVMYulLean preservation proofs can reason by
the source statement list instead of treating the native lowerer as an opaque
executable. -/
theorem lowerStmtsNativeWithSwitchIds_cons
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmt : YulStmt)
    (rest : List YulStmt) :
    lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId (stmt :: rest) =
      (do
        let loweredAndNext ←
          lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt
        match loweredAndNext with
        | (stmts', nextSwitchId) =>
            let restAndNext ←
              lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId rest
            match restAndNext with
            | (rest', nextSwitchId) => pure (stmts' ++ rest', nextSwitchId)) :=
  lowerStmtsNativeWithSwitchIds.eq_2 reservedNames nextSwitchId stmt rest

@[simp] theorem lowerSwitchCasesNativeWithSwitchIds_nil
    (reservedNames : List String)
    (nextSwitchId : Nat) :
    lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId [] =
      .ok ([], nextSwitchId) :=
  lowerSwitchCasesNativeWithSwitchIds.eq_1 reservedNames nextSwitchId

/-- Native switch case lowering preserves the case spine and threads the switch
temp counter through each lowered case body.

The generated dispatcher proof needs this before it can relate selected source
`switch` cases to the lazy guarded native lowering used to avoid EVMYulLean's
eager default execution. -/
theorem lowerSwitchCasesNativeWithSwitchIds_cons
    (reservedNames : List String)
    (nextSwitchId tag : Nat)
    (block : List YulStmt)
    (rest : List (Nat × List YulStmt)) :
    lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
        ((tag, block) :: rest) =
      (do
        let blockAndNext ←
          lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId block
        match blockAndNext with
        | (block', nextSwitchId) =>
            let restAndNext ←
              lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId rest
            match restAndNext with
            | (rest', nextSwitchId) => pure ((tag, block') :: rest', nextSwitchId)) :=
  lowerSwitchCasesNativeWithSwitchIds.eq_2 reservedNames nextSwitchId tag block rest

/-- Lowering native switch cases preserves selector misses through the lowered
case spine.

The native dispatcher proof consumes this to move from source-level selector
lookup to the generated guarded case list before considering an optional
default branch. -/
theorem lowerSwitchCasesNativeWithSwitchIds_find?_none
    (reservedNames : List String) (nextSwitchId final selector : Nat)
    (cases : List (Nat × List YulStmt))
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId cases =
      .ok (cases', final))
    (hFind : cases.find? (fun entry => entry.1 == selector) = none) :
    cases'.find? (fun entry => entry.1 == selector) = none := by
  induction cases generalizing nextSwitchId cases' final with
  | nil =>
      simp at hLower
      rcases hLower with ⟨rfl, rfl⟩
      simp
  | cons head rest ih =>
      rcases head with ⟨tag, block⟩
      cases hBlock : lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId block with
      | error err =>
          simp [lowerSwitchCasesNativeWithSwitchIds.eq_2, hBlock] at hLower
          cases hLower
      | ok blockAndNext =>
          rcases blockAndNext with ⟨block', nextSwitchId'⟩
          rw [lowerSwitchCasesNativeWithSwitchIds.eq_2, hBlock] at hLower
          change
            ((fun a => ((tag, block') :: a.1, a.2)) <$>
              lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId' rest) =
                Except.ok (cases', final) at hLower
          cases hRest :
              lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId' rest with
          | error err =>
              rw [hRest] at hLower
              simp at hLower
          | ok restAndNext =>
              rcases restAndNext with ⟨rest', final'⟩
              rw [hRest] at hLower
              simp at hLower
              rcases hLower with ⟨rfl, rfl⟩
              by_cases hTag : tag == selector
              · simp [List.find?, hTag] at hFind
              · have hRestFind :
                    rest.find? (fun entry => entry.1 == selector) = none := by
                    simpa [List.find?, hTag] using hFind
                have hLowerRest :
                    rest'.find? (fun entry => entry.1 == selector) = none :=
                  ih nextSwitchId' final' rest' hRest hRestFind
                simp [List.find?, hTag, hLowerRest]

/-- Lowering native switch cases preserves selector hits through the lowered
case spine, while exposing the switch-temp counter range used to lower the
selected body. -/
theorem lowerSwitchCasesNativeWithSwitchIds_find?_some
    (reservedNames : List String) (nextSwitchId final selector tag : Nat)
    (body : List YulStmt) (cases : List (Nat × List YulStmt))
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId cases =
      .ok (cases', final))
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body)) :
    ∃ body' bodyStart bodyEnd,
      cases'.find? (fun entry => entry.1 == selector) = some (tag, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart body =
        .ok (body', bodyEnd) := by
  induction cases generalizing nextSwitchId cases' final with
  | nil =>
      simp [List.find?] at hFind
  | cons head rest ih =>
      rcases head with ⟨headTag, headBody⟩
      cases hBlock : lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId headBody with
      | error err =>
          simp [lowerSwitchCasesNativeWithSwitchIds.eq_2, hBlock] at hLower
          cases hLower
      | ok blockAndNext =>
          rcases blockAndNext with ⟨headBody', nextSwitchId'⟩
          rw [lowerSwitchCasesNativeWithSwitchIds.eq_2, hBlock] at hLower
          change ((fun a => ((headTag, headBody') :: a.1, a.2)) <$>
            lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId' rest) =
              Except.ok (cases', final) at hLower
          cases hRest : lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId' rest with
          | error err =>
              rw [hRest] at hLower
              simp at hLower
          | ok restAndNext =>
              rcases restAndNext with ⟨rest', final'⟩
              rw [hRest] at hLower
              simp at hLower
              rcases hLower with ⟨rfl, rfl⟩
              by_cases hTag : headTag == selector
              · have hHead : (headTag, headBody) = (tag, body) := by
                    simpa [List.find?, hTag] using hFind
                cases hHead
                exact ⟨headBody', nextSwitchId, nextSwitchId',
                  by simp [List.find?, hTag], hBlock⟩
              · have hRestFind : rest.find? (fun entry => entry.1 == selector) =
                    some (tag, body) := by
                    simpa [List.find?, hTag] using hFind
                rcases ih nextSwitchId' final' rest' hRest hRestFind with
                  ⟨body', bodyStart, bodyEnd, hLowerFind, hLowerBody⟩
                exact ⟨body', bodyStart, bodyEnd,
                  by simp [List.find?, hTag, hLowerFind], hLowerBody⟩

/-- Native switch case lowering preserves the tag spine of the source cases. -/
theorem lowerSwitchCasesNativeWithSwitchIds_tags_eq
    (reservedNames : List String) (nextSwitchId final : Nat)
    (cases : List (Nat × List YulStmt))
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId cases =
      .ok (cases', final)) :
    cases'.map (·.1) = cases.map (·.1) := by
  induction cases generalizing nextSwitchId cases' final with
  | nil =>
      simp at hLower
      rcases hLower with ⟨rfl, _⟩
      rfl
  | cons head rest ih =>
      rcases head with ⟨tag, block⟩
      cases hBlock : lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId block with
      | error err =>
          simp [lowerSwitchCasesNativeWithSwitchIds.eq_2, hBlock] at hLower
          cases hLower
      | ok blockAndNext =>
          rcases blockAndNext with ⟨block', nextSwitchId'⟩
          rw [lowerSwitchCasesNativeWithSwitchIds.eq_2, hBlock] at hLower
          change ((fun a => ((tag, block') :: a.1, a.2)) <$>
            lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId' rest) =
              Except.ok (cases', final) at hLower
          cases hRest :
              lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId' rest with
          | error err =>
              rw [hRest] at hLower
              simp at hLower
          | ok restAndNext =>
              rcases restAndNext with ⟨rest', final'⟩
              rw [hRest] at hLower
              simp at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hRestTags := ih nextSwitchId' final' rest' hRest
              simp [List.map, hRestTags]

/-- Length companion of `lowerSwitchCasesNativeWithSwitchIds_tags_eq`: the
lowered case list has the same length as the source case list. Useful when
fuel parameters or other arithmetic in downstream proofs depend on
`cases'.length`. -/
theorem lowerSwitchCasesNativeWithSwitchIds_length_eq
    (reservedNames : List String) (nextSwitchId final : Nat)
    (cases : List (Nat × List YulStmt))
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId cases =
      .ok (cases', final)) :
    cases'.length = cases.length := by
  have h := lowerSwitchCasesNativeWithSwitchIds_tags_eq
    reservedNames nextSwitchId final cases cases' hLower
  have hLen := congrArg List.length h
  simpa using hLen

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_comment
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (text : String) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.comment text) =
      .ok ([.Block []], nextSwitchId) :=
  lowerStmtGroupNativeWithSwitchIds.eq_1 reservedNames nextSwitchId text

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_let
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (name : String)
    (value : YulExpr) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.let_ name value) =
      .ok ([.Let [name] (some (lowerExprNative value))], nextSwitchId) :=
  lowerStmtGroupNativeWithSwitchIds.eq_2 reservedNames nextSwitchId name value

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_letMany
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (names : List String)
    (value : YulExpr) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.letMany names value) =
      .ok ([.Let names (some (lowerExprNative value))], nextSwitchId) :=
  lowerStmtGroupNativeWithSwitchIds.eq_3 reservedNames nextSwitchId names value

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_assign
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (name : String)
    (value : YulExpr) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.assign name value) =
      .ok ([lowerAssignNative name value], nextSwitchId) :=
  lowerStmtGroupNativeWithSwitchIds.eq_4 reservedNames nextSwitchId name value

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_expr
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (e : YulExpr) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.expr e) =
      .ok ([.ExprStmtCall (lowerExprNative e)], nextSwitchId) :=
  lowerStmtGroupNativeWithSwitchIds.eq_5 reservedNames nextSwitchId e

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_leave
    (reservedNames : List String)
    (nextSwitchId : Nat) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId .leave =
      .ok ([.Leave], nextSwitchId) :=
  lowerStmtGroupNativeWithSwitchIds.eq_6 reservedNames nextSwitchId

theorem lowerStmtGroupNativeWithSwitchIds_if
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (cond : YulExpr)
    (body : List YulStmt) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.if_ cond body) =
      (do
        let bodyAndNext ←
          lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId body
        match bodyAndNext with
        | (body', nextSwitchId) =>
            pure ([.If (lowerExprNative cond) body'], nextSwitchId)) :=
  lowerStmtGroupNativeWithSwitchIds.eq_7 reservedNames nextSwitchId cond body

theorem lowerStmtGroupNativeWithSwitchIds_for
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (init : List YulStmt)
    (cond : YulExpr)
    (post body : List YulStmt) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.for_ init cond post body) =
      (do
        let initAndNext ←
          lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId init
        match initAndNext with
        | (init', nextSwitchId) =>
            let postAndNext ←
              lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId post
            match postAndNext with
            | (post', nextSwitchId) =>
                let bodyAndNext ←
                  lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId body
                match bodyAndNext with
                | (body', nextSwitchId) =>
                    pure (init' ++ [.For (lowerExprNative cond) post' body'],
                      nextSwitchId)) :=
  lowerStmtGroupNativeWithSwitchIds.eq_8 reservedNames nextSwitchId init cond post body

theorem lowerStmtGroupNativeWithSwitchIds_switch
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (expr : YulExpr)
    (cases : List (Nat × List YulStmt))
    (defaultCase : Option (List YulStmt)) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.switch expr cases defaultCase) =
      (let switchId := freshNativeSwitchId reservedNames nextSwitchId
       do
        let casesAndNext ←
          lowerSwitchCasesNativeWithSwitchIds reservedNames (switchId + 1) cases
        match casesAndNext with
        | (cases', nextSwitchId) =>
            let defaultAndNext ←
              match defaultCase with
              | some defaultBody =>
                  lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId
                    defaultBody
              | none => pure ([], nextSwitchId)
            match defaultAndNext with
            | (default', nextSwitchId) =>
                pure ([lowerNativeSwitchBlock expr switchId cases' default'],
                  nextSwitchId)) :=
  lowerStmtGroupNativeWithSwitchIds.eq_9 reservedNames nextSwitchId expr cases defaultCase

theorem lowerStmtGroupNativeWithSwitchIds_block
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (stmts : List YulStmt) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId (.block stmts) =
      (do
        let stmtsAndNext ←
          lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts
        match stmtsAndNext with
        | (stmts', nextSwitchId) => pure ([.Block stmts'], nextSwitchId)) :=
  lowerStmtGroupNativeWithSwitchIds.eq_10 reservedNames nextSwitchId stmts

@[simp] theorem lowerStmtGroupNativeWithSwitchIds_funcDef
    (reservedNames : List String)
    (nextSwitchId : Nat)
    (name : String)
    (params rets : List String)
    (body : List YulStmt) :
    lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId
        (.funcDef name params rets body) =
      .error s!"native EVMYulLean statement lowering cannot inline function definition '{name}'; use lowerRuntimeContractNative" :=
  lowerStmtGroupNativeWithSwitchIds.eq_11 reservedNames nextSwitchId name params rets body

def lowerFunctionDefinitionNativeWithReserved
    (globalReservedNames : List String)
    (params rets : List String)
    (body : List YulStmt) :
    Except AdapterError EvmYul.Yul.Ast.FunctionDefinition := do
  let reservedNames := globalReservedNames ++ params ++ rets ++ yulStmtsIdentifierNames body
  let (body', _) ← lowerStmtsNativeWithSwitchIds reservedNames 0 body
  pure (.Def params rets body')

def lowerFunctionDefinitionNative (params rets : List String) (body : List YulStmt) :
    Except AdapterError EvmYul.Yul.Ast.FunctionDefinition := do
  lowerFunctionDefinitionNativeWithReserved (yulStmtsIdentifierNames body) params rets body

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

def lowerRuntimeContractNativeAux
    (reservedNames : List String)
    (stmts : List YulStmt)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (functionsAcc : NativeFunctionMap)
    (nextSwitchId : Nat) :
    Except AdapterError (List EvmYul.Yul.Ast.Stmt × NativeFunctionMap × Nat) := do
  match stmts with
  | [] => pure (dispatcherAcc.reverse, functionsAcc, nextSwitchId)
  | .funcDef name params rets body :: rest =>
      let definition ← lowerFunctionDefinitionNativeWithReserved reservedNames params rets body
      let functionsAcc ← insertNativeFunction functionsAcc name definition
      lowerRuntimeContractNativeAux reservedNames rest dispatcherAcc functionsAcc nextSwitchId
  | stmt :: rest =>
      let (lowered, nextSwitchId) ←
        lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt
      lowerRuntimeContractNativeAux reservedNames rest (lowered.reverse ++ dispatcherAcc) functionsAcc
        nextSwitchId

@[simp] theorem lowerRuntimeContractNativeAux_nil
    (reservedNames : List String)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (functionsAcc : NativeFunctionMap)
    (nextSwitchId : Nat) :
    lowerRuntimeContractNativeAux reservedNames [] dispatcherAcc functionsAcc nextSwitchId =
      .ok (dispatcherAcc.reverse, functionsAcc, nextSwitchId) := by
  rw [lowerRuntimeContractNativeAux.eq_1]
  rfl

/-- Top-level native runtime lowering partitions a `funcDef` into the native
function map rather than appending it to dispatcher code.

Keeping this equation named is important for the native migration proof: it is
the first generated-fragment shape fact needed before proving that
`callDispatcher` runs the same selected body as the EVMYulLean fuel wrapper. -/
theorem lowerRuntimeContractNativeAux_funcDef_cons
    (reservedNames : List String)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (functionsAcc : NativeFunctionMap)
    (nextSwitchId : Nat)
    (name : String)
    (params rets : List String)
    (body rest : List YulStmt) :
    lowerRuntimeContractNativeAux reservedNames
        (YulStmt.funcDef name params rets body :: rest)
        dispatcherAcc functionsAcc nextSwitchId =
      (do
        let definition ← lowerFunctionDefinitionNativeWithReserved reservedNames params rets body
        let functionsAcc ← insertNativeFunction functionsAcc name definition
        lowerRuntimeContractNativeAux reservedNames rest dispatcherAcc functionsAcc nextSwitchId) := by
  rw [lowerRuntimeContractNativeAux.eq_2]

/-- Specialization of `lowerRuntimeContractNativeAux_funcDef_cons` for the
first helper definition in a runtime: once the helper body lowers, inserting it
into the empty native function map cannot hit the duplicate-definition guard. -/
theorem lowerRuntimeContractNativeAux_funcDef_cons_empty_of_lowerFunctionDefinition
    (reservedNames : List String)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (nextSwitchId : Nat)
    (name : String)
    (params rets : List String)
    (body rest : List YulStmt)
    (definition : EvmYul.Yul.Ast.FunctionDefinition)
    (hLower : lowerFunctionDefinitionNativeWithReserved
      reservedNames params rets body = .ok definition) :
    lowerRuntimeContractNativeAux reservedNames
        (YulStmt.funcDef name params rets body :: rest)
        dispatcherAcc (∅ : NativeFunctionMap) nextSwitchId =
      lowerRuntimeContractNativeAux reservedNames rest dispatcherAcc
        ((∅ : NativeFunctionMap).insert name definition) nextSwitchId := by
  rw [lowerRuntimeContractNativeAux_funcDef_cons, hLower]
  simp [insertNativeFunction, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Top-level native runtime lowering appends non-`funcDef` statements to the
dispatcher accumulator after statement lowering.

Together with `lowerRuntimeContractNativeAux_funcDef_cons`, this gives proofs a
transparent partition boundary for generated runtime code: helper definitions
flow to the function map, while the switch dispatcher remains dispatcher code. -/
theorem lowerRuntimeContractNativeAux_stmt_cons
    (reservedNames : List String)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (functionsAcc : NativeFunctionMap)
    (nextSwitchId : Nat)
    (stmt : YulStmt)
    (rest : List YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    lowerRuntimeContractNativeAux reservedNames (stmt :: rest)
        dispatcherAcc functionsAcc nextSwitchId =
      (do
        let loweredAndNext ←
          lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt
        match loweredAndNext with
        | (lowered, nextSwitchId) =>
            lowerRuntimeContractNativeAux reservedNames rest
              (lowered.reverse ++ dispatcherAcc) functionsAcc nextSwitchId) := by
  rw [lowerRuntimeContractNativeAux.eq_3]
  intro name params rets body h
  exact hNoFunc name params rets body h

/-- Lower generated runtime Yul into an executable EVMYulLean contract shape. -/
def lowerRuntimeContractNative (stmts : List YulStmt) :
    Except AdapterError EvmYul.Yul.Ast.YulContract := do
  let emptyFunctions : NativeFunctionMap := ∅
  let reservedNames := yulStmtsIdentifierNames stmts
  let (dispatcher, functions, _) ←
    lowerRuntimeContractNativeAux reservedNames stmts [] emptyFunctions 0
  pure {
    dispatcher := .Block dispatcher,
    functions := functions
  }

@[simp] theorem lowerRuntimeContractNative_empty :
    lowerRuntimeContractNative [] =
      .ok { dispatcher := EvmYul.Yul.Ast.Stmt.Block []
            functions := (∅ : NativeFunctionMap) } := by
  simp [lowerRuntimeContractNative]

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
    the abstract `storage : IRStorageSlot → IRStorageWord` into EVMYulLean's `Storage` recovers the
    same value). `mappingSlot` is bridged by routing through
    `abstractMappingSlot` — the same keccak-faithful Solidity mapping-slot
    derivation used by Verity's `legacyEvalBuiltinCallWithContext`; both backends
    ultimately compute `keccak256(abi.encode(key, baseSlot))`. Remaining
    context-dependent builtins (`caller`, `address`, `timestamp`, ...) are
    routed at the `evalBuiltinCallWithBackendContext` level. -/
def evalBuiltinCallViaEvmYulLean
    (storage : IRStorageSlot → IRStorageWord)
    (_sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  match func, argVals with
  | "calldataload", [offset] => some (Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset)
  | "sload", [slot] => some (storage (IRStorageSlot.ofNat slot)).toNat
  | "mappingSlot", [base, key] => some (Compiler.Proofs.abstractMappingSlot base key)
  | _, _ => evalPureBuiltinViaEvmYulLean func argVals

end Compiler.Proofs.YulGeneration.Backends
