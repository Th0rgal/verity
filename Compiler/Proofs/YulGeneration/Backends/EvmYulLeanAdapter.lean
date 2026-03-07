import Compiler.Yul.Ast
import Compiler.Constants
import EvmYul.Yul.Ast
import EvmYul.UInt256

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
  | .switch expr cases default => do
      let lowerCase := fun ((tag, block) : Nat × List YulStmt) => do
        let block' ← lowerStmts block
        pure (EvmYul.UInt256.ofNat tag, block')
      let cases' ← cases.mapM lowerCase
      let default' ← lowerStmts (default.getD [])
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

/-- Map a Verity builtin name to the corresponding EVMYulLean PrimOp.
    Returns `none` for Verity-specific helpers (e.g. `mappingSlot`) that
    have no direct EVMYulLean counterpart. -/
def lookupPrimOp : String → Option (EvmYul.Operation .Yul)
  | "add"          => some .ADD
  | "sub"          => some .SUB
  | "mul"          => some .MUL
  | "div"          => some .DIV
  | "mod"          => some .MOD
  | "lt"           => some .LT
  | "gt"           => some .GT
  | "eq"           => some .EQ
  | "iszero"       => some .ISZERO
  | "and"          => some .AND
  | "or"           => some .OR
  | "xor"          => some .XOR
  | "not"          => some .NOT
  | "shl"          => some .SHL
  | "shr"          => some .SHR
  | "sload"        => some .SLOAD
  | "caller"       => some .CALLER
  | "calldataload" => some .CALLDATALOAD
  | _              => none

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
  | "add", [a, b]    => some (toNat (EvmYul.UInt256.add (u a) (u b)))
  | "sub", [a, b]    => some (toNat (EvmYul.UInt256.sub (u a) (u b)))
  | "mul", [a, b]    => some (toNat (EvmYul.UInt256.mul (u a) (u b)))
  | "div", [a, b]    => some (toNat (EvmYul.UInt256.div (u a) (u b)))
  | "mod", [a, b]    => some (toNat (EvmYul.UInt256.mod (u a) (u b)))
  | "lt",  [a, b]    => some (if (u a) < (u b) then 1 else 0)
  | "gt",  [a, b]    => some (if (u b) < (u a) then 1 else 0)
  | "eq",  [a, b]    => some (if a % EvmYul.UInt256.size = b % EvmYul.UInt256.size then 1 else 0)
  | "iszero", [a]    => some (if a % EvmYul.UInt256.size = 0 then 1 else 0)
  | "and", [a, b]    => some (toNat (EvmYul.UInt256.land (u a) (u b)))
  | "or",  [a, b]    => some (toNat (EvmYul.UInt256.lor (u a) (u b)))
  | "xor", [a, b]    => some (toNat (EvmYul.UInt256.xor (u a) (u b)))
  | "not", [a]       => some (toNat (EvmYul.UInt256.lnot (u a)))
  | "shl", [s, v]    => some (toNat (EvmYul.UInt256.shiftLeft (u v) (u s)))
  | "shr", [s, v]    => some (toNat (EvmYul.UInt256.shiftRight (u v) (u s)))
  | _, _              => none

/-- Full builtin bridge: delegates pure arithmetic/comparison/bitwise builtins
    to EVMYulLean UInt256 operations. State-dependent builtins (`sload`,
    `caller`, `address`, `timestamp`, `calldataload`) and Verity-specific
    helpers (`mappingSlot`) fall through to the Verity path via `none`. -/
def evalBuiltinCallViaEvmYulLean
    (_storage : Nat → Nat)
    (_sender : Nat)
    (_selector : Nat)
    (_calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  evalPureBuiltinViaEvmYulLean func argVals

end Compiler.Proofs.YulGeneration.Backends
