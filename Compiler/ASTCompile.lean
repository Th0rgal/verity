/-
  Compiler.ASTCompile: Compile Unified AST to Yul

  Compiles `Verity.AST.Expr`/`Verity.AST.Stmt` directly to Yul IR,
  bypassing the `ContractSpec` layer entirely. This is the key step
  toward issue #364 (unify EDSL and ContractSpec).

  Key difference from `ContractSpec.compileExpr`/`compileStmt`:
  - Storage slots are `Nat` (not string field names) — no lookup needed
  - Continuation-passing style → flattened to `List YulStmt`
  - Pure (no `Except String`) since there are no name resolution errors

  Combined with `Verity.Denote` (AST → Contract monad), this gives:

      denote ast = EDSL function        (by rfl)
      compileAST ast = Yul code         (this module)

  A future structural induction proof will show:
      ∀ ast state, exec (compileAST ast) state ≈ denote ast state
-/

import Verity.AST
import Compiler.ContractSpec

namespace Compiler.ASTCompile

open Verity.AST
open Compiler.ContractSpec (revertWithMessage uint256Modulus)

/-!
## Expression Compilation

Maps `Verity.AST.Expr` to `Yul.YulExpr`. Pure expressions compile
to pure Yul; effectful expressions (storage reads) compile to `sload`/
`mappingSlot` calls.
-/

/-- Compile an AST expression to Yul. Effectful reads (storage, mapping, sender)
    are compiled to their EVM equivalents. -/
def compileExpr : Expr → Yul.YulExpr
  -- Pure value expressions
  | .lit n      => Yul.YulExpr.lit (n.val % uint256Modulus)
  | .var name   => Yul.YulExpr.ident name
  | .varAddr name => Yul.YulExpr.ident name
  -- Effectful reads (compiled to Yul builtins)
  | .storage slot    => Yul.YulExpr.call "sload" [Yul.YulExpr.lit slot]
  | .storageAddr slot => Yul.YulExpr.call "sload" [Yul.YulExpr.lit slot]
  | .mapping slot key =>
      Yul.YulExpr.call "sload" [
        Yul.YulExpr.call "mappingSlot" [Yul.YulExpr.lit slot, compileExpr key]
      ]
  | .sender     => Yul.YulExpr.call "caller" []
  -- Arithmetic
  | .add a b    => Yul.YulExpr.call "add" [compileExpr a, compileExpr b]
  | .sub a b    => Yul.YulExpr.call "sub" [compileExpr a, compileExpr b]
  | .mul a b    => Yul.YulExpr.call "mul" [compileExpr a, compileExpr b]
  -- Comparisons
  | .eqAddr a b => Yul.YulExpr.call "eq" [compileExpr a, compileExpr b]
  | .ge a b     => Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt" [compileExpr a, compileExpr b]]
  | .gt a b     => Yul.YulExpr.call "gt" [compileExpr a, compileExpr b]
  -- Safe arithmetic (Option-returning in EDSL, compiled to overflow-checked patterns)
  -- These are only used in `requireSome` position; the Yul equivalent is
  -- add/sub followed by an overflow check in the `requireSome` compilation.
  | .safeAdd a b => Yul.YulExpr.call "add" [compileExpr a, compileExpr b]
  | .safeSub a b => Yul.YulExpr.call "sub" [compileExpr a, compileExpr b]

/-- Compile a condition expression to its *failure* predicate, avoiding
    double-negation. For example, `require(ge(a,b))` compiles to `if lt(a,b) { revert }`. -/
def compileFailCond : Expr → Yul.YulExpr
  | .ge a b     => Yul.YulExpr.call "lt" [compileExpr a, compileExpr b]
  | .gt a b     => Yul.YulExpr.call "iszero" [Yul.YulExpr.call "gt" [compileExpr a, compileExpr b]]
  | .eqAddr a b => Yul.YulExpr.call "iszero" [Yul.YulExpr.call "eq" [compileExpr a, compileExpr b]]
  | other       => Yul.YulExpr.call "iszero" [compileExpr other]

/-!
## Statement Compilation

The key challenge: `Verity.AST.Stmt` uses continuation-passing style
(each statement carries a `rest : Stmt` tail), while Yul uses flat
statement lists. We flatten by recursively compiling `rest` and
appending.

Variable binding (`.bindUint`, `.bindAddr`, `.letUint`) compiles to
`let name := expr` in Yul. Storage writes compile to `sstore`.
-/

/-- Compile an AST statement to a list of Yul statements.
    Flattens the continuation-passing style into a sequential list. -/
def compileStmt : Stmt → List Yul.YulStmt
  -- Terminals
  | .ret e =>
      [ Yul.YulStmt.expr (Yul.YulExpr.call "mstore" [Yul.YulExpr.lit 0, compileExpr e]),
        Yul.YulStmt.expr (Yul.YulExpr.call "return" [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32]) ]
  | .retAddr e =>
      [ Yul.YulStmt.expr (Yul.YulExpr.call "mstore" [Yul.YulExpr.lit 0, compileExpr e]),
        Yul.YulStmt.expr (Yul.YulExpr.call "return" [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32]) ]
  | .stop =>
      [ Yul.YulStmt.expr (Yul.YulExpr.call "stop" []) ]

  -- Monadic binds: compile to `let name := expr; rest`
  | .bindUint name expr rest =>
      Yul.YulStmt.let_ name (compileExpr expr) :: compileStmt rest
  | .bindAddr name expr rest =>
      Yul.YulStmt.let_ name (compileExpr expr) :: compileStmt rest
  | .bindBool name expr rest =>
      Yul.YulStmt.let_ name (compileExpr expr) :: compileStmt rest

  -- Pure let
  | .letUint name expr rest =>
      Yul.YulStmt.let_ name (compileExpr expr) :: compileStmt rest

  -- Storage writes
  | .sstore slot valExpr rest =>
      Yul.YulStmt.expr (Yul.YulExpr.call "sstore" [
        Yul.YulExpr.lit slot, compileExpr valExpr
      ]) :: compileStmt rest
  | .sstoreAddr slot valExpr rest =>
      Yul.YulStmt.expr (Yul.YulExpr.call "sstore" [
        Yul.YulExpr.lit slot, compileExpr valExpr
      ]) :: compileStmt rest
  | .mstore slot keyExpr valExpr rest =>
      Yul.YulStmt.expr (Yul.YulExpr.call "sstore" [
        Yul.YulExpr.call "mappingSlot" [Yul.YulExpr.lit slot, compileExpr keyExpr],
        compileExpr valExpr
      ]) :: compileStmt rest

  -- Require guard
  | .require condExpr msg rest =>
      Yul.YulStmt.if_ (compileFailCond condExpr) (revertWithMessage msg)
      :: compileStmt rest

  -- RequireSome: bind from Option-returning expression.
  -- In the EDSL, this is `let x ← requireSomeUint (safeAdd a b) msg`.
  -- In Yul, we compute the result, check overflow, and bind.
  -- The overflow check depends on whether it's safeAdd or safeSub.
  | .requireSome name (.safeAdd a b) msg rest =>
      let aExpr := compileExpr a
      let bExpr := compileExpr b
      let result := Yul.YulExpr.call "add" [aExpr, bExpr]
      -- Overflow check: result >= a (for addition, wrapping means result < a)
      [ Yul.YulStmt.let_ name result,
        Yul.YulStmt.if_ (Yul.YulExpr.call "lt" [Yul.YulExpr.ident name, aExpr])
          (revertWithMessage msg) ]
      ++ compileStmt rest
  | .requireSome name (.safeSub a b) msg rest =>
      let aExpr := compileExpr a
      let bExpr := compileExpr b
      -- Underflow check: a >= b (for subtraction, wrapping means a < b)
      [ Yul.YulStmt.if_ (Yul.YulExpr.call "lt" [aExpr, bExpr])
          (revertWithMessage msg),
        Yul.YulStmt.let_ name (Yul.YulExpr.call "sub" [aExpr, bExpr]) ]
      ++ compileStmt rest
  | .requireSome name _optExpr _msg rest =>
      -- Fallback for other Option expressions (shouldn't occur in practice)
      Yul.YulStmt.let_ name (Yul.YulExpr.lit 0)
      :: compileStmt rest

  -- If-then-else
  | .ite condExpr thenBranch elseBranch =>
      [ Yul.YulStmt.block (
          [ Yul.YulStmt.let_ "__ite_cond" (compileExpr condExpr) ] ++
          [ Yul.YulStmt.switch (Yul.YulExpr.ident "__ite_cond")
              [(1, compileStmt thenBranch)]
              (some (compileStmt elseBranch)) ]
        ) ]

end Compiler.ASTCompile
