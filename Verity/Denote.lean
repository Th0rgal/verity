/-
  Verity.Denote: AST → EDSL Denotation

  Interprets the unified AST into the Contract monad. Every case directly
  calls the corresponding EDSL primitive, ensuring that:

    denote ast = handwritten_fn

  holds by `rfl` (definitional equality) when the AST was derived from
  the same contract logic.

  ## Auditor's checklist

  To verify the bridge is sound, check:
  1. Each `Stmt` constructor's denotation calls the matching EDSL primitive
     (e.g., `.sstore slot val rest` → `setStorage ⟨slot⟩ ...`)
  2. Terminal patterns (`.sstore ... .stop`) emit the primitive directly
     without `bind ... pure`, matching do-block desugaring
  3. Environment extension (`fun s => if s == name then val else env s`)
     mirrors Lean's `let name ← ...` binding
  4. Per-contract `_equiv` theorems in `Verity/AST/*.lean` are `rfl` or
     use only `bind_assoc`/`bind_pure_left` — no domain-specific axioms

  ## How `rfl` works

  All definitions referenced here (`bind`, `pure`, `getStorage`, etc.)
  are transparent `def`s, so Lean's kernel can unfold both sides to the
  same normal form.

  The `env`/`envAddr` parameters track variables bound by `Stmt.bindUint`
  and `Stmt.bindAddr`. After unfolding, `env "x"` reduces to the same
  lambda-bound variable that do-notation produces, making `rfl` work.
-/

import Verity.AST
import Verity.EVM.Uint256
import Verity.Stdlib.Math

namespace Verity.Denote

open Verity
open Verity.AST
open Verity.EVM.Uint256 (add sub mul)
open Verity.Stdlib.Math (safeAdd safeSub requireSomeUint)

/-- Evaluate a pure Uint256 expression. Only uses bound variables (via `env`)
    and literals — no state access. -/
def denoteVal (env : String → Uint256) : Expr → Uint256
  | .lit n     => n
  | .var name  => env name
  | .add a b   => add (denoteVal env a) (denoteVal env b)
  | .sub a b   => sub (denoteVal env a) (denoteVal env b)
  | .mul a b   => mul (denoteVal env a) (denoteVal env b)
  | _          => 0

/-- Evaluate a pure Address expression. -/
def denoteAddr (envAddr : String → Address) : Expr → Address
  | .varAddr name => envAddr name
  | _             => ""

/-- Evaluate a pure Bool expression (for `require` / `ite` conditions). -/
def denoteBool (env : String → Uint256) (envAddr : String → Address) : Expr → Bool
  | .eqAddr a b => denoteAddr envAddr a == denoteAddr envAddr b
  | .ge a b     => denoteVal env a >= denoteVal env b
  | .gt a b     => denoteVal env a > denoteVal env b
  | other       => denoteVal env other != 0  -- Uint256-to-Bool coercion (nonzero = true)

/-- Evaluate an Option Uint256 expression (for `requireSome`). -/
def denoteOpt (env : String → Uint256) : Expr → Option Uint256
  | .safeAdd a b => safeAdd (denoteVal env a) (denoteVal env b)
  | .safeSub a b => safeSub (denoteVal env a) (denoteVal env b)
  | _            => none

/-!
## Statement Denotation

Three variants for the three contract return types.

Critical design: When a storage write or other effectful statement is followed
by `.stop`, we emit the primitive directly (e.g., `setStorage ⟨slot⟩ val`)
without wrapping in `bind ... (fun () => pure ())`. This matches how Lean
desugars the last line of a do-block and is essential for `rfl`.
-/

/-- Denote a statement as `Contract Unit`. -/
def denoteUnit (env : String → Uint256) (envAddr : String → Address) : Stmt → Contract Unit

  | .stop => Verity.pure ()

  -- Bind Uint256 from effectful read
  | .bindUint name (.storage slot) rest =>
      Verity.bind (getStorage ⟨slot⟩) fun val =>
        denoteUnit (fun s => if s == name then val else env s) envAddr rest

  | .bindUint name (.mapping slot key) rest =>
      Verity.bind (getMapping ⟨slot⟩ (denoteAddr envAddr key)) fun val =>
        denoteUnit (fun s => if s == name then val else env s) envAddr rest

  -- Fallback: unsupported bindUint source (unreachable for well-formed ASTs).
  -- An incorrect AST would fail to `rfl`-prove equivalence.
  | .bindUint _name _expr rest => denoteUnit env envAddr rest

  -- Bind Address from effectful read
  | .bindAddr name .sender rest =>
      Verity.bind msgSender fun addr =>
        denoteUnit env (fun s => if s == name then addr else envAddr s) rest

  | .bindAddr name (.storageAddr slot) rest =>
      Verity.bind (getStorageAddr ⟨slot⟩) fun addr =>
        denoteUnit env (fun s => if s == name then addr else envAddr s) rest

  -- Fallback: unsupported bindAddr source (unreachable for well-formed ASTs)
  | .bindAddr _name _expr rest => denoteUnit env envAddr rest

  -- Bind Bool (e.g., isOwner check)
  | .bindBool name expr rest =>
      Verity.bind (Verity.pure (denoteBool env envAddr expr)) fun val =>
        denoteUnit (fun s => if s == name then (if val then 1 else 0) else env s) envAddr rest

  -- Pure let: extend env without monadic effect
  | .letUint name expr rest =>
      denoteUnit (fun s => if s == name then denoteVal env expr else env s) envAddr rest

  -- Storage write: terminal (last statement) vs non-terminal
  | .sstore slot valExpr .stop =>
      setStorage ⟨slot⟩ (denoteVal env valExpr)

  | .sstore slot valExpr rest =>
      Verity.bind (setStorage ⟨slot⟩ (denoteVal env valExpr)) fun () =>
        denoteUnit env envAddr rest

  -- Address storage write: terminal vs non-terminal
  | .sstoreAddr slot valExpr .stop =>
      setStorageAddr ⟨slot⟩ (denoteAddr envAddr valExpr)

  | .sstoreAddr slot valExpr rest =>
      Verity.bind (setStorageAddr ⟨slot⟩ (denoteAddr envAddr valExpr)) fun () =>
        denoteUnit env envAddr rest

  -- Mapping write: terminal vs non-terminal
  | .mstore slot keyExpr valExpr .stop =>
      setMapping ⟨slot⟩ (denoteAddr envAddr keyExpr) (denoteVal env valExpr)

  | .mstore slot keyExpr valExpr rest =>
      Verity.bind (setMapping ⟨slot⟩ (denoteAddr envAddr keyExpr) (denoteVal env valExpr)) fun () =>
        denoteUnit env envAddr rest

  -- Require guard
  | .require condExpr msg rest =>
      Verity.bind (Verity.require (denoteBool env envAddr condExpr) msg) fun () =>
        denoteUnit env envAddr rest

  -- RequireSome: bind from Option-returning expression
  | .requireSome name optExpr msg rest =>
      Verity.bind (requireSomeUint (denoteOpt env optExpr) msg) fun val =>
        denoteUnit (fun s => if s == name then val else env s) envAddr rest

  -- If-then-else: produce `ite` directly (not eta-expanded) so rfl matches do-notation
  | .ite condExpr thenBranch elseBranch =>
      if denoteBool env envAddr condExpr
      then denoteUnit env envAddr thenBranch
      else denoteUnit env envAddr elseBranch

  -- Return statements in a Unit context: ignore the value
  | .ret _e => Verity.pure ()
  | .retAddr _e => Verity.pure ()

/-- Denote a statement as `Contract Uint256` (for getter functions). -/
def denoteUint (env : String → Uint256) (envAddr : String → Address) : Stmt → Contract Uint256

  | .ret e => Verity.pure (denoteVal env e)

  | .bindUint name (.storage slot) rest =>
      Verity.bind (getStorage ⟨slot⟩) fun val =>
        denoteUint (fun s => if s == name then val else env s) envAddr rest

  | .bindUint name (.mapping slot key) rest =>
      Verity.bind (getMapping ⟨slot⟩ (denoteAddr envAddr key)) fun val =>
        denoteUint (fun s => if s == name then val else env s) envAddr rest

  -- Fallback: unsupported bindUint source (unreachable for well-formed ASTs)
  | .bindUint _name _expr rest => denoteUint env envAddr rest

  | .bindAddr name .sender rest =>
      Verity.bind msgSender fun addr =>
        denoteUint env (fun s => if s == name then addr else envAddr s) rest

  | .bindAddr name (.storageAddr slot) rest =>
      Verity.bind (getStorageAddr ⟨slot⟩) fun addr =>
        denoteUint env (fun s => if s == name then addr else envAddr s) rest

  -- Fallback: unsupported bindAddr source (unreachable for well-formed ASTs)
  | .bindAddr _name _expr rest => denoteUint env envAddr rest

  -- Default: remaining patterns (unreachable for well-formed ASTs)
  | _ => Verity.pure 0

/-- Denote a statement as `Contract Address` (for address getters). -/
def denoteAddress (env : String → Uint256) (envAddr : String → Address) : Stmt → Contract Address

  | .retAddr (.varAddr name) => Verity.pure (envAddr name)

  | .bindAddr name (.storageAddr slot) rest =>
      Verity.bind (getStorageAddr ⟨slot⟩) fun addr =>
        denoteAddress env (fun s => if s == name then addr else envAddr s) rest

  | .bindAddr name .sender rest =>
      Verity.bind msgSender fun addr =>
        denoteAddress env (fun s => if s == name then addr else envAddr s) rest

  -- Default: remaining patterns (unreachable for well-formed ASTs)
  | _ => Verity.pure ""

/-!
## Monad Laws

The monad laws (`Contract.bind_assoc`, `Contract.bind_pure_left`,
`Contract.bind_pure_right`) are proved in `Verity.Core` with `@[simp]`.
`bind_assoc` lets us flatten nested `bind` from helper composition
(e.g., `onlyOwner` calling `isOwner`). Combined with `rfl`-based AST
denotation, this enables equivalence proofs for contracts that use
modular helper functions.
-/

/-- Default empty environments for use in equivalence proofs. -/
def emptyEnv : String → Uint256 := fun _ => 0
def emptyEnvAddr : String → Address := fun _ => ""

end Verity.Denote
