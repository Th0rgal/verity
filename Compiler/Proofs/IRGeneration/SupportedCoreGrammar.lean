import Compiler.CompilationModel.Types

/-!
# Core grammar fragments for supported IR proof surface

Self-contained inductive types and helper definitions that classify
which expression/statement AST fragments the generic proof layer can
already handle.  These live in their own file so that both
`SupportedFragment.lean` (upstream) and `FunctionBody.lean`
(downstream) can reference them without creating an import cycle.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

namespace FunctionBody

mutual
def exprBoundNames : Expr → List String
  | .param name => [name]
  | .localVar name => [name]
  | .mapping _ key | .mappingWord _ key _ | .mappingPackedWord _ key _ _ | .mappingUint _ key
  | .structMember _ key _ | .extcodesize key | .mload key | .tload key
  | .calldataload key | .returndataOptionalBoolAt key => exprBoundNames key
  | .mapping2 _ key1 key2 | .mapping2Word _ key1 key2 _ | .structMember2 _ key1 key2 _ =>
      exprBoundNames key1 ++ exprBoundNames key2
  | .keccak256 offset size =>
      exprBoundNames offset ++ exprBoundNames size
  | .call gas target value inOffset inSize outOffset outSize =>
      exprBoundNames gas ++ exprBoundNames target ++ exprBoundNames value ++
        exprBoundNames inOffset ++ exprBoundNames inSize ++
        exprBoundNames outOffset ++ exprBoundNames outSize
  | .staticcall gas target inOffset inSize outOffset outSize =>
      exprBoundNames gas ++ exprBoundNames target ++ exprBoundNames inOffset ++
        exprBoundNames inSize ++ exprBoundNames outOffset ++ exprBoundNames outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      exprBoundNames gas ++ exprBoundNames target ++ exprBoundNames inOffset ++
        exprBoundNames inSize ++ exprBoundNames outOffset ++ exprBoundNames outSize
  | .externalCall _ args | .internalCall _ args => exprListBoundNames args
  | .dynamicBytesEq _ _ => []
  | .mappingChain _ keys => exprListBoundNames keys
  | .arrayElement name index => name :: exprBoundNames index
  | .arrayLength name => [name]
  | .storageArrayLength name => [name]
  | .storageArrayElement name index => name :: exprBoundNames index
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b | .wMulDown a b
  | .wDivUp a b | .min a b | .max a b
  | .shl a b | .shr a b | .sar a b | .signextend a b =>
      exprBoundNames a ++ exprBoundNames b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprBoundNames a ++ exprBoundNames b ++ exprBoundNames c
  | .bitNot a | .logicalNot a => exprBoundNames a
  | .ite cond thenVal elseVal =>
      exprBoundNames cond ++ exprBoundNames thenVal ++ exprBoundNames elseVal
  | .literal _ | .constructorArg _ | .storage _ | .storageAddr _ | .caller
  | .contractAddress | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .blobbasefee | .calldatasize | .returndataSize => []
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals omega

def exprListBoundNames : List Expr → List String
  | [] => []
  | expr :: rest => exprBoundNames expr ++ exprListBoundNames rest
termination_by exprs => sizeOf exprs
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def exprBoundNamesInScope (expr : Expr) (scope : List String) : Prop :=
  ∀ name, name ∈ exprBoundNames expr → name ∈ scope

/-- Expression fragment whose `compileExpr` correctness is already structurally
closed: scalar leaves, runtime builtins, arithmetic, comparisons, and boolean
operators. Storage/mapping/dynamic forms still require separate invariants. -/
inductive ExprCompileCore : Expr → Prop where
  | literal (value : Nat) : ExprCompileCore (.literal value)
  | param (name : String) : ExprCompileCore (.param name)
  | localVar (name : String) : ExprCompileCore (.localVar name)
  | caller : ExprCompileCore .caller
  | contractAddress : ExprCompileCore .contractAddress
  | msgValue : ExprCompileCore .msgValue
  | blockTimestamp : ExprCompileCore .blockTimestamp
  | blockNumber : ExprCompileCore .blockNumber
  | chainid : ExprCompileCore .chainid
  | add {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.add lhs rhs)
  | sub {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.sub lhs rhs)
  | mul {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.mul lhs rhs)
  | div {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.div lhs rhs)
  | mod {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.mod lhs rhs)
  | eq {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.eq lhs rhs)
  | lt {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.lt lhs rhs)
  | gt {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.gt lhs rhs)
  | ge {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.ge lhs rhs)
  | le {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.le lhs rhs)
  | logicalNot {expr : Expr} :
      ExprCompileCore expr → ExprCompileCore (.logicalNot expr)
  | logicalAnd {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.logicalAnd lhs rhs)
  | logicalOr {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.logicalOr lhs rhs)

/-- Sequential statement fragment that can already be proved generically from the
expression core. The scope tracks names available to later expressions. -/
inductive StmtListCompileCore : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListCompileCore scope []
  | letVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore (name :: scope) rest →
      StmtListCompileCore scope (.letVar name value :: rest)
  | assignVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore (name :: scope) rest →
      StmtListCompileCore scope (.assignVar name value :: rest)
  | require_ {scope : List String} {cond : Expr} {message : String} {rest : List Stmt} :
      ExprCompileCore cond →
      exprBoundNamesInScope cond scope →
      StmtListCompileCore scope rest →
      StmtListCompileCore scope (.require cond message :: rest)
  | return_ {scope : List String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore scope rest →
      StmtListCompileCore scope (.return value :: rest)
  | stop {scope : List String} {rest : List Stmt} :
      StmtListCompileCore scope rest →
      StmtListCompileCore scope (.stop :: rest)

/-- Core statement lists whose execution is guaranteed to terminate before
reaching the end of the list. This is the smallest useful extension needed
to simulate `Stmt.ite` without threading an exact-global bindings invariant
through the compiler-generated `__ite_cond` temporary. -/
inductive StmtListTerminalCore : List String → List Stmt → Prop where
  | letVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListTerminalCore (name :: scope) rest →
      StmtListTerminalCore scope (.letVar name value :: rest)
  | assignVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListTerminalCore (name :: scope) rest →
      StmtListTerminalCore scope (.assignVar name value :: rest)
  | require_ {scope : List String} {cond : Expr} {message : String} {rest : List Stmt} :
      ExprCompileCore cond →
      exprBoundNamesInScope cond scope →
      StmtListTerminalCore scope rest →
      StmtListTerminalCore scope (.require cond message :: rest)
  | return_ {scope : List String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore scope rest →
      StmtListTerminalCore scope (.return value :: rest)
  | stop {scope : List String} {rest : List Stmt} :
      StmtListCompileCore scope rest →
      StmtListTerminalCore scope (.stop :: rest)
  | ite {scope : List String} {cond : Expr}
      {thenBranch elseBranch rest : List Stmt} :
      ExprCompileCore cond →
      exprBoundNamesInScope cond scope →
      StmtListTerminalCore scope thenBranch →
      StmtListTerminalCore scope elseBranch →
      StmtListCompileCore scope rest →
      StmtListTerminalCore scope (.ite cond thenBranch elseBranch :: rest)

end FunctionBody

end Compiler.Proofs.IRGeneration
