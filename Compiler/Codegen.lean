import Compiler.IR
import Compiler.Yul.PrettyPrint
import Compiler.Yul.PatchFramework
import Compiler.Yul.PatchRules

namespace Compiler

open Yul

structure YulEmitOptions where
  patchConfig : Yul.PatchPassConfig := { enabled := false }

/-- Runtime emission output plus patch audit report for tool/CI consumption. -/
structure RuntimeEmitReport where
  runtimeCode : List YulStmt
  patchReport : Yul.PatchPassReport

private def yulDatacopy : YulStmt :=
  YulStmt.expr (YulExpr.call "datacopy" [
    YulExpr.lit 0,
    YulExpr.call "dataoffset" [YulExpr.str "runtime"],
    YulExpr.call "datasize" [YulExpr.str "runtime"]
  ])

private def yulReturnRuntime : YulStmt :=
  YulStmt.expr (YulExpr.call "return" [
    YulExpr.lit 0,
    YulExpr.call "datasize" [YulExpr.str "runtime"]
  ])

def mappingSlotFunc : YulStmt :=
  YulStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "key"]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, YulExpr.ident "baseSlot"]),
    YulStmt.assign "slot" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 64])
  ]

/-- Revert if ETH is sent to a non-payable function. -/
def callvalueGuard : YulStmt :=
  YulStmt.if_ (YulExpr.call "callvalue" [])
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

/-- Revert if calldata is shorter than expected (4-byte selector + 32 bytes per param). -/
def calldatasizeGuard (numParams : Nat) : YulStmt :=
  YulStmt.if_ (YulExpr.call "lt" [
    YulExpr.call "calldatasize" [],
    YulExpr.lit (4 + numParams * 32)])
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

private def dispatchBody (payable : Bool) (label : String) (body : List YulStmt) : List YulStmt :=
  let valueGuard := if payable then [] else [callvalueGuard]
  [YulStmt.comment label] ++ valueGuard ++ body

private def defaultDispatchCase
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) : List YulStmt :=
  match receive, fallback with
  | none, none =>
      [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  | none, some fb =>
      dispatchBody fb.payable "fallback()" fb.body
  | some rc, none =>
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          (dispatchBody rc.payable "receive()" rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
      ]]
  | some rc, some fb =>
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          (dispatchBody rc.payable "receive()" rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          (dispatchBody fb.payable "fallback()" fb.body)
      ]]

def buildSwitch
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint := none)
    (receive : Option IREntrypoint := none) : YulStmt :=
  let selectorExpr := YulExpr.call "shr" [YulExpr.lit 224, YulExpr.call "calldataload" [YulExpr.lit 0]]
  let cases := funcs.map (fun fn =>
    let body := dispatchBody fn.payable s!"{fn.name}()" ([calldatasizeGuard fn.params.length] ++ fn.body)
    (fn.selector, body)
  )
  YulStmt.switch selectorExpr cases (some (defaultDispatchCase fallback receive))

def runtimeCode (contract : IRContract) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFunc] else []
  let internals := contract.internalFunctions
  mapping ++ internals ++ [buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint]

/-- Emit runtime code and keep the patch pass report (manifest + iteration count). -/
def runtimeCodeWithOptionsReport (contract : IRContract) (options : YulEmitOptions) : RuntimeEmitReport :=
  let base := runtimeCode contract
  let patchReport := Yul.runExprPatchPass options.patchConfig Yul.foundationExprPatchPack base
  { runtimeCode := patchReport.patched, patchReport := patchReport }

def runtimeCodeWithOptions (contract : IRContract) (options : YulEmitOptions) : List YulStmt :=
  (runtimeCodeWithOptionsReport contract options).runtimeCode

private def deployCode (contract : IRContract) : List YulStmt :=
  let valueGuard := if contract.constructorPayable then [] else [callvalueGuard]
  valueGuard ++ contract.deploy ++ [yulDatacopy, yulReturnRuntime]

def emitYul (contract : IRContract) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCode contract }

def emitYulWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCodeWithOptions contract options }

/-- Emit Yul and preserve patch-pass audit details for downstream reporting. -/
def emitYulWithOptionsReport (contract : IRContract) (options : YulEmitOptions) :
    YulObject × Yul.PatchPassReport :=
  let runtimeReport := runtimeCodeWithOptionsReport contract options
  ({ name := contract.name
     deployCode := deployCode contract
     runtimeCode := runtimeReport.runtimeCode },
   runtimeReport.patchReport)

/-- Regression guard: report and legacy runtime APIs stay in sync. -/
example (contract : IRContract) (options : YulEmitOptions) :
    (runtimeCodeWithOptionsReport contract options).runtimeCode = runtimeCodeWithOptions contract options := by
  rfl

/-- Regression guard: report and legacy object APIs stay in sync. -/
example (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport contract options).1 = emitYulWithOptions contract options := by
  rfl

/-- Regression guard: object report API returns the exact patch report from runtime emission. -/
example (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport contract options).2 =
      (runtimeCodeWithOptionsReport contract options).patchReport := by
  rfl

end Compiler
