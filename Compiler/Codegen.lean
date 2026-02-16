import Compiler.IR
import Compiler.Yul.PrettyPrint

namespace Compiler

open Yul

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

def buildSwitch (funcs : List IRFunction) : YulStmt :=
  let selectorExpr := YulExpr.call "shr" [YulExpr.lit 224, YulExpr.call "calldataload" [YulExpr.lit 0]]
  let cases := funcs.map (fun fn =>
    let body := [YulStmt.comment s!"{fn.name}()"] ++
      [callvalueGuard] ++ [calldatasizeGuard fn.params.length] ++ fn.body
    (fn.selector, body)
  )
  YulStmt.switch selectorExpr cases (some [
    YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
  ])

def runtimeCode (contract : IRContract) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFunc] else []
  mapping ++ [buildSwitch contract.functions]

private def deployCode (contract : IRContract) : List YulStmt :=
  contract.deploy ++ [yulDatacopy, yulReturnRuntime]

def emitYul (contract : IRContract) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCode contract }

end Compiler
