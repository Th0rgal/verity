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

private def mappingSlotFunc : YulStmt :=
  YulStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "key"]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, YulExpr.ident "baseSlot"]),
    YulStmt.assign "slot" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 64])
  ]

private def buildSwitch (funcs : List IRFunction) : YulStmt :=
  let selectorExpr := YulExpr.call "shr" [YulExpr.lit 224, YulExpr.call "calldataload" [YulExpr.lit 0]]
  let cases := funcs.map (fun fn =>
    let body := [YulStmt.comment s!"{fn.name}()"] ++ fn.body
    (fn.selector, body)
  )
  YulStmt.switch selectorExpr cases (some [
    YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
  ])

private def runtimeCode (contract : IRContract) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFunc] else []
  mapping ++ [buildSwitch contract.functions]

private def deployCode (contract : IRContract) : List YulStmt :=
  contract.deploy ++ [yulDatacopy, yulReturnRuntime]

def emitYul (contract : IRContract) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCode contract }

end Compiler
