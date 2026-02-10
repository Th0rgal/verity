import Compiler.IR

namespace Compiler.Translate

open Compiler
open Compiler.Yul

private def addressMask : Nat := (2^160) - 1

private def lit (n : Nat) : YulExpr := YulExpr.lit n
private def hex (n : Nat) : YulExpr := YulExpr.hex n
private def ident (name : String) : YulExpr := YulExpr.ident name
private def call (fn : String) (args : List YulExpr) : YulExpr := YulExpr.call fn args

private def stmtLet (name : String) (value : YulExpr) : YulStmt := YulStmt.let_ name value
private def stmtAssign (name : String) (value : YulExpr) : YulStmt := YulStmt.assign name value
private def stmtExpr (e : YulExpr) : YulStmt := YulStmt.expr e
private def stmtIf (cond : YulExpr) (body : List YulStmt) : YulStmt := YulStmt.if_ cond body

private def sloadSlot (slot : Nat) : YulExpr := call "sload" [lit slot]
private def sstoreSlot (slot : Nat) (value : YulExpr) : YulStmt := stmtExpr (call "sstore" [lit slot, value])

private def calldataUint (offset : Nat) : YulExpr := call "calldataload" [lit offset]
private def calldataAddress (offset : Nat) : YulExpr := call "and" [call "calldataload" [lit offset], hex addressMask]

private def returnUint (value : YulExpr) : List YulStmt :=
  [stmtExpr (call "mstore" [lit 0, value]), stmtExpr (call "return" [lit 0, lit 32])]

private def stop : YulStmt := stmtExpr (call "stop" [])
private def revert0 : YulStmt := stmtExpr (call "revert" [lit 0, lit 0])

private def onlyOwnerCheck (ownerSlot : Nat) : List YulStmt :=
  [stmtIf (call "iszero" [call "eq" [call "caller" [], sloadSlot ownerSlot]]) [revert0]]

private def mappingSlot (baseSlot : Nat) (key : YulExpr) : YulExpr :=
  call "mappingSlot" [lit baseSlot, key]

private def mapLoad (baseSlot : Nat) (key : YulExpr) : YulExpr :=
  call "sload" [mappingSlot baseSlot key]

private def mapStore (baseSlot : Nat) (key : YulExpr) (value : YulExpr) : YulStmt :=
  stmtExpr (call "sstore" [mappingSlot baseSlot key, value])

private def fn (name : String) (selector : Nat) (params : List IRParam) (ret : IRType) (body : List YulStmt) : IRFunction :=
  { name := name, selector := selector, params := params, ret := ret, body := body }

private def uintParam (name : String) : IRParam := { name := name, ty := IRType.uint256 }
private def addrParam (name : String) : IRParam := { name := name, ty := IRType.address }

private def simpleStorageContract : IRContract :=
  let storeBody := [
    stmtLet "value" (calldataUint 4),
    sstoreSlot 0 (ident "value"),
    stop
  ]
  let retrieveBody := returnUint (sloadSlot 0)
  { name := "SimpleStorage"
    deploy := []
    functions := [
      fn "store" 0x6057361d [uintParam "value"] IRType.unit storeBody,
      fn "retrieve" 0x2e64cec1 [] IRType.uint256 retrieveBody
    ]
    usesMapping := false }

private def counterContract : IRContract :=
  let incrementBody := [
    stmtLet "current" (sloadSlot 0),
    sstoreSlot 0 (call "add" [ident "current", lit 1]),
    stop
  ]
  let decrementBody := [
    stmtLet "current" (sloadSlot 0),
    sstoreSlot 0 (call "sub" [ident "current", lit 1]),
    stop
  ]
  let getCountBody := returnUint (sloadSlot 0)
  { name := "Counter"
    deploy := []
    functions := [
      fn "increment" 0xd09de08a [] IRType.unit incrementBody,
      fn "decrement" 0x2baeceb7 [] IRType.unit decrementBody,
      fn "getCount" 0xa87d942c [] IRType.uint256 getCountBody
    ]
    usesMapping := false }

private def ownedContract : IRContract :=
  let transferBody :=
    onlyOwnerCheck 0 ++ [
      stmtLet "newOwner" (calldataAddress 4),
      sstoreSlot 0 (ident "newOwner"),
      stop
    ]
  let getOwnerBody := returnUint (sloadSlot 0)
  let deployBody := [
    stmtLet "argsOffset" (call "sub" [call "codesize" [], lit 32]),
    stmtExpr (call "codecopy" [lit 0, ident "argsOffset", lit 32]),
    stmtLet "initialOwner" (call "and" [call "mload" [lit 0], hex addressMask]),
    sstoreSlot 0 (ident "initialOwner")
  ]
  { name := "Owned"
    deploy := deployBody
    functions := [
      fn "transferOwnership" 0xf2fde38b [addrParam "newOwner"] IRType.unit transferBody,
      fn "getOwner" 0x893d20e8 [] IRType.address getOwnerBody
    ]
    usesMapping := false }

private def ownedCounterContract : IRContract :=
  let incrementBody :=
    onlyOwnerCheck 0 ++ [
      stmtLet "current" (sloadSlot 1),
      sstoreSlot 1 (call "add" [ident "current", lit 1]),
      stop
    ]
  let decrementBody :=
    onlyOwnerCheck 0 ++ [
      stmtLet "current" (sloadSlot 1),
      sstoreSlot 1 (call "sub" [ident "current", lit 1]),
      stop
    ]
  let getCountBody := returnUint (sloadSlot 1)
  let getOwnerBody := returnUint (sloadSlot 0)
  let transferBody :=
    onlyOwnerCheck 0 ++ [
      stmtLet "newOwner" (calldataAddress 4),
      sstoreSlot 0 (ident "newOwner"),
      stop
    ]
  let deployBody := [
    stmtLet "argsOffset" (call "sub" [call "codesize" [], lit 32]),
    stmtExpr (call "codecopy" [lit 0, ident "argsOffset", lit 32]),
    stmtLet "initialOwner" (call "and" [call "mload" [lit 0], hex addressMask]),
    sstoreSlot 0 (ident "initialOwner")
  ]
  { name := "OwnedCounter"
    deploy := deployBody
    functions := [
      fn "increment" 0xd09de08a [] IRType.unit incrementBody,
      fn "decrement" 0x2baeceb7 [] IRType.unit decrementBody,
      fn "getCount" 0xa87d942c [] IRType.uint256 getCountBody,
      fn "getOwner" 0x893d20e8 [] IRType.address getOwnerBody,
      fn "transferOwnership" 0xf2fde38b [addrParam "newOwner"] IRType.unit transferBody
    ]
    usesMapping := false }

private def ledgerContract : IRContract :=
  let depositBody := [
    stmtLet "sender" (call "caller" []),
    stmtLet "amount" (calldataUint 4),
    stmtLet "current" (mapLoad 0 (ident "sender")),
    mapStore 0 (ident "sender") (call "add" [ident "current", ident "amount"]),
    stop
  ]
  let withdrawBody := [
    stmtLet "sender" (call "caller" []),
    stmtLet "amount" (calldataUint 4),
    stmtLet "current" (mapLoad 0 (ident "sender")),
    stmtIf (call "lt" [ident "current", ident "amount"]) [revert0],
    mapStore 0 (ident "sender") (call "sub" [ident "current", ident "amount"]),
    stop
  ]
  let transferBody := [
    stmtLet "sender" (call "caller" []),
    stmtLet "to" (calldataAddress 4),
    stmtLet "amount" (calldataUint 36),
    stmtLet "senderBal" (mapLoad 0 (ident "sender")),
    stmtIf (call "lt" [ident "senderBal", ident "amount"]) [revert0],
    stmtLet "recipientBal" (mapLoad 0 (ident "to")),
    mapStore 0 (ident "sender") (call "sub" [ident "senderBal", ident "amount"]),
    mapStore 0 (ident "to") (call "add" [ident "recipientBal", ident "amount"]),
    stop
  ]
  let getBalanceBody := [
    stmtLet "addr" (calldataAddress 4)
  ] ++ returnUint (mapLoad 0 (ident "addr"))
  { name := "Ledger"
    deploy := []
    functions := [
      fn "deposit" 0xb6b55f25 [uintParam "amount"] IRType.unit depositBody,
      fn "withdraw" 0x2e1a7d4d [uintParam "amount"] IRType.unit withdrawBody,
      fn "transfer" 0xa9059cbb [addrParam "to", uintParam "amount"] IRType.unit transferBody,
      fn "getBalance" 0xf8b2cb4f [addrParam "addr"] IRType.uint256 getBalanceBody
    ]
    usesMapping := true }

private def simpleTokenContract : IRContract :=
  let mintBody :=
    onlyOwnerCheck 0 ++ [
      stmtLet "to" (calldataAddress 4),
      stmtLet "amount" (calldataUint 36),
      stmtLet "currentBal" (mapLoad 1 (ident "to")),
      mapStore 1 (ident "to") (call "add" [ident "currentBal", ident "amount"]),
      stmtLet "supply" (sloadSlot 2),
      sstoreSlot 2 (call "add" [ident "supply", ident "amount"]),
      stop
    ]
  let transferBody := [
    stmtLet "sender" (call "caller" []),
    stmtLet "to" (calldataAddress 4),
    stmtLet "amount" (calldataUint 36),
    stmtLet "senderBal" (mapLoad 1 (ident "sender")),
    stmtIf (call "lt" [ident "senderBal", ident "amount"]) [revert0],
    stmtLet "recipientBal" (mapLoad 1 (ident "to")),
    mapStore 1 (ident "sender") (call "sub" [ident "senderBal", ident "amount"]),
    mapStore 1 (ident "to") (call "add" [ident "recipientBal", ident "amount"]),
    stop
  ]
  let balanceOfBody := [stmtLet "addr" (calldataAddress 4)] ++ returnUint (mapLoad 1 (ident "addr"))
  let totalSupplyBody := returnUint (sloadSlot 2)
  let ownerBody := returnUint (sloadSlot 0)
  let deployBody := [
    stmtLet "argsOffset" (call "sub" [call "codesize" [], lit 32]),
    stmtExpr (call "codecopy" [lit 0, ident "argsOffset", lit 32]),
    stmtLet "initialOwner" (call "and" [call "mload" [lit 0], hex addressMask]),
    sstoreSlot 0 (ident "initialOwner"),
    sstoreSlot 2 (lit 0)
  ]
  { name := "SimpleToken"
    deploy := deployBody
    functions := [
      fn "mint" 0x40c10f19 [addrParam "to", uintParam "amount"] IRType.unit mintBody,
      fn "transfer" 0xa9059cbb [addrParam "to", uintParam "amount"] IRType.unit transferBody,
      fn "balanceOf" 0x70a08231 [addrParam "addr"] IRType.uint256 balanceOfBody,
      fn "totalSupply" 0x18160ddd [] IRType.uint256 totalSupplyBody,
      fn "owner" 0x8da5cb5b [] IRType.address ownerBody
    ]
    usesMapping := true }

private def safeCounterContract : IRContract :=
  let incrementBody := [
    stmtLet "current" (sloadSlot 0),
    stmtLet "result" (call "add" [ident "current", lit 1]),
    stmtIf (call "lt" [ident "result", ident "current"]) [revert0],
    sstoreSlot 0 (ident "result"),
    stop
  ]
  let decrementBody := [
    stmtLet "current" (sloadSlot 0),
    stmtIf (call "gt" [lit 1, ident "current"]) [revert0],
    stmtLet "result" (call "sub" [ident "current", lit 1]),
    sstoreSlot 0 (ident "result"),
    stop
  ]
  let getCountBody := returnUint (sloadSlot 0)
  { name := "SafeCounter"
    deploy := []
    functions := [
      fn "increment" 0xd09de08a [] IRType.unit incrementBody,
      fn "decrement" 0x2baeceb7 [] IRType.unit decrementBody,
      fn "getCount" 0xa87d942c [] IRType.uint256 getCountBody
    ]
    usesMapping := false }

private def contracts : List IRContract :=
  [ simpleStorageContract
  , counterContract
  , ownedContract
  , ownedCounterContract
  , ledgerContract
  , simpleTokenContract
  , safeCounterContract
  ]

def allContracts : List IRContract := contracts

end Compiler.Translate
