import DumbContracts.Lang
import DumbContracts.Yul

namespace DumbContracts.Compiler

open DumbContracts.Lang
open DumbContracts.Yul

def compileExpr : Lang.Expr -> Yul.Expr
  | Lang.Expr.lit n => Yul.Expr.lit n
  | Lang.Expr.var v => Yul.Expr.var v
  | Lang.Expr.add a b => Yul.Expr.call "add" [compileExpr a, compileExpr b]
  | Lang.Expr.sub a b => Yul.Expr.call "sub" [compileExpr a, compileExpr b]
  | Lang.Expr.mul a b => Yul.Expr.call "mul" [compileExpr a, compileExpr b]
  | Lang.Expr.div a b => Yul.Expr.call "div" [compileExpr a, compileExpr b]
  | Lang.Expr.eq a b => Yul.Expr.call "eq" [compileExpr a, compileExpr b]
  | Lang.Expr.lt a b => Yul.Expr.call "lt" [compileExpr a, compileExpr b]
  | Lang.Expr.gt a b => Yul.Expr.call "gt" [compileExpr a, compileExpr b]
  | Lang.Expr.and a b => Yul.Expr.call "and" [compileExpr a, compileExpr b]
  | Lang.Expr.or a b => Yul.Expr.call "or" [compileExpr a, compileExpr b]
  | Lang.Expr.not a => Yul.Expr.call "iszero" [compileExpr a]
  | Lang.Expr.sload k => Yul.Expr.call "sload" [compileExpr k]
  | Lang.Expr.calldataload k => Yul.Expr.call "calldataload" [compileExpr k]

def compileStmt : Lang.Stmt -> Yul.Stmt
  | Lang.Stmt.skip => Yul.Stmt.block []
  | Lang.Stmt.seq a b =>
      match compileStmt a, compileStmt b with
      | Yul.Stmt.block as, Yul.Stmt.block bs => Yul.Stmt.block (as ++ bs)
      | sa, sb => Yul.Stmt.block [sa, sb]
  | Lang.Stmt.let_ v e body =>
      Yul.Stmt.block [Yul.Stmt.let_ v (compileExpr e), compileStmt body]
  | Lang.Stmt.assign v e => Yul.Stmt.assign v (compileExpr e)
  | Lang.Stmt.if_ c t f =>
      Yul.Stmt.block [
        Yul.Stmt.if_ (compileExpr c) (compileStmt t),
        Yul.Stmt.if_ (Yul.Expr.call "iszero" [compileExpr c]) (compileStmt f)
      ]
  | Lang.Stmt.sstore k v => Yul.Stmt.expr (Yul.Expr.call "sstore" [compileExpr k, compileExpr v])
  | Lang.Stmt.revert => Yul.Stmt.expr (Yul.Expr.call "revert" [Yul.Expr.lit 0, Yul.Expr.lit 0])
  | Lang.Stmt.return_ v =>
      let storeRet := Yul.Stmt.expr (Yul.Expr.call "mstore" [Yul.Expr.lit 0, compileExpr v])
      let doRet := Yul.Stmt.expr (Yul.Expr.call "return" [Yul.Expr.lit 0, Yul.Expr.lit 32])
      Yul.Stmt.block [storeRet, doRet]

structure EntryPoint where
  name : String
  args : List String
  body : Lang.Stmt
  selector : Nat
  returns : Bool
  deriving Repr

def compileProgram (entries : List EntryPoint) : Yul.Program :=
  let mkFun (e : EntryPoint) : Yul.Stmt :=
    let funBody := match compileStmt e.body with
      | Yul.Stmt.block ss => Yul.Stmt.block ss
      | s => Yul.Stmt.block [s]
    Yul.Stmt.func e.name e.args [] funBody
  let selector :=
    Yul.Expr.call "shr" [
      Yul.Expr.lit 224,
      Yul.Expr.call "calldataload" [Yul.Expr.lit 0]
    ]
  let mkArg (i : Nat) : Yul.Expr :=
    Yul.Expr.call "calldataload" [Yul.Expr.lit (4 + 32 * i)]
  let mkCase (e : EntryPoint) : Nat × Yul.Stmt :=
    let args := (List.range e.args.length).map mkArg
    let callEntry := Yul.Stmt.expr (Yul.Expr.call e.name args)
    let stop := Yul.Stmt.expr (Yul.Expr.call "stop" [])
    let okCase := if e.returns then Yul.Stmt.block [callEntry] else Yul.Stmt.block [callEntry, stop]
    (e.selector, okCase)
  let cases := entries.map mkCase
  let badCase := Yul.Stmt.block [Yul.Stmt.expr (Yul.Expr.call "revert" [Yul.Expr.lit 0, Yul.Expr.lit 0])]
  let dispatcher := Yul.Stmt.switch selector cases badCase
  let code := Yul.Stmt.block ((entries.map mkFun) ++ [dispatcher])
  { obj := { name := "DumbContract", code := code } }

-- Single-entry wrapper.
def compileEntry (e : EntryPoint) : Yul.Program :=
  compileProgram [e]

-- Example entries.
def exampleEntry : EntryPoint :=
  { name := "getSlot"
    args := ["slot"]
    body := Lang.Stmt.return_ (Lang.Expr.sload (Lang.Expr.var "slot"))
    -- getSlot(uint256) -> 0x7eba7ba6
    selector := 0x7eba7ba6
    returns := true }

def exampleEntry2 : EntryPoint :=
  { name := "setSlot"
    args := ["slot", "value"]
    body := Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "value")
    -- setSlot(uint256,uint256) -> 0xf2c298be
    selector := 0xf2c298be
    returns := false }

def exampleEntry3 : EntryPoint :=
  { name := "addSlot"
    args := ["slot", "delta"]
    body := Lang.Stmt.sstore
      (Lang.Expr.var "slot")
      (Lang.Expr.add (Lang.Expr.sload (Lang.Expr.var "slot")) (Lang.Expr.var "delta"))
    -- addSlot(uint256,uint256) -> 0x02222aec
    selector := 0x02222aec
    returns := false }

def exampleEntry4 : EntryPoint :=
  { name := "guardedAddSlot"
    args := ["slot", "delta"]
    body := Lang.Stmt.if_
      (Lang.Expr.gt (Lang.Expr.var "delta") (Lang.Expr.lit 0))
      (Lang.Stmt.sstore
        (Lang.Expr.var "slot")
        (Lang.Expr.add (Lang.Expr.sload (Lang.Expr.var "slot")) (Lang.Expr.var "delta")))
      Lang.Stmt.revert
    -- guardedAddSlot(uint256,uint256) -> 0x49f583e3
    selector := 0x49f583e3
    returns := false }

def exampleEntry5 : EntryPoint :=
  { name := "maxStore"
    args := ["slot", "a", "b"]
    body := Lang.Stmt.if_
      (Lang.Expr.gt (Lang.Expr.var "a") (Lang.Expr.var "b"))
      (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "a"))
      (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "b"))
    -- maxStore(uint256,uint256,uint256) -> 0xb61d4088
    selector := 0xb61d4088
    returns := false }

def exampleEntry6 : EntryPoint :=
  { name := "setNonZero"
    args := ["slot", "value"]
    body := Lang.Stmt.if_
      (Lang.Expr.not (Lang.Expr.eq (Lang.Expr.var "value") (Lang.Expr.lit 0)))
      (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "value"))
      Lang.Stmt.revert
    -- setNonZero(uint256,uint256) -> 0xac1f1f67
    selector := 0xac1f1f67
    returns := false }

def exampleEntry7 : EntryPoint :=
  { name := "compareAndSwap"
    args := ["slot", "expected", "value"]
    body :=
      Lang.Stmt.let_ "current" (Lang.Expr.sload (Lang.Expr.var "slot"))
        (Lang.Stmt.if_
          (Lang.Expr.eq (Lang.Expr.var "current") (Lang.Expr.var "expected"))
          (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "value"))
          Lang.Stmt.revert)
    -- compareAndSwap(uint256,uint256,uint256) -> 0xc74962fa
    selector := 0xc74962fa
    returns := false }

def exampleEntry8 : EntryPoint :=
  { name := "setIfGreater"
    args := ["slot", "value", "min"]
    body :=
      Lang.Stmt.if_
        (Lang.Expr.gt (Lang.Expr.var "value") (Lang.Expr.var "min"))
        (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "value"))
        Lang.Stmt.revert
    -- setIfGreater(uint256,uint256,uint256) -> 0x2dbeb1ba
    selector := 0x2dbeb1ba
    returns := false }

def exampleEntry9 : EntryPoint :=
  { name := "bumpSlot"
    args := ["slot"]
    body :=
      Lang.Stmt.sstore
        (Lang.Expr.var "slot")
        (Lang.Expr.add (Lang.Expr.sload (Lang.Expr.var "slot")) (Lang.Expr.lit 1))
    -- bumpSlot(uint256) -> 0xb8df0e12
    selector := 0xb8df0e12
    returns := false }

def exampleEntry10 : EntryPoint :=
  { name := "setIfLess"
    args := ["slot", "value", "max"]
    body :=
      Lang.Stmt.if_
        (Lang.Expr.lt (Lang.Expr.var "value") (Lang.Expr.var "max"))
        (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "value"))
        Lang.Stmt.revert
    -- setIfLess(uint256,uint256,uint256) -> 0x7e5acdb6
    selector := 0x7e5acdb6
    returns := false }

def exampleEntry11 : EntryPoint :=
  { name := "setIfBetween"
    args := ["slot", "value", "min", "max"]
    body :=
      Lang.Stmt.if_
        (Lang.Expr.gt (Lang.Expr.var "value") (Lang.Expr.var "min"))
        (Lang.Stmt.if_
          (Lang.Expr.lt (Lang.Expr.var "value") (Lang.Expr.var "max"))
          (Lang.Stmt.sstore (Lang.Expr.var "slot") (Lang.Expr.var "value"))
          Lang.Stmt.revert)
        Lang.Stmt.revert
    -- setIfBetween(uint256,uint256,uint256,uint256) -> 0x5ebc58db
    selector := 0x5ebc58db
    returns := false }

def exampleEntries : List EntryPoint :=
  [exampleEntry, exampleEntry2, exampleEntry3, exampleEntry4, exampleEntry5, exampleEntry6, exampleEntry7,
    exampleEntry8, exampleEntry9, exampleEntry10, exampleEntry11]

def healthEntrySet : EntryPoint :=
  { name := "setRisk"
    args := ["collateral", "debt", "minHF"]
    body :=
      Lang.Stmt.sstore (Lang.Expr.lit 0) (Lang.Expr.var "collateral") ;;
      Lang.Stmt.sstore (Lang.Expr.lit 1) (Lang.Expr.var "debt") ;;
      Lang.Stmt.sstore (Lang.Expr.lit 2) (Lang.Expr.var "minHF")
    -- setRisk(uint256,uint256,uint256) -> 0xf978da39
    selector := 0xf978da39
    returns := false }

def healthEntryCheck : EntryPoint :=
  { name := "checkHealth"
    args := []
    body := Lang.Stmt.if_
      (Lang.Expr.lt (Lang.Expr.sload (Lang.Expr.lit 0))
        (Lang.Expr.mul (Lang.Expr.sload (Lang.Expr.lit 1)) (Lang.Expr.sload (Lang.Expr.lit 2))))
      Lang.Stmt.revert
      Lang.Stmt.skip
    -- checkHealth() -> 0x1753bbd7
    selector := 0x1753bbd7
    returns := false }

def healthEntries : List EntryPoint :=
  [healthEntrySet, healthEntryCheck]

end DumbContracts.Compiler
