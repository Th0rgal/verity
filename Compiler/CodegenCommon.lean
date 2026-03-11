import Compiler.Constants
import Compiler.IR
import Compiler.Yul.PrettyPrint
import Compiler.Yul.PatchFramework

namespace Compiler.CodegenCommon

open Compiler.Constants (selectorShift)
open Compiler.Yul

inductive BackendProfile where
  | semantic
  | solidityParityOrdering
  | solidityParity
  deriving Repr, DecidableEq

instance : Inhabited BackendProfile where
  default := .semantic

structure YulEmitOptions where
  backendProfile : BackendProfile := .semantic
  patchConfig : PatchPassConfig := { enabled := false }
  /-- Scratch memory base used by compiler-generated mapping-slot helpers.
      Default `0` preserves historical behavior (`mstore(0, key); mstore(32, baseSlot)`). -/
  mappingSlotScratchBase : Nat := 0

structure RuntimeEmitReport where
  runtimeCode : List YulStmt
  patchReport : PatchPassReport

structure EmitObjectWithOptionsReport where
  patched : YulObject
  patchReport : PatchPassReport

structure PatchBackend where
  apply : YulObject → YulEmitOptions → EmitObjectWithOptionsReport

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

def mappingSlotFuncAt (scratchBase : Nat) : YulStmt :=
  let keyPtr := scratchBase
  let slotPtr := scratchBase + 32
  YulStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit keyPtr, YulExpr.ident "key"]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit slotPtr, YulExpr.ident "baseSlot"]),
    YulStmt.assign "slot" (YulExpr.call "keccak256" [YulExpr.lit keyPtr, YulExpr.lit 64])
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

def dispatchBody (payable : Bool) (label : String) (body : List YulStmt) : List YulStmt :=
  let valueGuard := if payable then [] else [callvalueGuard]
  [YulStmt.comment label] ++ valueGuard ++ body

def defaultDispatchCase
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

private def insertBy [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (x : α) : List α → List α
  | [] => [x]
  | head :: tail =>
      if key x < key head then x :: head :: tail
      else head :: insertBy key x tail

private def insertionSortBy [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy key x acc) []

def buildSwitch
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint := none)
    (receive : Option IREntrypoint := none)
    (sortCasesBySelector : Bool := false) : YulStmt :=
  let funcs :=
    if sortCasesBySelector then
      insertionSortBy (·.selector) funcs
    else
      funcs
  let selectorExpr := YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]]
  let cases := funcs.map (fun fn =>
    let body := dispatchBody fn.payable s!"{fn.name}()" ([calldatasizeGuard fn.params.length] ++ fn.body)
    (fn.selector, body)
  )
  let defaultCase := defaultDispatchCase fallback receive
  YulStmt.block [
    YulStmt.let_ "__has_selector"
      (YulExpr.call "iszero" [YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit 4]]),
    YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) defaultCase,
    YulStmt.if_ (YulExpr.ident "__has_selector")
      [YulStmt.switch selectorExpr cases (some defaultCase)]
  ]

def runtimeCode (contract : IRContract) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFuncAt 0] else []
  let internals := contract.internalFunctions
  mapping ++ internals ++ [buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint]

private def profileSortsOutput (profile : BackendProfile) : Bool :=
  match profile with
  | .semantic => false
  | .solidityParityOrdering => true
  | .solidityParity => true

private def profileSortsDispatchCases (profile : BackendProfile) : Bool :=
  profileSortsOutput profile

private def profileSortsInternalHelpers (profile : BackendProfile) : Bool :=
  profileSortsOutput profile

private def internalHelperName? (stmt : YulStmt) : Option String :=
  match stmt with
  | .funcDef name _ _ _ => some name
  | _ => none

private def sortInternalHelpersByName (helpers : List YulStmt) : List YulStmt :=
  let named := helpers.filterMap (fun stmt =>
    match internalHelperName? stmt with
    | some name => some (name, stmt)
    | none => none)
  if named.length == helpers.length then
    (insertionSortBy Prod.fst named).map Prod.snd
  else
    helpers

private def internalHelpersForProfile (profile : BackendProfile) (helpers : List YulStmt) : List YulStmt :=
  if profileSortsInternalHelpers profile then
    sortInternalHelpersByName helpers
  else
    helpers

private def runtimeCodeWithEmitOptions (contract : IRContract) (options : YulEmitOptions) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFuncAt options.mappingSlotScratchBase] else []
  let internals := internalHelpersForProfile options.backendProfile contract.internalFunctions
  let sortCases := profileSortsDispatchCases options.backendProfile
  let switchStmt := buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint sortCases
  mapping ++ internals ++ [switchStmt]

private def deployCodeWithProfile (contract : IRContract) (profile : BackendProfile)
    (mappingSlotScratchBase : Nat := 0) : List YulStmt :=
  let valueGuard := if contract.constructorPayable then [] else [callvalueGuard]
  let mapping := if contract.usesMapping then [mappingSlotFuncAt mappingSlotScratchBase] else []
  let internals := internalHelpersForProfile profile contract.internalFunctions
  valueGuard ++ mapping ++ internals ++ contract.deploy ++ [yulDatacopy, yulReturnRuntime]

private def deployCode (contract : IRContract) : List YulStmt :=
  deployCodeWithProfile contract .semantic

private def baseObjectWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  { name := contract.name
    deployCode := deployCodeWithProfile contract options.backendProfile options.mappingSlotScratchBase
    runtimeCode := runtimeCodeWithEmitOptions contract options }

private def runtimeCodeWithOptionsReport
    (backend : PatchBackend)
    (contract : IRContract)
    (options : YulEmitOptions) : RuntimeEmitReport :=
  let report := backend.apply (baseObjectWithOptions contract options) options
  { runtimeCode := report.patched.runtimeCode
    patchReport := report.patchReport }

private def runtimeCodeWithOptions
    (backend : PatchBackend)
    (contract : IRContract)
    (options : YulEmitOptions) : List YulStmt :=
  (runtimeCodeWithOptionsReport backend contract options).runtimeCode

def emitYul (contract : IRContract) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCode contract }

def emitYulWithOptions (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  (backend.apply (baseObjectWithOptions contract options) options).patched

def emitYulWithOptionsReport
    (backend : PatchBackend)
    (contract : IRContract)
    (options : YulEmitOptions) : YulObject × PatchPassReport :=
  let report := backend.apply (baseObjectWithOptions contract options) options
  (report.patched, report.patchReport)

example (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) :
    (runtimeCodeWithOptionsReport backend contract options).runtimeCode =
      runtimeCodeWithOptions backend contract options := by
  rfl

example (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport backend contract options).1 =
      emitYulWithOptions backend contract options := by
  rfl

example (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport backend contract options).2 =
      (runtimeCodeWithOptionsReport backend contract options).patchReport := by
  rfl

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
          if (c :: cs).take n.length == n then true
          else go cs
    go h

mutual
  private def stmtContainsSwitchCaseCall (target : String) : YulStmt → Bool
    | .comment _ => false
    | .let_ _ _ => false
    | .letMany _ _ => false
    | .assign _ _ => false
    | .expr _ => false
    | .leave => false
    | .if_ _ body => stmtListContainsSwitchCaseCall target body
    | .for_ init _ post body =>
        stmtListContainsSwitchCaseCall target init ||
        stmtListContainsSwitchCaseCall target post ||
        stmtListContainsSwitchCaseCall target body
    | .switch _ cases default =>
        let caseHit :=
          cases.any (fun (_, body) =>
            match body with
            | [.expr (.call fn [])] => decide (fn = target)
            | _ => false)
        let defaultHit :=
          match default with
          | some body => stmtListContainsSwitchCaseCall target body
          | none => false
        caseHit || defaultHit
    | .block stmts => stmtListContainsSwitchCaseCall target stmts
    | .funcDef _ _ _ body => stmtListContainsSwitchCaseCall target body
  termination_by stmt => sizeOf stmt

  private def stmtListContainsSwitchCaseCall (target : String) : List YulStmt → Bool
    | [] => false
    | stmt :: rest =>
        stmtContainsSwitchCaseCall target stmt || stmtListContainsSwitchCaseCall target rest
  termination_by stmts => sizeOf stmts
end

/-- Regression guard: solidity parity profile keeps dispatch inlined in switch cases. -/
example :
    let contract : IRContract :=
      { name := "DispatchOutlineRegression"
        deploy := []
        constructorPayable := true
        functions :=
          [{ name := "ping"
             selector := 1
             params := []
             ret := .unit
             payable := false
             body := [.leave] }]
        usesMapping := false
        internalFunctions := [] }
    let runtime := runtimeCodeWithEmitOptions contract { backendProfile := .solidityParity }
    let hasFunHelper :=
      runtime.any (fun stmt =>
        match stmt with
        | .funcDef "fun_ping" [] [] _ => true
        | _ => false)
    let switchCallsHelper := runtime.any (stmtContainsSwitchCaseCall "fun_ping")
    (!hasFunHelper) && (!switchCallsHelper) := by
  native_decide

end Compiler.CodegenCommon
