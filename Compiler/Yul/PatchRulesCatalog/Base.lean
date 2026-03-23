import Compiler.Yul.PatchFramework

namespace Compiler.Yul

/-- `or(x, 0) -> x` -/
def orZeroRightRule : ExprPatchRule :=
  { patchName := "or-zero-right"
    pattern := "or(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 100
    applyExpr := fun _ expr =>
      match expr with
      | .call "or" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `or(0, x) -> x` -/
def orZeroLeftRule : ExprPatchRule :=
  { patchName := "or-zero-left"
    pattern := "or(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_left_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 95
    applyExpr := fun _ expr =>
      match expr with
      | .call "or" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `xor(x, 0) -> x` -/
def xorZeroRightRule : ExprPatchRule :=
  { patchName := "xor-zero-right"
    pattern := "xor(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.xor_zero_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 90
    applyExpr := fun _ expr =>
      match expr with
      | .call "xor" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `xor(0, x) -> x` -/
def xorZeroLeftRule : ExprPatchRule :=
  { patchName := "xor-zero-left"
    pattern := "xor(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.xor_zero_left_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 85
    applyExpr := fun _ expr =>
      match expr with
      | .call "xor" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `and(x, 0) -> 0` -/
def andZeroRightRule : ExprPatchRule :=
  { patchName := "and-zero-right"
    pattern := "and(x, 0)"
    rewrite := "0"
    sideConditions := ["second argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.and_zero_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 80
    applyExpr := fun _ expr =>
      match expr with
      | .call "and" [_lhs, .lit 0] => some (.lit 0)
      | _ => none }

/-- `add(x, 0) -> x` -/
def addZeroRightRule : ExprPatchRule :=
  { patchName := "add-zero-right"
    pattern := "add(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.add_zero_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 75
    applyExpr := fun _ expr =>
      match expr with
      | .call "add" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `add(0, x) -> x` -/
def addZeroLeftRule : ExprPatchRule :=
  { patchName := "add-zero-left"
    pattern := "add(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.add_zero_left_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 74
    applyExpr := fun _ expr =>
      match expr with
      | .call "add" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `sub(x, 0) -> x` -/
def subZeroRightRule : ExprPatchRule :=
  { patchName := "sub-zero-right"
    pattern := "sub(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.sub_zero_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 73
    applyExpr := fun _ expr =>
      match expr with
      | .call "sub" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `mul(x, 1) -> x` -/
def mulOneRightRule : ExprPatchRule :=
  { patchName := "mul-one-right"
    pattern := "mul(x, 1)"
    rewrite := "x"
    sideConditions := ["second argument is literal one"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.mul_one_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 72
    applyExpr := fun _ expr =>
      match expr with
      | .call "mul" [lhs, .lit 1] => some lhs
      | _ => none }

/-- `mul(1, x) -> x` -/
def mulOneLeftRule : ExprPatchRule :=
  { patchName := "mul-one-left"
    pattern := "mul(1, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal one"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.mul_one_left_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 71
    applyExpr := fun _ expr =>
      match expr with
      | .call "mul" [.lit 1, rhs] => some rhs
      | _ => none }

/-- `div(x, 1) -> x` -/
def divOneRightRule : ExprPatchRule :=
  { patchName := "div-one-right"
    pattern := "div(x, 1)"
    rewrite := "x"
    sideConditions := ["second argument is literal one"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.div_one_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 70
    applyExpr := fun _ expr =>
      match expr with
      | .call "div" [lhs, .lit 1] => some lhs
      | _ => none }

/-- `mod(x, 1) -> 0` -/
def modOneRightRule : ExprPatchRule :=
  { patchName := "mod-one-right"
    pattern := "mod(x, 1)"
    rewrite := "0"
    sideConditions := ["second argument is literal one"]
    proofId := proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.mod_one_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 69
    applyExpr := fun _ expr =>
      match expr with
      | .call "mod" [_lhs, .lit 1] => some (.lit 0)
      | _ => none }

/-- Initial deterministic, proven-safe expression patch pack (Issue #583 expansion). -/
def foundationExprPatchPack : List ExprPatchRule :=
  [ orZeroRightRule
  , orZeroLeftRule
  , xorZeroRightRule
  , xorZeroLeftRule
  , andZeroRightRule
  , addZeroRightRule
  , addZeroLeftRule
  , subZeroRightRule
  , mulOneRightRule
  , mulOneLeftRule
  , divOneRightRule
  , modOneRightRule
  ]

/-- Initial deterministic statement patch pack.
    Intentionally empty until the first proof-carrying statement rewrites land. -/
def foundationStmtPatchPack : List StmtPatchRule :=
  []

/-- Initial deterministic block patch pack.
    Intentionally empty until the first proof-carrying block rewrites land. -/
def foundationBlockPatchPack : List BlockPatchRule :=
  []

/-- Initial deterministic object patch pack.
    Intentionally empty until the first proof-carrying object rewrites land. -/
def foundationObjectPatchPack : List ObjectPatchRule :=
  []

private def appendUniqueString (xs : List String) (item : String) : List String :=
  if xs.any (fun seen => seen = item) then xs else xs ++ [item]

private def unionUniqueStrings (xs ys : List String) : List String :=
  ys.foldl (fun acc item => appendUniqueString acc item) xs

mutual

private partial def callNamesInExpr : YulExpr → List String
  | .call func args =>
      let argCalls := callNamesInExprs args
      appendUniqueString argCalls func
  | _ => []

private partial def callNamesInExprs : List YulExpr → List String
  | [] => []
  | expr :: rest =>
      unionUniqueStrings (callNamesInExpr expr) (callNamesInExprs rest)

partial def callNamesInStmt : YulStmt → List String
  | .comment _ => []
  | .let_ _ value => callNamesInExpr value
  | .letMany _ value => callNamesInExpr value
  | .assign _ value => callNamesInExpr value
  | .expr value => callNamesInExpr value
  | .leave => []
  | .if_ cond body =>
      unionUniqueStrings (callNamesInExpr cond) (callNamesInStmts body)
  | .for_ init cond post body =>
      unionUniqueStrings
        (callNamesInStmts init)
        (unionUniqueStrings (callNamesInExpr cond) (unionUniqueStrings (callNamesInStmts post) (callNamesInStmts body)))
  | .switch expr cases default =>
      let caseCalls :=
        cases.foldl (fun acc (_, body) => unionUniqueStrings acc (callNamesInStmts body)) []
      let defaultCalls :=
        match default with
        | some body => callNamesInStmts body
        | none => []
      unionUniqueStrings (callNamesInExpr expr) (unionUniqueStrings caseCalls defaultCalls)
  | .block stmts => callNamesInStmts stmts
  | .funcDef _ _ _ body => callNamesInStmts body

partial def callNamesInStmts : List YulStmt → List String
  | [] => []
  | stmt :: rest =>
      unionUniqueStrings (callNamesInStmt stmt) (callNamesInStmts rest)

private partial def callNamesInStmtNoFuncDefs : YulStmt → List String
  | .comment _ => []
  | .expr expr => callNamesInExpr expr
  | .let_ _ expr => callNamesInExpr expr
  | .letMany _ expr => callNamesInExpr expr
  | .assign _ expr => callNamesInExpr expr
  | .leave => []
  | .if_ cond body =>
      unionUniqueStrings (callNamesInExpr cond) (callNamesInStmtsNoFuncDefs body)
  | .for_ init cond post body =>
      unionUniqueStrings
        (callNamesInStmtsNoFuncDefs init)
        (unionUniqueStrings
          (callNamesInExpr cond)
          (unionUniqueStrings
            (callNamesInStmtsNoFuncDefs post)
            (callNamesInStmtsNoFuncDefs body)))
  | .switch expr cases default =>
      let caseCalls :=
        cases.foldl (fun acc (_, body) => unionUniqueStrings acc (callNamesInStmtsNoFuncDefs body)) []
      let defaultCalls :=
        match default with
        | some body => callNamesInStmtsNoFuncDefs body
        | none => []
      unionUniqueStrings (callNamesInExpr expr) (unionUniqueStrings caseCalls defaultCalls)
  | .block stmts => callNamesInStmtsNoFuncDefs stmts
  | .funcDef _ _ _ _ => []

partial def callNamesInStmtsNoFuncDefs : List YulStmt → List String
  | [] => []
  | stmt :: rest =>
      unionUniqueStrings (callNamesInStmtNoFuncDefs stmt) (callNamesInStmtsNoFuncDefs rest)

end

private def topLevelFunctionDefs (stmts : List YulStmt) : List (String × List YulStmt) :=
  stmts.foldr
    (fun stmt acc =>
      match stmt with
      | .funcDef name _ _ body => (name, body) :: acc
      | _ => acc)
    []

private def topLevelNonFunctionStmts (stmts : List YulStmt) : List YulStmt :=
  stmts.foldr
    (fun stmt acc =>
      match stmt with
      | .funcDef _ _ _ _ => acc
      | _ => stmt :: acc)
    []

private def filterDefinedNames (definedNames : List String) (candidates : List String) : List String :=
  candidates.foldl
    (fun acc name =>
      if definedNames.any (fun defined => defined = name) then
        appendUniqueString acc name
      else
        acc)
    []

private partial def reachableHelperNamesFrom
    (defs : List (String × List YulStmt))
    (definedNames : List String)
    (fuel : Nat)
    (reachable : List String) : List String :=
  match fuel with
  | 0 => reachable
  | fuel + 1 =>
      let expanded :=
        reachable.foldl
          (fun acc name =>
            match defs.find? (fun defn => defn.fst = name) with
            | some (_, body) =>
                unionUniqueStrings acc (filterDefinedNames definedNames (callNamesInStmts body))
            | none => acc)
          reachable
      if expanded.length = reachable.length then
        reachable
      else
        reachableHelperNamesFrom defs definedNames fuel expanded

private def reachableTopLevelHelperNames (stmts : List YulStmt) : List String :=
  let defs := topLevelFunctionDefs stmts
  let definedNames := defs.map Prod.fst
  let seed := filterDefinedNames definedNames (callNamesInStmtsNoFuncDefs (topLevelNonFunctionStmts stmts))
  reachableHelperNamesFrom defs definedNames (defs.length + 1) seed

def pruneUnreachableTopLevelHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  let reachable := reachableTopLevelHelperNames topStmts
  let (prunedTopStmts, removed) :=
    topStmts.foldr
    (fun stmt (accStmts, removed) =>
      match stmt with
      | .funcDef name params rets body =>
          if reachable.any (fun seen => seen = name) then
            (.funcDef name params rets body :: accStmts, removed)
          else
            (accStmts, removed + 1)
      | _ =>
          (stmt :: accStmts, removed))
    ([], 0)
  if wrapped then
    ([.block prunedTopStmts], removed)
  else
    (prunedTopStmts, removed)

private def solcCompatFunAliasTarget? (name : String) : Option String :=
  if name.startsWith "internal__" then
    some s!"fun_{name.drop 10}"
  else
    none

private def renameTargetFor (renames : List (String × String)) (name : String) : String :=
  match renames.find? (fun entry => entry.fst = name) with
  | some entry => entry.snd
  | none => name

private def solcCompatInternalFunRenameMap (stmts : List YulStmt) : List (String × String) :=
  let definedNames := topLevelFunctionDefs stmts |>.map Prod.fst
  definedNames.foldl
    (fun acc name =>
      match solcCompatFunAliasTarget? name with
      | none => acc
      | some target =>
          let targetAlreadyDefined := definedNames.any (fun seen => seen = target)
          let targetAlreadyAssigned := acc.any (fun entry => entry.snd = target)
          if targetAlreadyDefined || targetAlreadyAssigned then
            acc
          else
            acc ++ [(name, target)])
    []

mutual

private partial def renameCallsInExpr (renames : List (String × String)) : YulExpr → YulExpr
  | .lit n => .lit n
  | .hex n => .hex n
  | .str s => .str s
  | .ident name => .ident name
  | .call func args =>
      .call (renameTargetFor renames func) (renameCallsInExprs renames args)

private partial def renameCallsInExprs (renames : List (String × String)) : List YulExpr → List YulExpr
  | [] => []
  | expr :: rest => renameCallsInExpr renames expr :: renameCallsInExprs renames rest

partial def renameCallsInStmt (renames : List (String × String)) : YulStmt → YulStmt
  | .comment text => .comment text
  | .let_ name value => .let_ name (renameCallsInExpr renames value)
  | .letMany names value => .letMany names (renameCallsInExpr renames value)
  | .assign name value => .assign name (renameCallsInExpr renames value)
  | .expr value => .expr (renameCallsInExpr renames value)
  | .leave => .leave
  | .if_ cond body =>
      .if_ (renameCallsInExpr renames cond) (renameCallsInStmts renames body)
  | .for_ init cond post body =>
      .for_
        (renameCallsInStmts renames init)
        (renameCallsInExpr renames cond)
        (renameCallsInStmts renames post)
        (renameCallsInStmts renames body)
  | .switch expr cases default =>
      .switch
        (renameCallsInExpr renames expr)
        (cases.map (fun (tag, body) => (tag, renameCallsInStmts renames body)))
        (default.map (renameCallsInStmts renames))
  | .block stmts => .block (renameCallsInStmts renames stmts)
  | .funcDef name params rets body =>
      .funcDef (renameTargetFor renames name) params rets (renameCallsInStmts renames body)

partial def renameCallsInStmts (renames : List (String × String)) : List YulStmt → List YulStmt
  | [] => []
  | stmt :: rest => renameCallsInStmt renames stmt :: renameCallsInStmts renames rest

end

def canonicalizeInternalFunNames (stmts : List YulStmt) : List YulStmt × Nat :=
  let renames := solcCompatInternalFunRenameMap stmts
  if renames.isEmpty then
    (stmts, 0)
  else
    (renameCallsInStmts renames stmts, renames.length)

private def dispatchLabelFunctionName? (label : String) : Option String :=
  if label = "fallback()" || label = "receive()" then
    none
  else if label.endsWith "()" then
    let raw := label.dropRight 2
    if raw.isEmpty then none else some raw
  else
    none

def topLevelFunctionNames (stmts : List YulStmt) : List String :=
  (topLevelFunctionDefs stmts).map Prod.fst

private def appendUniqueHelperDef
    (defs : List (String × List YulStmt))
    (name : String)
    (body : List YulStmt) : List (String × List YulStmt) :=
  if defs.any (fun entry => entry.1 = name) then
    defs
  else
    defs ++ [(name, body)]

private def helperDefsToStmts (defs : List (String × List YulStmt)) : List YulStmt :=
  defs.map (fun entry => .funcDef entry.1 [] [] entry.2)

private def insertTopLevelHelpersAfterPrefix
    (stmts : List YulStmt)
    (defs : List (String × List YulStmt)) : List YulStmt :=
  let rec splitPrefix : List YulStmt → List YulStmt × List YulStmt
    | [] => ([], [])
    | stmt :: rest =>
        match stmt with
        | .funcDef _ _ _ _ =>
            let (pref, suff) := splitPrefix rest
            (stmt :: pref, suff)
        | _ => ([], stmt :: rest)
  let (pref, suff) := splitPrefix stmts
  pref ++ helperDefsToStmts defs ++ suff

mutual

private partial def outlineDispatchCasesInStmt
    (knownDefs : List String)
    (stmt : YulStmt) : YulStmt × List (String × List YulStmt) × List String
  := match stmt with
    | .comment text => (.comment text, [], knownDefs)
    | .let_ name value => (.let_ name value, [], knownDefs)
    | .letMany names value => (.letMany names value, [], knownDefs)
    | .assign name value => (.assign name value, [], knownDefs)
    | .expr value => (.expr value, [], knownDefs)
    | .leave => (.leave, [], knownDefs)
    | .if_ cond body =>
        let (body', defs, knownDefs') := outlineDispatchCasesInStmts knownDefs body
        (.if_ cond body', defs, knownDefs')
    | .for_ init cond post body =>
        let (init', initDefs, knownAfterInit) := outlineDispatchCasesInStmts knownDefs init
        let (post', postDefs, knownAfterPost) := outlineDispatchCasesInStmts knownAfterInit post
        let (body', bodyDefs, knownAfterBody) := outlineDispatchCasesInStmts knownAfterPost body
        (.for_ init' cond post' body',
          initDefs ++ postDefs ++ bodyDefs,
          knownAfterBody)
    | .switch expr cases default =>
        let rec rewriteCases
            (remaining : List (Nat × List YulStmt))
            (known : List String)
            (accCases : List (Nat × List YulStmt))
            (accDefs : List (String × List YulStmt))
            : List (Nat × List YulStmt) × List (String × List YulStmt) × List String :=
          match remaining with
          | [] => (accCases.reverse, accDefs, known)
          | (tag, body) :: rest =>
              let (body', nestedDefs, knownAfterBody) := outlineDispatchCasesInStmts known body
              let knownWithNested :=
                nestedDefs.foldl (fun acc entry => appendUniqueString acc entry.1) knownAfterBody
              let nestedMerged :=
                nestedDefs.foldl (fun acc entry => appendUniqueHelperDef acc entry.1 entry.2) accDefs
              match body' with
              | .comment label :: restBody =>
                  match dispatchLabelFunctionName? label with
                  | some baseName =>
                      let helperName := s!"fun_{baseName}"
                      if knownWithNested.any (fun seen => seen = helperName) then
                        rewriteCases rest knownWithNested ((tag, body') :: accCases) nestedMerged
                      else
                        let defs' := appendUniqueHelperDef nestedMerged helperName restBody
                        let known' := appendUniqueString knownWithNested helperName
                        rewriteCases rest known' ((tag, [.expr (.call helperName [])]) :: accCases) defs'
                  | none =>
                      rewriteCases rest knownWithNested ((tag, body') :: accCases) nestedMerged
              | _ =>
                  rewriteCases rest knownWithNested ((tag, body') :: accCases) nestedMerged
        let (cases', defsFromCases, knownAfterCases) := rewriteCases cases knownDefs [] []
        let (default', defsFromDefault, knownAfterDefault) :=
          match default with
          | some body =>
              let (body', defs, known') := outlineDispatchCasesInStmts knownAfterCases body
              (some body', defs, known')
          | none => (none, [], knownAfterCases)
        let defsAll :=
          defsFromDefault.foldl (fun acc entry => appendUniqueHelperDef acc entry.1 entry.2) defsFromCases
        (.switch expr cases' default', defsAll, knownAfterDefault)
    | .block stmts =>
        let (stmts', defs, knownDefs') := outlineDispatchCasesInStmts knownDefs stmts
        (.block stmts', defs, knownDefs')
    | .funcDef name params rets body =>
        let (body', defs, knownDefs') := outlineDispatchCasesInStmts knownDefs body
        (.funcDef name params rets body', defs, knownDefs')

private partial def outlineDispatchCasesInStmts
    (knownDefs : List String)
    (stmts : List YulStmt) : List YulStmt × List (String × List YulStmt) × List String
  := match stmts with
    | [] => ([], [], knownDefs)
    | stmt :: rest =>
        let (stmt', defsHead, knownAfterHead) := outlineDispatchCasesInStmt knownDefs stmt
        let (rest', defsTail, knownAfterTail) := outlineDispatchCasesInStmts knownAfterHead rest
        let defs :=
          defsTail.foldl (fun acc entry => appendUniqueHelperDef acc entry.1 entry.2) defsHead
        (stmt' :: rest', defs, knownAfterTail)

end

def outlineRuntimeDispatchHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let known := topLevelFunctionNames stmts
  let (rewritten, helperDefs, _) := outlineDispatchCasesInStmts known stmts
  if helperDefs.isEmpty then
    (stmts, 0)
  else
    (insertTopLevelHelpersAfterPrefix rewritten helperDefs, helperDefs.length)

def topLevelZeroArityFunctionBodies (stmts : List YulStmt) : List (String × List YulStmt) :=
  stmts.foldr
    (fun stmt acc =>
      match stmt with
      | .funcDef name [] [] body => (name, body) :: acc
      | _ => acc)
    []

def helperBodyForName? (defs : List (String × List YulStmt)) (name : String) : Option (List YulStmt) :=
  match defs.find? (fun entry => entry.1 = name) with
  | some entry => some entry.2
  | none => none

mutual

private partial def inlineDispatchWrapperCallsInStmt
    (helpers : List (String × List YulStmt))
    (stmt : YulStmt) : YulStmt × Nat
  := match stmt with
    | .comment text => (.comment text, 0)
    | .let_ name value => (.let_ name value, 0)
    | .letMany names value => (.letMany names value, 0)
    | .assign name value => (.assign name value, 0)
    | .expr value => (.expr value, 0)
    | .leave => (.leave, 0)
    | .if_ cond body =>
        let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
        (.if_ cond body', rewritten)
    | .for_ init cond post body =>
        let (init', initRewrites) := inlineDispatchWrapperCallsInStmts helpers init
        let (post', postRewrites) := inlineDispatchWrapperCallsInStmts helpers post
        let (body', bodyRewrites) := inlineDispatchWrapperCallsInStmts helpers body
        (.for_ init' cond post' body', initRewrites + postRewrites + bodyRewrites)
    | .switch expr cases default =>
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          match body with
          | [.expr (.call helperName [])] =>
              if helperName.startsWith "fun_" then
                match helperBodyForName? helpers helperName with
                | some helperBody => ((tag, helperBody), 1)
                | none => ((tag, body), 0)
              else
                ((tag, body), 0)
          | _ =>
              let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
              ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewriteCount := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewriteCount) :=
          match default with
          | some body =>
              let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
              (some body', rewritten)
          | none => (none, 0)
        (.switch expr cases' default', caseRewriteCount + defaultRewriteCount)
    | .block stmts =>
        let (stmts', rewritten) := inlineDispatchWrapperCallsInStmts helpers stmts
        (.block stmts', rewritten)
    | .funcDef name params rets body =>
        let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
        (.funcDef name params rets body', rewritten)

private partial def inlineDispatchWrapperCallsInStmts
    (helpers : List (String × List YulStmt))
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := inlineDispatchWrapperCallsInStmt helpers stmt
        let (rest', rewrittenTail) := inlineDispatchWrapperCallsInStmts helpers rest
        (stmt' :: rest', rewrittenHead + rewrittenTail)

end

def inlineRuntimeDispatchWrapperCalls (stmts : List YulStmt) : List YulStmt × Nat :=
  let helpers := topLevelZeroArityFunctionBodies stmts
  inlineDispatchWrapperCallsInStmts helpers stmts

private def freshMappingSlotTemp (nextId : Nat) : String × Nat :=
  (s!"__compat_mapping_slot_{nextId}", nextId + 1)

mutual

private partial def inlineMappingSlotCallsInExpr
    (nextId : Nat)
    (expr : YulExpr) : List YulStmt × YulExpr × Nat × Nat
  := match expr with
    | .lit n => ([], .lit n, nextId, 0)
    | .hex n => ([], .hex n, nextId, 0)
    | .str s => ([], .str s, nextId, 0)
    | .ident name => ([], .ident name, nextId, 0)
    | .call "mappingSlot" [baseSlot, key] =>
        let (basePrefix, baseSlot', nextAfterBase, baseRewrites) := inlineMappingSlotCallsInExpr nextId baseSlot
        let (keyPrefix, key', nextAfterKey, keyRewrites) := inlineMappingSlotCallsInExpr nextAfterBase key
        let (tmpName, nextAfterTmp) := freshMappingSlotTemp nextAfterKey
        let preStmts :=
          basePrefix ++
            keyPrefix ++
              [ .expr (.call "mstore" [.lit 512, key'])
              , .expr (.call "mstore" [.lit 544, baseSlot'])
              , .let_ tmpName (.call "keccak256" [.lit 512, .lit 64])
              ]
        (preStmts, .ident tmpName, nextAfterTmp, baseRewrites + keyRewrites + 1)
    | .call func args =>
        let (preStmts, args', nextId', rewrites) := inlineMappingSlotCallsInExprs nextId args
        (preStmts, .call func args', nextId', rewrites)

private partial def inlineMappingSlotCallsInExprs
    (nextId : Nat)
    (exprs : List YulExpr) : List YulStmt × List YulExpr × Nat × Nat
  := match exprs with
    | [] => ([], [], nextId, 0)
    | expr :: rest =>
        let (prefixHead, exprHead, nextAfterHead, rewritesHead) := inlineMappingSlotCallsInExpr nextId expr
        let (prefixTail, exprTail, nextAfterTail, rewritesTail) := inlineMappingSlotCallsInExprs nextAfterHead rest
        (prefixHead ++ prefixTail, exprHead :: exprTail, nextAfterTail, rewritesHead + rewritesTail)

private partial def inlineMappingSlotCallsInStmt
    (nextId : Nat)
    (stmt : YulStmt) : List YulStmt × Nat × Nat
  := match stmt with
    | .comment text => ([.comment text], nextId, 0)
    | .let_ name value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.let_ name value'], nextId', rewrites)
    | .letMany names value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.letMany names value'], nextId', rewrites)
    | .assign name value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.assign name value'], nextId', rewrites)
    | .expr value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.expr value'], nextId', rewrites)
    | .leave => ([.leave], nextId, 0)
    | .if_ cond body =>
        let (condPrefix, cond', nextAfterCond, condRewrites) := inlineMappingSlotCallsInExpr nextId cond
        let (body', nextAfterBody, bodyRewrites) := inlineMappingSlotCallsInStmts nextAfterCond body
        (condPrefix ++ [.if_ cond' body'], nextAfterBody, condRewrites + bodyRewrites)
    | .for_ init cond post body =>
        let (init', nextAfterInit, initRewrites) := inlineMappingSlotCallsInStmts nextId init
        let (post', nextAfterPost, postRewrites) := inlineMappingSlotCallsInStmts nextAfterInit post
        let (body', nextAfterBody, bodyRewrites) := inlineMappingSlotCallsInStmts nextAfterPost body
        ([.for_ init' cond post' body'], nextAfterBody, initRewrites + postRewrites + bodyRewrites)
    | .switch expr cases default =>
        let (exprPrefix, expr', nextAfterExpr, exprRewrites) := inlineMappingSlotCallsInExpr nextId expr
        let rec rewriteCases
            (remaining : List (Nat × List YulStmt))
            (nextIdCases : Nat)
            (accCases : List (Nat × List YulStmt))
            (accRewrites : Nat)
            : List (Nat × List YulStmt) × Nat × Nat :=
          match remaining with
          | [] => (accCases.reverse, nextIdCases, accRewrites)
          | (tag, body) :: rest =>
              let (body', nextAfterBody, bodyRewrites) := inlineMappingSlotCallsInStmts nextIdCases body
              rewriteCases rest nextAfterBody ((tag, body') :: accCases) (accRewrites + bodyRewrites)
        let (cases', nextAfterCases, caseRewrites) := rewriteCases cases nextAfterExpr [] 0
        let (default', nextAfterDefault, defaultRewrites) :=
          match default with
          | some body =>
              let (body', nextBody, rewritten) := inlineMappingSlotCallsInStmts nextAfterCases body
              (some body', nextBody, rewritten)
          | none => (none, nextAfterCases, 0)
        (exprPrefix ++ [.switch expr' cases' default'], nextAfterDefault, exprRewrites + caseRewrites + defaultRewrites)
    | .block stmts =>
        let (stmts', nextId', rewrites) := inlineMappingSlotCallsInStmts nextId stmts
        ([.block stmts'], nextId', rewrites)
    | .funcDef name params rets body =>
        let (body', nextId', rewrites) := inlineMappingSlotCallsInStmts nextId body
        ([.funcDef name params rets body'], nextId', rewrites)

private partial def inlineMappingSlotCallsInStmts
    (nextId : Nat)
    (stmts : List YulStmt) : List YulStmt × Nat × Nat
  := match stmts with
    | [] => ([], nextId, 0)
    | stmt :: rest =>
        let (stmt', nextAfterStmt, rewritesHead) := inlineMappingSlotCallsInStmt nextId stmt
        let (rest', nextAfterRest, rewritesTail) := inlineMappingSlotCallsInStmts nextAfterStmt rest
        (stmt' ++ rest', nextAfterRest, rewritesHead + rewritesTail)

end

def inlineRuntimeMappingSlotCalls (stmts : List YulStmt) : List YulStmt × Nat :=
  let (stmts', _, rewritten) := inlineMappingSlotCallsInStmts 0 stmts
  (stmts', rewritten)

private def inlineKeccakMarketParamsLet?
    (name : String)
    (args : List YulExpr) : Option (List YulStmt) :=
  match args with
  | [loanToken, collateralToken, oracle, irm, lltv] =>
      some
        [ .expr (.call "mstore" [.lit 0, loanToken])
        , .expr (.call "mstore" [.lit 32, collateralToken])
        , .expr (.call "mstore" [.lit 64, oracle])
        , .expr (.call "mstore" [.lit 96, irm])
        , .expr (.call "mstore" [.lit 128, lltv])
        , .let_ name (.call "keccak256" [.lit 0, .lit 160])
        ]
  | _ => none

private def inlineKeccakMarketParamsAssign?
    (name : String)
    (args : List YulExpr) : Option (List YulStmt) :=
  match args with
  | [loanToken, collateralToken, oracle, irm, lltv] =>
      some
        [ .expr (.call "mstore" [.lit 0, loanToken])
        , .expr (.call "mstore" [.lit 32, collateralToken])
        , .expr (.call "mstore" [.lit 64, oracle])
        , .expr (.call "mstore" [.lit 96, irm])
        , .expr (.call "mstore" [.lit 128, lltv])
        , .assign name (.call "keccak256" [.lit 0, .lit 160])
        ]
  | _ => none

mutual

partial def inlineKeccakMarketParamsCallsInStmt
    (stmt : YulStmt) : List YulStmt × Nat
  := match stmt with
    | .comment text => ([.comment text], 0)
    | .let_ name (.call "keccakMarketParams" args) =>
        match inlineKeccakMarketParamsLet? name args with
        | some stmts => (stmts, 1)
        | none => ([stmt], 0)
    | .let_ _ _ => ([stmt], 0)
    | .letMany _ _ => ([stmt], 0)
    | .assign name (.call "keccakMarketParams" args) =>
        match inlineKeccakMarketParamsAssign? name args with
        | some stmts => (stmts, 1)
        | none => ([stmt], 0)
    | .assign _ _ => ([stmt], 0)
    | .expr _ => ([stmt], 0)
    | .leave => ([stmt], 0)
    | .if_ cond body =>
        let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
        ([.if_ cond body'], rewritten)
    | .for_ init cond post body =>
        let (init', initRewrites) := inlineKeccakMarketParamsCallsInStmts init
        let (post', postRewrites) := inlineKeccakMarketParamsCallsInStmts post
        let (body', bodyRewrites) := inlineKeccakMarketParamsCallsInStmts body
        ([.for_ init' cond post' body'], initRewrites + postRewrites + bodyRewrites)
    | .switch expr cases default =>
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
          ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewriteCount := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewriteCount) :=
          match default with
          | some body =>
              let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
              (some body', rewritten)
          | none => (none, 0)
        ([.switch expr cases' default'], caseRewriteCount + defaultRewriteCount)
    | .block stmts =>
        let (stmts', rewritten) := inlineKeccakMarketParamsCallsInStmts stmts
        ([.block stmts'], rewritten)
    | .funcDef name params rets body =>
        let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
        ([.funcDef name params rets body'], rewritten)

partial def inlineKeccakMarketParamsCallsInStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := inlineKeccakMarketParamsCallsInStmt stmt
        let (rest', rewrittenTail) := inlineKeccakMarketParamsCallsInStmts rest
        (stmt' ++ rest', rewrittenHead + rewrittenTail)

end

def inlineRuntimeKeccakMarketParamsCalls (stmts : List YulStmt) : List YulStmt × Nat :=
  inlineKeccakMarketParamsCallsInStmts stmts
