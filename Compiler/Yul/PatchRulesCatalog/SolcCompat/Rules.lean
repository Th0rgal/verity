import Compiler.Yul.PatchRulesCatalog.SolcCompat.AccrueInterest

namespace Compiler.Yul

def solcCompatPruneUnreachableHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_prune_unreachable_helpers_preserves"

/-- Canonicalize Verity internal helper naming to `solc`-style `fun_*` names when collision-free. -/
def solcCompatCanonicalizeInternalFunNamesProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_canonicalize_internal_fun_names_preserves"

/-- Deduplicate top-level helper definitions that are structurally equivalent. -/
def solcCompatDedupeEquivalentHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_dedupe_equivalent_helpers_preserves"

/-- Inline dispatch wrapper case calls to top-level zero-arity `fun_*` helper definitions. -/
def solcCompatInlineDispatchWrapperCallsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_dispatch_wrapper_calls_preserves"

/-- Outline switch dispatch case bodies into explicit top-level `fun_*` helpers. -/
def solcCompatOutlineDispatchHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_outline_dispatch_helpers_preserves"

/-- Inline direct `keccakMarketParams(...)` helper calls into explicit memory writes + `keccak256`. -/
def solcCompatInlineKeccakMarketParamsCallsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_keccak_market_params_calls_preserves"

/-- Inline `mappingSlot(baseSlot, key)` helper calls into explicit scratch writes + `keccak256`. -/
def solcCompatInlineMappingSlotCallsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_mapping_slot_calls_preserves"

def solcCompatDropUnusedKeccakMarketParamsHelperProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_drop_unused_keccak_market_params_helper_preserves"

def solcCompatDropUnusedMappingSlotHelperProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_drop_unused_mapping_slot_helper_preserves"

def solcCompatPruneUnreachableDeployHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_prune_unreachable_deploy_helpers_preserves"

def solcCompatRewriteNonceIncrementProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_nonce_increment_preserves"

def solcCompatRewriteElapsedCheckedSubProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_elapsed_checked_sub_preserves"

def solcCompatRewriteAccrueInterestCheckedArithmeticProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_accrue_interest_checked_arithmetic_preserves"

def solcCompatRewriteAccrueInterestPrologueTempsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_accrue_interest_prologue_temps_preserves"

def solcCompatRewriteAccrueInterestIrmGuardProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_accrue_interest_irm_guard_preserves"

private def findEquivalentTopLevelHelper?
    (seen : List (String × List String × List String × String))
    (params rets : List String)
    (body : List YulStmt) : Option String :=
  let bodyKey : String := reprStr body
  match seen.find? (fun entry =>
      decide (entry.2.1 = params) && decide (entry.2.2.1 = rets) && decide (entry.2.2.2 = bodyKey)) with
  | some entry => some entry.1
  | none => none

private def dedupeEquivalentTopLevelHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let step := fun (acc : (List YulStmt × List (String × List String × List String × String) ×
      List (String × String) × Nat)) (stmt : YulStmt) =>
    let (keptRev, seen, renames, removed) := acc
    match stmt with
    | .funcDef name params rets body =>
        match findEquivalentTopLevelHelper? seen params rets body with
        | some canonical =>
            let renames' :=
              if canonical = name || renames.any (fun pair => pair.fst = name && pair.snd = canonical) then
                renames
              else
                renames ++ [(name, canonical)]
            (keptRev, seen, renames', removed + 1)
        | none =>
            (.funcDef name params rets body :: keptRev, (name, params, rets, reprStr body) :: seen, renames, removed)
    | _ =>
        (stmt :: keptRev, seen, renames, removed)
  let (keptRev, _, renames, removed) := stmts.foldl step ([], [], [], 0)
  let kept := keptRev.reverse
  if removed = 0 then
    (stmts, 0)
  else if renames.isEmpty then
    (kept, removed)
  else
    (renameCallsInStmts renames kept, removed)

private def dropUnusedTopLevelFunctionByName (stmts : List YulStmt) (name : String) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  let (withoutTarget, removed) :=
    topStmts.foldr
      (fun stmt (accStmts, accRemoved) =>
        match stmt with
        | .funcDef defName params rets body =>
            if defName = name then
              (accStmts, accRemoved + 1)
            else
              (.funcDef defName params rets body :: accStmts, accRemoved)
        | _ => (stmt :: accStmts, accRemoved))
      ([], 0)
  if removed = 0 then
    (stmts, 0)
  else if (callNamesInStmts withoutTarget).any (fun called => called = name) then
    (stmts, 0)
  else if wrapped then
    ([.block withoutTarget], removed)
  else
    (withoutTarget, removed)

/-- Canonicalize `internal__*` helper names to `fun_*` and rewrite in-object call sites.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatCanonicalizeInternalFunNamesRule : ObjectPatchRule :=
  { patchName := "solc-compat-canonicalize-internal-fun-names"
    pattern := "function internal__X(...) with in-object call sites"
    rewrite := "function fun_X(...) with updated in-object call sites"
    sideConditions :=
      [ "only top-level function names with prefix internal__ are considered"
      , "target fun_* name must not already be defined in the same object code list"
      , "if two internal__ names map to the same target, only the first is renamed" ]
    proofId := solcCompatCanonicalizeInternalFunNamesProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRenamed) := canonicalizeInternalFunNames obj.deployCode
      let (runtimeCode', runtimeRenamed) := canonicalizeInternalFunNames obj.runtimeCode
      if deployRenamed + runtimeRenamed = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Outline labeled runtime switch cases as explicit `fun_*` helper defs and dispatch via calls.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatOutlineDispatchHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-outline-dispatch-helpers"
    pattern := "runtime switch case body prefixed with comment `<name>()`"
    rewrite := "insert top-level `fun_<name>` helper and replace case body with helper call"
    sideConditions :=
      [ "only runtime code is transformed"
      , "labels `fallback()` and `receive()` are excluded"
      , "existing `fun_*` names are collision-safe and never overwritten"
      , "outlined helper parameters/returns are empty (dispatch shape only)" ]
    proofId := solcCompatOutlineDispatchHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 215
    applyObject := fun _ obj =>
      let (runtimeCode', outlined) := outlineRuntimeDispatchHelpers obj.runtimeCode
      if outlined = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Deduplicate top-level helper function defs that are structurally equivalent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDedupeEquivalentHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-dedupe-equivalent-helpers"
    pattern := "duplicate top-level helper defs with equivalent params/returns/body"
    rewrite := "retain first helper def, rewrite call sites to retained helper"
    sideConditions :=
      [ "only top-level function definitions are considered"
      , "equivalence requires exact params/returns/body structural equality"
      , "the first encountered equivalent helper is canonical" ]
    proofId := solcCompatDedupeEquivalentHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 205
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dedupeEquivalentTopLevelHelpers obj.deployCode
      let (runtimeCode', runtimeRemoved) := dedupeEquivalentTopLevelHelpers obj.runtimeCode
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Inline runtime switch case bodies of the form `fun_X()` to the corresponding zero-arity helper body.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineDispatchWrapperCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-dispatch-wrapper-calls"
    pattern := "runtime switch case body with a single call to `fun_*`"
    rewrite := "replace case body with the referenced top-level zero-arity helper body"
    sideConditions :=
      [ "only runtime code is transformed"
      , "case body must be exactly one statement: `fun_*()` call"
      , "target helper must be a top-level zero-arity definition in the same object" ]
    proofId := solcCompatInlineDispatchWrapperCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 212
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeDispatchWrapperCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Inline runtime direct `keccakMarketParams(...)` helper calls to `mstore`/`keccak256` sequence.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineKeccakMarketParamsCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-keccak-market-params-calls"
    pattern := "let/assign using direct call `keccakMarketParams(a,b,c,d,e)`"
    rewrite := "replace with explicit memory writes at [0,32,64,96,128] then `keccak256(0,160)`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only direct `.let_`/`.assign` calls are rewritten"
      , "exactly five arguments are required"
      , "scratch memory clobbering follows existing helper semantics" ]
    proofId := solcCompatInlineKeccakMarketParamsCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeKeccakMarketParamsCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Inline runtime `mappingSlot(baseSlot, key)` helper calls into explicit `mstore`/`keccak256`.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineMappingSlotCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-mapping-slot-calls"
    pattern := "expression call `mappingSlot(baseSlot, key)`"
    rewrite := "introduce scratch writes to [512,544] and replace call with a fresh slot temporary"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only calls with exactly two arguments are rewritten"
      , "loop-condition expressions are intentionally not rewritten"
      , "fresh temporary names use reserved prefix `__compat_mapping_slot_`"
      , "scratch memory clobbering follows existing `mappingSlot` helper semantics (base 512)" ]
    proofId := solcCompatInlineMappingSlotCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeMappingSlotCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Drop top-level runtime `keccakMarketParams` helper when no call sites remain.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDropUnusedKeccakMarketParamsHelperRule : ObjectPatchRule :=
  { patchName := "solc-compat-drop-unused-keccak-market-params-helper"
    pattern := "top-level helper definition `keccakMarketParams` with no remaining call sites"
    rewrite := "remove helper definition"
    sideConditions :=
      [ "deploy/runtime code is transformed"
      , "only top-level definitions named `keccakMarketParams` are considered"
      , "helper is removed only when no call site remains in the same object section" ]
    proofId := solcCompatDropUnusedKeccakMarketParamsHelperProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dropUnusedTopLevelFunctionByName obj.deployCode "keccakMarketParams"
      let (runtimeCode', runtimeRemoved) := dropUnusedTopLevelFunctionByName obj.runtimeCode "keccakMarketParams"
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Drop top-level runtime `mappingSlot` helper when no call sites remain.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDropUnusedMappingSlotHelperRule : ObjectPatchRule :=
  { patchName := "solc-compat-drop-unused-mapping-slot-helper"
    pattern := "top-level helper definition `mappingSlot` with no remaining call sites"
    rewrite := "remove helper definition"
    sideConditions :=
      [ "deploy/runtime code is transformed"
      , "only top-level definitions named `mappingSlot` are considered"
      , "helper is removed only when no call site remains in the same object section" ]
    proofId := solcCompatDropUnusedMappingSlotHelperProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dropUnusedTopLevelFunctionByName obj.deployCode "mappingSlot"
      let (runtimeCode', runtimeRemoved) := dropUnusedTopLevelFunctionByName obj.runtimeCode "mappingSlot"
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Rewrite nonce increments from `add(currentNonce, 1)` to `increment_uint256(currentNonce)`.
    Insert `increment_uint256` helper only when referenced and absent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteNonceIncrementRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-nonce-increment"
    pattern := "runtime expression `add(currentNonce, 1)`"
    rewrite := "replace with `increment_uint256(currentNonce)` and materialize helper if needed"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to identifier name `currentNonce`"
      , "helper insertion is top-level, deterministic, and only when absent" ]
    proofId := solcCompatRewriteNonceIncrementProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteCurrentNonceIncrementStmts obj.runtimeCode
      let (runtimeCode'', inserted) := materializeIncrementUint256HelperIfCalled runtimeCode'
      if rewritten + inserted = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode'' } }

/-- Rewrite `sub(timestamp(), prevLastUpdate)` to `checked_sub_uint256(timestamp(), prevLastUpdate)`.
    Insert `checked_sub_uint256` helper only when referenced and absent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteElapsedCheckedSubRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-elapsed-checked-sub"
    pattern := "runtime expression `sub(timestamp(), prevLastUpdate)`"
    rewrite := "replace with `checked_sub_uint256(timestamp(), prevLastUpdate)` and materialize helper if needed"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to identifier name `prevLastUpdate`"
      , "helper insertion is top-level, deterministic, and only when absent" ]
    proofId := solcCompatRewriteElapsedCheckedSubProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteElapsedCheckedSubStmts obj.runtimeCode
      let (runtimeCode'', inserted) := materializeCheckedSubUint256HelperIfCalled runtimeCode'
      if rewritten + inserted = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode'' } }

/-- Rewrite selected runtime `accrueInterest` arithmetic patterns to
    Solidity-style checked helper calls (`checked_add_uint256` / `checked_add_uint128` /
    `checked_sub_uint128` / `checked_mul_uint256` / `checked_div_uint256`), plus
    explicit `fun_toUint128(...)` casts for selected uint128 add operands.
    Insert helpers only when referenced and absent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteAccrueInterestCheckedArithmeticRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-accrue-interest-checked-arithmetic"
    pattern := "selected runtime arithmetic and structural `accrueInterest` patterns, including uint128 cast and compat timestamp-write shape"
    rewrite := "replace with checked helper calls, canonical `accrueInterest` structural forms, and `fun_toUint128` casts, then materialize referenced helpers if needed"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to known identifier-shape arithmetic and guarded structural patterns in accrue-interest flow"
      , "helper insertion is top-level, deterministic, and only when absent" ]
    proofId := solcCompatRewriteAccrueInterestCheckedArithmeticProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts obj.runtimeCode
      let (runtimeCode'', inserted) := materializeCheckedAddMulDivUint256HelpersIfCalled runtimeCode'
      if rewritten + inserted = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode'' } }

/-- Rewrite runtime two-arg `fun_accrueInterest(var_marketParams_46531_mpos, var_id)` prologue
    into Solidity-style scratch-slot temp bindings (`_1.._5`) for deterministic parity.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteAccrueInterestPrologueTempsRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-accrue-interest-prologue-temps"
    pattern := "runtime `fun_accrueInterest` prologue with direct `mstore(512, var_id)` / `mstore(544, 3)` and compat slot-0 elapsed check"
    rewrite := "materialize Solidity-style `_1.._5` temps and canonicalize prevLastUpdate source to `and(sload(add(keccak256(_1, _5), 2)), _4)`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to `fun_accrueInterest(var_marketParams_46531_mpos, var_id)`"
      , "compat elapsed-check shape must match exactly"
      , "rewrite is skipped when `_1.._5` names are already locally bound" ]
    proofId := solcCompatRewriteAccrueInterestPrologueTempsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteAccrueInterestPrologueTempsStmts obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Rewrite runtime `accrueInterest` IRM non-zero guard shape to Solidity-style masked
    `cleaned` guard form. This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteAccrueInterestIrmGuardRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-accrue-interest-irm-guard"
    pattern := "runtime `if iszero(eq(mload(add(var_marketParams_*, 96)), 0))` guard"
    rewrite := "replace with masked `cleaned` temporary and `if iszero(iszero(cleaned))`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to `var_marketParams_*` pointer names"
      , "helper insertion remains unchanged" ]
    proofId := solcCompatRewriteAccrueInterestIrmGuardProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteAccrueInterestIrmGuardStmts obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Remove unreachable top-level helper function definitions in deploy/runtime code.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatPruneUnreachableHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-prune-unreachable-helpers"
    pattern := "object-level top-level helper function defs"
    rewrite := "remove helpers not reachable from non-function statements"
    sideConditions :=
      [ "only top-level function definitions are considered"
      , "reachability is computed transitively from non-function statements"
      , "helpers called by reachable helpers are retained" ]
    proofId := solcCompatPruneUnreachableHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 200
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := pruneUnreachableTopLevelHelpers obj.deployCode
      let (runtimeCode', runtimeRemoved) := pruneUnreachableTopLevelHelpers obj.runtimeCode
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Remove unreachable top-level helper function definitions in deploy code only.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatPruneUnreachableDeployHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-prune-unreachable-deploy-helpers"
    pattern := "deploy-level top-level helper function defs"
    rewrite := "remove deploy helpers not reachable from non-function deploy statements"
    sideConditions :=
      [ "only top-level function definitions in deploy code are considered"
      , "reachability is computed transitively from deploy non-function statements"
      , "runtime code is unchanged" ]
    proofId := solcCompatPruneUnreachableDeployHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 209
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := pruneUnreachableTopLevelHelpers obj.deployCode
      if deployRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode' } }

structure RewriteRuleBundle where
  id : String
  exprRules : List ExprPatchRule
  stmtRules : List StmtPatchRule
  blockRules : List BlockPatchRule
  objectRules : List ObjectPatchRule

private def rewriteBundleProofAllowlist (bundle : RewriteRuleBundle) : List Lean.Name :=
  let exprProofs := bundle.exprRules.map (fun rule => rule.proofId)
  let stmtProofs := bundle.stmtRules.map (fun rule => rule.proofId)
  let blockProofs := bundle.blockRules.map (fun rule => rule.proofId)
  let objectProofs := bundle.objectRules.map (fun rule => rule.proofId)
  let allProofs := exprProofs ++ stmtProofs ++ blockProofs ++ objectProofs
  allProofs.foldl
    (fun acc proofRef => if acc.any (fun seen => seen = proofRef) then acc else acc ++ [proofRef])
    []

def foundationRewriteBundleId : String := "foundation"

def solcCompatRewriteBundleId : String := "solc-compat-v0"

/-- Baseline, non-compat rewrite bundle. -/
def foundationRewriteBundle : RewriteRuleBundle :=
  { id := foundationRewriteBundleId
    exprRules := foundationExprPatchPack
    stmtRules := foundationStmtPatchPack
    blockRules := foundationBlockPatchPack
    objectRules := foundationObjectPatchPack }

/-- Opt-in `solc` compatibility rewrite bundle.
    Initially aliases foundation rules until dedicated compatibility rewrites land. -/
def solcCompatRewriteBundle : RewriteRuleBundle :=
  { id := solcCompatRewriteBundleId
    exprRules := foundationExprPatchPack
    stmtRules := foundationStmtPatchPack
    blockRules := foundationBlockPatchPack
    objectRules := foundationObjectPatchPack ++
      [ solcCompatCanonicalizeInternalFunNamesRule
      , solcCompatInlineDispatchWrapperCallsRule
      , solcCompatInlineMappingSlotCallsRule
      , solcCompatInlineKeccakMarketParamsCallsRule
      , solcCompatRewriteElapsedCheckedSubRule
      , solcCompatRewriteAccrueInterestIrmGuardRule
      , solcCompatRewriteAccrueInterestCheckedArithmeticRule
      , solcCompatRewriteAccrueInterestPrologueTempsRule
      , solcCompatRewriteNonceIncrementRule
      , solcCompatPruneUnreachableDeployHelpersRule
      , solcCompatDropUnusedMappingSlotHelperRule
      , solcCompatDropUnusedKeccakMarketParamsHelperRule
      , solcCompatDedupeEquivalentHelpersRule ] }

def allRewriteBundles : List RewriteRuleBundle :=
  [foundationRewriteBundle, solcCompatRewriteBundle]

def supportedRewriteBundleIds : List String :=
  allRewriteBundles.map (·.id)

def findRewriteBundle? (bundleId : String) : Option RewriteRuleBundle :=
  allRewriteBundles.find? (fun bundle => bundle.id = bundleId)

def rewriteBundleForId (bundleId : String) : RewriteRuleBundle :=
  match findRewriteBundle? bundleId with
  | some bundle => bundle
  | none => foundationRewriteBundle

def rewriteProofAllowlistForId (bundleId : String) : List Lean.Name :=
  rewriteBundleProofAllowlist (rewriteBundleForId bundleId)

/-- Activation-time proof allowlist for the shipped foundation patch packs. -/
def foundationProofAllowlist : List Lean.Name :=
  rewriteBundleProofAllowlist foundationRewriteBundle

/-- Activation-time proof allowlist for the shipped `solc` compatibility patch bundle. -/
def solcCompatProofAllowlist : List Lean.Name :=
  rewriteBundleProofAllowlist solcCompatRewriteBundle
