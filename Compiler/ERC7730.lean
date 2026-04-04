/-
  Compiler.ERC7730: Generate ERC-7730 clear-signing JSON from IntentSpec.

  For each intent binding, produces a `display.formats` entry keyed by
  the 4-byte selector hex string.  The top-level JSON follows the
  ERC-7730 "Structured Data Clear Signing Format" schema:

    {
      "$schema": "...",
      "context": { "contract": { "deployments": [...], "abi": [...] } },
      "metadata": { ... },
      "display": {
        "formats": {
          "0xaabbccdd": {
            "$id": "functionName",
            "intent": "Human-readable intent string",
            "fields": [ ... ],
            "required": [ ... ]
          }
        }
      }
    }

  Phase 1: generates the `display` section from the IntentSpec.
  Context and metadata are emitted as stubs to be filled in per-deployment.

  See PR #1676 for the full design document.
-/
import Verity.Intent.Types
import Compiler.CompilationModel.Types
import Compiler.Json

namespace Compiler.ERC7730

open Verity.Intent
open Compiler.CompilationModel (ParamType)
open Compiler.Json

/-! ## Format Mapping

Map the intent DSL `Format` to ERC-7730 field format strings.
-/

/-- Map an intent DSL Format to an ERC-7730 format type string. -/
private def erc7730FormatType : Format → String
  | .raw => "raw"
  | .tokenAmount _ _ => "tokenAmount"
  | .address => "addressName"
  | .enum _ => "enum"

/-- Render the `params` object for a field, if applicable. -/
private def erc7730FormatParams : Format → Option String
  | .tokenAmount _decimals (some symbol) =>
    some (jsonObject [
      ("tokenPath", jsonString "$.metadata.token"),
      ("nativeCurrencyAddress", jsonString "eip155:1/slip44:60"),
      ("threshold", jsonString "0"),
      ("message", jsonString s!"Amount in {symbol}")
    ])
  | .tokenAmount _decimals none =>
    some (jsonObject [
      ("tokenPath", jsonString "$.metadata.token")
    ])
  | .enum enumName =>
    some (jsonObject [
      ("enumRef", jsonString enumName)
    ])
  | _ => none

/-! ## Field Rendering -/

/-- Render a single Hole as an ERC-7730 field entry. -/
private def renderField (hole : Hole) : String :=
  let baseFields : List (String × String) := [
    ("path", jsonString hole.param),
    ("label", jsonString hole.param),
    ("format", jsonString (erc7730FormatType hole.format))
  ]
  let allFields := match erc7730FormatParams hole.format with
    | some params => baseFields ++ [("params", params)]
    | none => baseFields
  jsonObject allFields

/-! ## Template → Intent String

Extract a clean intent string from a template's text.
The template text may contain `{name}` placeholders which are
kept as-is — they serve as human-readable markers.
-/

/-- Extract the intent string from a template.
    For conditional intents, we use the first (then-branch) template. -/
private def intentStringFromTemplate (tmpl : Template) : String :=
  tmpl.text

/-! ## Statement Analysis

Walk the statement AST to collect all templates and their holes.
For a conditional (ite), we collect from both branches and
use the first emitted template as the primary intent.
-/

/-- Collect all (template, holes) pairs from a list of statements. -/
private def collectTemplates : List Stmt → List (Template)
  | [] => []
  | .emit tmpl :: rest => tmpl :: collectTemplates rest
  | .ite _ thenBranch elseBranch :: rest =>
    collectTemplates thenBranch ++ collectTemplates elseBranch ++ collectTemplates rest
  | .forEach _ _ body :: rest =>
    collectTemplates body ++ collectTemplates rest
  | .call _ _ :: rest => collectTemplates rest

/-- Collect all unique holes from all templates in a function body. -/
private def collectAllHoles (stmts : List Stmt) : List Hole :=
  let templates := collectTemplates stmts
  let allHoles := templates.foldl (fun acc t => acc ++ t.holes) []
  -- Deduplicate by param name, keeping first occurrence
  List.foldl (fun acc h =>
    if acc.any (fun existing => existing.param == h.param) then acc
    else acc ++ [h]) [] allHoles

/-! ## Format Entry Rendering -/

/-- Render a single binding as an ERC-7730 display format entry.
    Returns `(selectorHex, jsonContent)` or `none` if the binding's
    intent function isn't found. -/
private def renderFormatEntry (spec : IntentSpec) (binding : IntentBinding)
    (selectorHex : String) : Option (String × String) := do
  let fn ← spec.fns.find? (fun f => f.name == binding.intentFn)
  let templates := collectTemplates fn.body
  let intentStr := match templates.head? with
    | some tmpl => intentStringFromTemplate tmpl
    | none => binding.functionName
  let holes := collectAllHoles fn.body
  let fields := holes.map renderField
  let required := holes.map (fun h => jsonString h.param)
  let entry := jsonObject [
    ("$id", jsonString binding.functionName),
    ("intent", jsonString intentStr),
    ("fields", jsonArray fields),
    ("required", jsonArray required)
  ]
  pure (selectorHex, entry)

/-! ## Top-Level JSON Generation -/

/-- Render the full ERC-7730 JSON for a contract's IntentSpec.
    `selectors` maps `(functionName, selectorHex)` pairs. -/
def emitERC7730Json (spec : IntentSpec)
    (selectors : List (String × String)) : String :=
  let formatEntries := spec.bindings.filterMap fun binding =>
    match selectors.find? (fun (name, _) => name == binding.functionName) with
    | some (_, hex) =>
      let selectorKey := if hex.startsWith "0x" then hex else "0x" ++ hex
      renderFormatEntry spec binding selectorKey
    | none => none
  let formatsObj := jsonObject (formatEntries.map fun (sel, entry) => (sel, entry))
  let displayObj := jsonObject [("formats", formatsObj)]
  -- Context stub: to be filled per-deployment
  let contextObj := jsonObject [
    ("$id", jsonString s!"erc7730-{spec.contractName.toLower}"),
    ("contract", jsonObject [
      ("abi", jsonString s!"https://api.etherscan.io/api?module=contract&action=getabi&address=TBD"),
      ("deployments", jsonArray [
        jsonObject [
          ("chainId", "1"),
          ("address", jsonString "0xTBD")
        ]
      ])
    ])
  ]
  -- Metadata stub
  let metadataObj := jsonObject [
    ("owner", jsonString spec.contractName),
    ("info", jsonObject [
      ("legalName", jsonString spec.contractName),
      ("url", jsonString "")
    ])
  ]
  -- Top-level
  let topLevel := jsonObject [
    ("$schema", jsonString "https://eips.ethereum.org/assets/eip-7730/erc7730-v1.schema.json"),
    ("context", contextObj),
    ("metadata", metadataObj),
    ("display", displayObj)
  ]
  topLevel ++ "\n"

/-- Write the ERC-7730 JSON file for a contract. -/
def writeERC7730File (outDir : String) (spec : IntentSpec)
    (selectors : List (String × String)) : IO Unit := do
  IO.FS.createDirAll outDir
  let content := emitERC7730Json spec selectors
  let path := s!"{outDir}/{spec.contractName}.erc7730.json"
  IO.FS.writeFile path content
  IO.println s!"✓ Wrote ERC-7730 clear-signing manifest: {path}"

/-- Write ERC-7730 JSON files for all bindings in the spec. -/
def writeAllERC7730Files (outDir : String) (spec : IntentSpec)
    (selectors : List (String × String)) : IO Unit :=
  writeERC7730File outDir spec selectors

end Compiler.ERC7730
