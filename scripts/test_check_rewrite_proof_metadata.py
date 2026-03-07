#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_rewrite_proof_metadata as guard


class RewriteProofMetadataTests(unittest.TestCase):
    def _write_repo(self, patch_rules_text: str, *, proofs_text: str = "", parity_packs_text: str = "") -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        patch_rules_path = root / "PatchRules.lean"
        patch_rules_path.write_text(patch_rules_text, encoding="utf-8")
        if proofs_text:
            (root / "Proofs.lean").write_text(proofs_text, encoding="utf-8")
        if parity_packs_text:
            (root / "ParityPacks.lean").write_text(parity_packs_text, encoding="utf-8")
        return root

    def test_accepts_non_empty_literal_and_alias_proof_refs(self) -> None:
        root = self._write_repo(
            """
            def proofAlias : String := "Proofs.alias"

            def exprRuleA : ExprPatchRule := {
              patchName := "expr-a"
              proofId := "Proofs.expr_a"
            }

            def stmtRuleA : StmtPatchRule := {
              patchName := "stmt-a"
              proofId := proofAlias
            }

            def blockRuleA : BlockPatchRule := {
              patchName := "block-a"
              proofId := "Proofs.block_a"
            }

            def ruleA : ObjectPatchRule := {
              patchName := "a"
              proofId := "Proofs.a"
            }

            def ruleB : ObjectPatchRule := {
              patchName := "b"
              proofId := proofAlias
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := [exprRuleA]
              stmtRules := [stmtRuleA]
              blockRules := [blockRuleA]
              objectRules := [ruleA]
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := [ruleB]
            }
            """,
            proofs_text="""
            namespace Proofs
            theorem expr_a : True := by trivial
            theorem alias : True := by trivial
            theorem block_a : True := by trivial
            theorem a : True := by trivial
            theorem b : True := by trivial
            end Proofs
            """,
        )
        self.assertEqual(guard.check_active_object_rule_proofs(root / "PatchRules.lean", root), [])

    def test_accepts_lean_name_aliases_and_helper_calls(self) -> None:
        root = self._write_repo(
            """
            def proofAlias : Lean.Name := ``Proofs.alias
            def helperAlias : Lean.Name := proofRefName "Proofs.helper"

            def exprRuleA : ExprPatchRule := {
              patchName := "expr-a"
              proofId := proofAlias
            }

            def stmtRuleA : StmtPatchRule := {
              patchName := "stmt-a"
              proofId := proofRefName "Proofs.stmt_a"
            }

            def blockRuleA : BlockPatchRule := {
              patchName := "block-a"
              proofId := helperAlias
            }

            def ruleA : ObjectPatchRule := {
              patchName := "a"
              proofId := ``Proofs.object_a
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := [exprRuleA]
              stmtRules := [stmtRuleA]
              blockRules := [blockRuleA]
              objectRules := [ruleA]
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }
            """,
            proofs_text="""
            namespace Proofs
            theorem alias : True := by trivial
            theorem helper : True := by trivial
            theorem stmt_a : True := by trivial
            theorem object_a : True := by trivial
            end Proofs
            """,
        )
        self.assertEqual(guard.check_active_object_rule_proofs(root / "PatchRules.lean", root), [])

    def test_rejects_empty_proof_id_literal(self) -> None:
        root = self._write_repo(
            """
            def badRule : ObjectPatchRule := {
              patchName := "bad"
              proofId := ""
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := [badRule]
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(root / "PatchRules.lean", root)
        self.assertTrue(any("unresolved or empty proofId token" in err for err in errors))

    def test_rejects_anonymous_lean_name_proof_ref(self) -> None:
        root = self._write_repo(
            """
            def badRule : ObjectPatchRule := {
              patchName := "bad"
              proofId := .anonymous
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := [badRule]
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(root / "PatchRules.lean", root)
        self.assertTrue(any("unresolved or empty proofId token" in err for err in errors))

    def test_rejects_missing_object_rule_definition(self) -> None:
        root = self._write_repo(
            """
            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := [missingRule]
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(root / "PatchRules.lean", root)
        self.assertTrue(any("not defined as ObjectPatchRule" in err for err in errors))

    def test_rejects_unresolved_alias(self) -> None:
        root = self._write_repo(
            """
            def badRule : ObjectPatchRule := {
              patchName := "bad"
              proofId := unknownAlias
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := [badRule]
            }
            """
        )
        errors = guard.check_active_object_rule_proofs(root / "PatchRules.lean", root)
        self.assertTrue(any("unresolved or empty proofId token" in err for err in errors))

    def test_rejects_missing_proof_declaration(self) -> None:
        root = self._write_repo(
            """
            def ruleA : ObjectPatchRule := {
              patchName := "a"
              proofId := "Proofs.missing"
            }

            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := [ruleA]
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }
            """,
            proofs_text="""
            namespace Proofs
            theorem present : True := by trivial
            end Proofs
            """,
        )
        errors = guard.check_active_object_rule_proofs(root / "PatchRules.lean", root)
        self.assertTrue(any("missing proof declaration" in err for err in errors))

    def test_rejects_missing_parity_pack_composition_declaration(self) -> None:
        root = self._write_repo(
            """
            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }
            """,
            proofs_text="""
            namespace Proofs
            theorem present : True := by trivial
            end Proofs
            """,
            parity_packs_text="""
            def packA : ParityPack := {
              id := "pack-a"
              compositionProofRef := "Proofs.missing"
            }
            """,
        )
        errors = guard._check_parity_pack_proof_refs(root / "ParityPacks.lean", root)
        self.assertTrue(any("missing composition proof declaration" in err for err in errors))

    def test_collect_decl_names_keeps_namespace_after_section_end(self) -> None:
        root = self._write_repo(
            """
            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }
            """,
            proofs_text="""
            namespace Proofs
            section Internal
            theorem before_section_end : True := by trivial
            end Internal
            theorem after_section_end : True := by trivial
            end Proofs
            """,
            parity_packs_text="""
            def packA : ParityPack := {
              id := "pack-a"
              compositionProofRef := "Proofs.after_section_end"
            }
            """,
        )
        errors = guard._check_parity_pack_proof_refs(root / "ParityPacks.lean", root)
        self.assertEqual(errors, [])

    def test_accepts_lean_name_parity_pack_refs(self) -> None:
        root = self._write_repo(
            """
            def foundationRewriteBundle : RewriteRuleBundle := {
              id := "foundation"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }

            def solcCompatRewriteBundle : RewriteRuleBundle := {
              id := "solc"
              exprRules := []
              stmtRules := []
              blockRules := []
              objectRules := []
            }
            """,
            proofs_text="""
            namespace Proofs
            theorem alias : True := by trivial
            theorem helper : True := by trivial
            theorem direct : True := by trivial
            end Proofs
            """,
            parity_packs_text="""
            def packAlias : Lean.Name := ``Proofs.alias
            def helperAlias : Lean.Name := proofRefName "Proofs.helper"

            def packA : ParityPack := {
              id := "pack-a"
              compositionProofRef := packAlias
            }

            def packB : ParityPack := {
              id := "pack-b"
              compositionProofRef := helperAlias
            }

            def packC : ParityPack := {
              id := "pack-c"
              compositionProofRef := ``Proofs.direct
            }
            """,
        )
        errors = guard._check_parity_pack_proof_refs(root / "ParityPacks.lean", root)
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
