# Scripts Reference

This document is the long-form reference for script responsibilities.

## Verify workflow sync

- `check_verify_sync.py`: unified table-driven validator for workflow invariants.
- `verify_sync_spec.json`: expected job order, command lists, path filters, foundry settings, and artifact producers.

## Issue #1060 automation

- `check_issue_1060_integrity.py`: ledger schema + anti-inflation + repository-fact checks (run in CI).
- `check_issue_templates.py`: validate GitHub issue form structure and fail on accidental CI-log contamination.

## Artifacts and documentation consistency

- `generate_verification_status.py`: refresh/check `artifacts/verification_status.json`.
- `check_verification_status_doc.py`: keep `docs/VERIFICATION_STATUS.md` aligned with the artifact-backed live totals.
- `verification_metrics.py`: shared metric collection and strict artifact validation.
- `refresh_verification_artifacts.sh`: regenerate and validate the verification artifact.

## Property and proof boundaries

Primary guards:
- `check_axioms.py`: validate AXIOMS.md registry locations and parse `PrintAxioms.lean` dependency output.
- `check_paths.py`: detect case-insensitive checkout hazards and enforce universal Layer-2 bridge quantification.
- `check_property_manifest.py`
- `check_property_coverage.py`
- `check_property_manifest_sync.py`
- `check_storage_layout.py`
- `check_manual_spec_quarantine.py`
- `check_spec_proof_migration_boundary.py`
- `check_lean_hygiene.py`
- `check_proof_length.py`

## Foundry/gas/selector pipeline

- `check_selectors.py`
- `check_selector_fixtures.py`
- `check_yul.py`
- `check_gas_report.py`
- `check_patch_gas_delta.py`
- `check_gas_model_coverage.py`
- `check_gas_calibration.py`

## Helpers and generators

- `workflow_jobs.py`: shared workflow parsing and command matching helpers.
- `generate_print_axioms.py`
- `generate_contract.py`
- `generate_macro_property_tests.py`
- `check_macro_property_test_generation.py`
