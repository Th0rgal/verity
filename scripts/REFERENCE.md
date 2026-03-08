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
- `check_builtin_bridge_matrix_sync.py`: keep the builtin bridge matrix artifact and docs in sync, including delegated env builtins.
- `check_interpreter_feature_boundary_catalog_sync.py`: keep the interpreter proof-boundary category note aligned with the machine-readable feature matrix.
- `check_interpreter_feature_summary_sync.py`: keep the interpreter feature summary table aligned with the machine-readable feature matrix artifact.
- `check_low_level_call_boundary_sync.py`: keep docs aligned with the current low-level call proof boundary.
- `check_linear_memory_boundary_sync.py`: keep docs aligned with the current linear-memory proof boundary.
- `check_axiomatized_primitive_boundary_sync.py`: keep docs aligned with the current axiomatized-primitive proof boundary.
- `check_struct_mapping_surface_sync.py`: keep struct-mapping storage docs aligned with the current compiler surface.
- `check_storage_layout.py`
- `check_lean_hygiene.py`
- `check_proof_length.py`
- `check_macro_health.py`
- `check_compiler_boundaries.py`
- `test_check_struct_mapping_surface_sync.py`: unit coverage for the struct-mapping doc sync guard.

## Foundry/gas/selector pipeline

- `check_selectors.py`
- `check_yul.py`
- `check_gas.py`
- `check_patch_gas_delta.py`

## Helpers and generators

- `workflow_jobs.py`: shared workflow parsing and command matching helpers.
- `generate_print_axioms.py`
- `generate_contract.py`
- `generate_macro_property_tests.py`
