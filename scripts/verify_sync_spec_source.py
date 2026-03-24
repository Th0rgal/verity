#!/usr/bin/env python3
"""Authoritative verify workflow sync spec.

Edit this module and regenerate `verify_sync_spec.json` via
`python3 scripts/generate_verify_sync_spec.py` instead of hand-editing the JSON artifact.
"""

from __future__ import annotations

import copy

SPEC = {'check_only_paths': ['.github/workflows/**',
                      '.github/ISSUE_TEMPLATE/**',
                      'artifacts/**',
                      'docs/**',
                      'docs-site/**',
                      'Makefile',
                      'AUDIT.md',
                      'AXIOMS.md',
                      'README.md',
                      'TRUST_ASSUMPTIONS.md'],
 'compiler_paths': ['.github/actions/**',
                    'Verity/**',
                    '!Verity/Proofs/**',
                    'Compiler/**',
                    '!Compiler/Proofs/**',
                    'Compiler.lean',
                    'Contracts/**',
                    '!Contracts/**/Proofs/**',
                    'Contracts.lean',
                    'examples/**',
                    'packages/**',
                    'test/**',
                    'scripts/check_gas.py',
                    'scripts/check_patch_gas_delta.py',
                    'scripts/check_parity_pack_metrics.py',
                    'scripts/check_selectors.py',
                    'scripts/check_yul.py',
                    'scripts/generate_yul_identity_diff_report.py',
                    'scripts/keccak256.py',
                    'scripts/lean_cc_ccache_clang.sh',
                    'scripts/property_utils.py',
                    'lakefile.lean',
                    'lake-manifest.json',
                    'lean-toolchain',
                    'foundry.toml'],
 'expected_push_branches': ['main'],
 'expected_trigger_keys': ['schedule', 'push', 'pull_request', 'workflow_dispatch'],
 'require_workflow_dispatch': True,
 'expected_jobs': ['changes',
                   'checks',
                   'timeout-watchdog',
                   'build',
                   'prepare-macro-fuzz',
                   'build-audits',
                   'macro-fuzz',
                   'build-compiler-binaries',
                   'generate-yul',
                   'generate-yul-patched',
                   'gas-report',
                   'compiler-audits',
                   'compiler-regressions',
                   'lean-profile',
                   'foundry-gas-calibration',
                   'foundry',
                   'foundry-patched',
                   'foundry-multi-seed',
                   'failure-hints'],
 'expected_job_needs': {'changes': [],
                        'checks': [],
                        'timeout-watchdog': ['checks'],
                        'build': ['changes', 'checks'],
                        'prepare-macro-fuzz': ['changes', 'checks', 'build'],
                        'build-audits': ['changes', 'checks', 'build'],
                        'macro-fuzz': ['changes', 'checks', 'prepare-macro-fuzz'],
                        'build-compiler-binaries': ['changes', 'checks', 'build'],
                        'generate-yul': ['changes', 'checks', 'build', 'build-compiler-binaries'],
                        'generate-yul-patched': ['changes',
                                                 'checks',
                                                 'build',
                                                 'build-compiler-binaries'],
                        'gas-report': ['changes', 'checks', 'build', 'build-compiler-binaries'],
                        'compiler-audits': ['changes',
                                            'checks',
                                            'build',
                                            'generate-yul',
                                            'generate-yul-patched',
                                            'gas-report',
                                            'build-compiler-binaries'],
                        'compiler-regressions': ['changes',
                                                 'checks',
                                                 'build',
                                                 'build-compiler-binaries'],
                        'lean-profile': ['changes'],
                        'foundry-gas-calibration': ['changes',
                                                    'generate-yul',
                                                    'gas-report',
                                                    'build-compiler-binaries'],
                        'foundry': ['changes', 'generate-yul', 'build-compiler-binaries'],
                        'foundry-patched': ['changes',
                                            'generate-yul-patched',
                                            'build-compiler-binaries'],
                        'foundry-multi-seed': ['changes',
                                               'generate-yul',
                                               'build-compiler-binaries'],
                        'failure-hints': ['checks',
                                          'build',
                                          'prepare-macro-fuzz',
                                          'build-audits',
                                          'macro-fuzz',
                                          'build-compiler-binaries',
                                          'generate-yul',
                                          'generate-yul-patched',
                                          'gas-report',
                                          'compiler-audits',
                                          'compiler-regressions',
                                          'foundry-gas-calibration',
                                          'foundry',
                                          'foundry-patched',
                                          'foundry-multi-seed']},
 'expected_job_if_conditions': {'changes': None,
                                'checks': None,
                                'timeout-watchdog': "needs.checks.result == 'success' && "
                                                    "!(github.event_name == 'workflow_dispatch' "
                                                    '&& inputs.clean_build)',
                                'build': "needs.checks.result == 'success' && "
                                         "needs.changes.outputs.build == 'true'",
                                'prepare-macro-fuzz': "needs.checks.result == 'success' && "
                                                      "needs.build.result == 'success' && "
                                                      "needs.changes.outputs.macro_fuzz == 'true'",
                                'build-audits': "needs.checks.result == 'success' && "
                                                "needs.build.result == 'success' && "
                                                "needs.changes.outputs.build == 'true'",
                                'macro-fuzz': "needs.checks.result == 'success' && "
                                              "needs.prepare-macro-fuzz.result == 'success' && "
                                              "needs.changes.outputs.macro_fuzz == 'true'",
                                'build-compiler-binaries': "needs.checks.result == 'success' && "
                                                           "needs.build.result == 'success' && "
                                                           "needs.changes.outputs.compiler == "
                                                           "'true'",
                                'generate-yul': "needs.checks.result == 'success' && "
                                                "needs.build.result == 'success' && "
                                                "needs.build-compiler-binaries.result == "
                                                "'success' && "
                                                "needs.changes.outputs.compiler == 'true'",
                                'generate-yul-patched': "needs.checks.result == 'success' && "
                                                        "needs.build.result == 'success' && "
                                                        "needs.build-compiler-binaries.result == "
                                                        "'success' && "
                                                        "needs.changes.outputs.compiler == "
                                                        "'true'",
                                'gas-report': "needs.checks.result == 'success' && "
                                              "needs.build.result == 'success' && "
                                              "needs.build-compiler-binaries.result == "
                                              "'success' && "
                                              "needs.changes.outputs.compiler == 'true'",
                                'compiler-audits': "needs.checks.result == 'success' && "
                                                   "needs.build.result == 'success' && "
                                                   "needs.generate-yul.result == 'success' && "
                                                   "needs.generate-yul-patched.result == "
                                                   "'success' && "
                                                   "needs.gas-report.result == 'success' && "
                                                   "needs.build-compiler-binaries.result == "
                                                   "'success' && "
                                                   "needs.changes.outputs.compiler == 'true'",
                                'compiler-regressions': "needs.checks.result == 'success' && "
                                                        "needs.build.result == 'success' && "
                                                        "needs.build-compiler-binaries.result == "
                                                        "'success' "
                                                        '&& needs.changes.outputs.compiler == '
                                                        "'true'",
                                'lean-profile': "github.event_name == 'workflow_dispatch' && "
                                                "needs.changes.outputs.build == 'true'",
                                'foundry-gas-calibration': 'needs.changes.outputs.compiler == '
                                                           "'true' && (github.event_name != "
                                                           "'pull_request' || "
                                                           'github.event.pull_request.draft == '
                                                           'false)',
                                'foundry': "needs.changes.outputs.compiler == 'true' && "
                                           "(github.event_name != 'pull_request' || "
                                           'github.event.pull_request.draft == false)',
                                'foundry-patched': "needs.changes.outputs.compiler == 'true' && "
                                                   "(github.event_name != 'pull_request' || "
                                                   'github.event.pull_request.draft == false)',
                                'foundry-multi-seed': "needs.changes.outputs.compiler == 'true' && "
                                                      "github.event_name != 'pull_request'",
                                'failure-hints': "always() && github.event_name == 'pull_request' "
                                                 "&& contains(join(needs.*.result, ','), "
                                                 "'failure')"},
 'expected_job_runs_on': {'changes': 'blacksmith-2vcpu-ubuntu-2404',
                          'checks': 'blacksmith-2vcpu-ubuntu-2404',
                          'timeout-watchdog': 'blacksmith-2vcpu-ubuntu-2404',
                          'build': 'blacksmith-8vcpu-ubuntu-2404',
                          'prepare-macro-fuzz': 'blacksmith-16vcpu-ubuntu-2404',
                          'build-audits': 'blacksmith-4vcpu-ubuntu-2404',
                          'macro-fuzz': 'blacksmith-8vcpu-ubuntu-2404',
                          'build-compiler-binaries': 'blacksmith-16vcpu-ubuntu-2404',
                          'generate-yul': 'blacksmith-8vcpu-ubuntu-2404',
                          'generate-yul-patched': 'blacksmith-8vcpu-ubuntu-2404',
                          'gas-report': 'blacksmith-8vcpu-ubuntu-2404',
                          'compiler-audits': 'blacksmith-8vcpu-ubuntu-2404',
                          'compiler-regressions': 'blacksmith-16vcpu-ubuntu-2404',
                          'lean-profile': 'blacksmith-8vcpu-ubuntu-2404',
                          'foundry-gas-calibration': 'blacksmith-4vcpu-ubuntu-2404',
                          'foundry': 'blacksmith-4vcpu-ubuntu-2404',
                          'foundry-patched': 'blacksmith-4vcpu-ubuntu-2404',
                          'foundry-multi-seed': 'blacksmith-4vcpu-ubuntu-2404',
                          'failure-hints': 'blacksmith-2vcpu-ubuntu-2404'},
 'expected_job_timeouts': {'changes': 5,
                           'checks': 5,
                           'timeout-watchdog': 5,
                           'build': "${{ fromJSON(github.event_name == 'workflow_dispatch' && inputs.clean_build && '60' || '35') }}",
                           'prepare-macro-fuzz': 360,
                           'build-audits': 20,
                           'macro-fuzz': "${{ fromJSON(github.event_name == 'workflow_dispatch' && inputs.clean_build && '150' || '90') }}",
                           'build-compiler-binaries': 360,
                           'generate-yul': 45,
                           'generate-yul-patched': 45,
                           'gas-report': 45,
                           'compiler-audits': 45,
                           'compiler-regressions': "${{ fromJSON(github.event_name == 'workflow_dispatch' && inputs.clean_build && '150' || '90') }}",
                           'lean-profile': 45,
                           'foundry-gas-calibration': 15,
                           'foundry': 15,
                           'foundry-patched': 25,
                           'foundry-multi-seed': 25},
 'expected_job_strategy_fail_fast': {'macro-fuzz': False, 'foundry': False, 'foundry-multi-seed': False},
 'expected_job_outputs': {'changes': {'code': '${{ steps.effective.outputs.code }}',
                                      'build': '${{ steps.effective.outputs.build }}',
                                      'compiler': '${{ steps.effective.outputs.compiler }}',
                                      'macro_fuzz': '${{ steps.effective.outputs.macro_fuzz }}'}},
 'expected_job_permissions': {'checks': {'contents': 'write'},
                              'timeout-watchdog': {'actions': 'read', 'contents': 'read'},
                              'failure-hints': {'contents': 'read', 'pull-requests': 'write'}},
 'expected_workflow_permissions': {'contents': 'read'},
 'expected_workflow_concurrency': {'group': '${{ github.workflow }}-${{ github.ref }}',
                                   'cancel-in-progress': "${{ github.event_name != 'schedule' }}"},
 'expected_workflow_env': {'SOLC_VERSION': '0.8.33',
                           'SOLC_URL': 'https://binaries.soliditylang.org/linux-amd64/solc-linux-amd64-v0.8.33+commit.64118f21',
                           'SOLC_SHA256': '1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468',
                           'VERIFY_CLEAN_BUILD': "${{ github.event_name == 'workflow_dispatch' && inputs.clean_build && 'true' || 'false' }}",
                           'VERIFY_FORCE_FULL_RUN': "${{ (github.event_name == 'schedule' || (github.event_name == 'workflow_dispatch' && inputs.force_full_run)) && 'true' || 'false' }}",
                           'VERIFY_USE_STICKY_DISKS': "${{ github.event_name == 'workflow_dispatch' && inputs.clean_build && 'false' || 'true' }}",
                           'VERIFY_DISABLE_LAKE_CACHE_RESTORE': "${{ github.event_name == 'workflow_dispatch' && inputs.clean_build && 'true' || 'false' }}",
                           'VERIFY_CACHE_BUCKET': "${{ github.event_name == 'pull_request' && format('pr-{0}', github.event.pull_request.number) || format('ref-{0}', github.ref_name) }}",
                           'VERIFY_MAIN_CACHE_BUCKET': 'ref-main'},
 'build_compiler_job_names': ['build-compiler-binaries',
                              'generate-yul',
                              'generate-yul-patched',
                              'gas-report'],
 'expected_step_contracts': {'changes': [{'uses': 'actions/checkout@v6'},
                                         {'id': 'filter', 'uses': 'dorny/paths-filter@v4'},
                                         {'id': 'effective',
                                          'name': 'Resolve effective change flags',
                                          'run': 'if [ "$FORCE_FULL_RUN" = "true" ]; then\n'
                                                 '  code=true\n'
                                                 '  build=true\n'
                                                 '  compiler=true\n'
                                                 '  macro_fuzz=true\n'
                                                 'else\n'
                                                 '  code="$CODE_CHANGED"\n'
                                                 '  build="$BUILD_CHANGED"\n'
                                                 '  compiler="$COMPILER_CHANGED"\n'
                                                 '  macro_fuzz="$MACRO_FUZZ_CHANGED"\n'
                                                 'fi\n'
                                                 '\n'
                                                 '{\n'
                                                 '  echo "code=$code"\n'
                                                 '  echo "build=$build"\n'
                                                 '  echo "compiler=$compiler"\n'
                                                 '  echo "macro_fuzz=$macro_fuzz"\n'
                                                 '} >> "$GITHUB_OUTPUT"',
                                          'env': {'FORCE_FULL_RUN': '${{ env.VERIFY_FORCE_FULL_RUN }}',
                                                  'CODE_CHANGED': '${{ steps.filter.outputs.code }}',
                                                  'BUILD_CHANGED': '${{ steps.filter.outputs.build }}',
                                                  'COMPILER_CHANGED': '${{ steps.filter.outputs.compiler }}',
                                                  'MACRO_FUZZ_CHANGED': '${{ steps.filter.outputs.macro_fuzz }}'}}],
                             'checks': [{'uses': 'actions/checkout@v6'},
                                        {'name': 'Run all checks', 'run': 'make check'}],
                             'timeout-watchdog': [{'name': 'Warn on timeout-risk trend',
                                                   'env': {'GH_TOKEN': '${{ github.token }}'},
                                                   'run': 'python3 scripts/ci_timeout_watchdog.py '
                                                          '\\\n'
                                                          '  --repo ${{ github.repository }} \\\n'
                                                          '  --workflow verify.yml \\\n'
                                                          '  --branch ${{ '
                                                          'github.event.pull_request.base.ref || '
                                                          'github.ref_name }}'}],
                             'build': [{'uses': 'actions/checkout@v6',
                                        'with': {'submodules': 'recursive'}},
                                       {'name': 'Setup Lean',
                                        'uses': './.github/actions/setup-lean',
                                        'with': {'cache-key-prefix': 'lake',
                                                 'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                 'sticky-disk-key-prefix': 'verify',
                                                 'use-build-sticky-disk': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                 'build-sticky-disk-key': "verify-build-base-${{ env.VERIFY_CACHE_BUCKET }}-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}-${{ hashFiles('lakefile.lean') }}-${{ hashFiles('lake-manifest.json') }}",
                                                 'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                 'cache-primary-key': 'lake-${{ runner.os }}-${{ '
                                                                      "hashFiles('lean-toolchain') "
                                                                      '}}-${{ '
                                                                      "hashFiles('lakefile.lean') "
                                                                      '}}-${{ '
                                                                      "hashFiles('lake-manifest.json') "
                                                                      '}}-${{ github.run_id }}'}},
                                       {'name': 'Prebuild shared audit Lean targets',
                                        'run': 'set -o pipefail\n'
                                               'lake build PrintAxioms 2>&1 | tee -a '
                                               'lake-build.log'},
                                       {'name': 'Upload prepared Lean workspace build',
                                        'uses': 'actions/upload-artifact@v7',
                                        'with': {'name': 'lean-workspace-build',
                                                 'path': 'lean-workspace-build.tar'}},
                                       {'name': 'Save current run Lake cache',
                                        'uses': 'actions/cache/save@v5',
                                        'if': "success() && needs.changes.outputs.build == 'true' "
                                              "&& steps.setup-lean.outputs.using-sticky-disks != "
                                              "'true'",
                                        'with': {'path': '.lake',
                                                 'key': 'lake-${{ runner.os }}-${{ '
                                                        "hashFiles('lean-toolchain') }}-${{ "
                                                        "hashFiles('lakefile.lean') }}-${{ "
                                                        "hashFiles('lake-manifest.json') }}-${{ "
                                                        'github.run_id }}'}},
                                       {'name': 'Save Lake packages cache',
                                        'uses': 'actions/cache/save@v5',
                                        'if': "success() && needs.changes.outputs.build == 'true' "
                                              "&& steps.setup-lean.outputs.using-sticky-disks != "
                                              "'true' && "
                                              "steps.setup-lean.outputs.cache-hit != 'true'",
                                        'with': {'path': '.lake',
                                                 'key': 'lake-${{ runner.os }}-${{ '
                                                        "hashFiles('lean-toolchain') }}-${{ "
                                                        "hashFiles('lakefile.lean') }}-${{ "
                                                        "hashFiles('lake-manifest.json') }}"}}],
                             'prepare-macro-fuzz': [{'uses': 'actions/checkout@v6',
                                                     'with': {'submodules': 'recursive'}},
                                                    {'name': 'Setup Lean',
                                                     'uses': './.github/actions/setup-lean',
                                                     'with': {'cache-key-prefix': 'lake',
                                                              'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                              'sticky-disk-key-prefix': 'verify',
                                                              'use-build-sticky-disk': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                              'build-sticky-disk-key': "verify-build-macro-fuzz-${{ env.VERIFY_CACHE_BUCKET }}-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}-${{ hashFiles('lakefile.lean') }}-${{ hashFiles('lake-manifest.json') }}",
                                                              'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                              'cache-primary-key': 'lake-${{ '
                                                                                   'runner.os '
                                                                                   '}}-${{ '
                                                                                   "hashFiles('lean-toolchain') "
                                                                                   '}}-${{ '
                                                                                   "hashFiles('lakefile.lean') "
                                                                                   '}}-${{ '
                                                                                   "hashFiles('lake-manifest.json') "
                                                                                   '}}-${{ '
                                                                                   'github.run_id '
                                                                                   '}}'}},
                                                    {'name': 'Download prepared Lean workspace build',
                                                     'uses': 'actions/download-artifact@v7',
                                                     'with': {'name': 'lean-workspace-build'}},
                                                    {'name': 'Build macro round-trip fuzz executable',
                                                     'run': 'for attempt in 1 2 3; do\n'
                                                            '  if stdbuf -oL -eL lake build macro-roundtrip-fuzz; then\n'
                                                            '    exit 0\n'
                                                            '  fi\n'
                                                            '  echo "::warning::lake build attempt $attempt failed; retrying in 10s"\n'
                                                            '  sleep 10\n'
                                                            'done\n'
                                                            'echo "::error::lake build failed after 3 attempts"\n'
                                                            'exit 1'},
                                                    {'name': 'Upload macro-fuzz Lean workspace '
                                                             'build',
                                                     'uses': 'actions/upload-artifact@v7',
                                                     'with': {'name': 'lean-workspace-macro-fuzz-build',
                                                              'path': 'lean-workspace-macro-fuzz-build.tar'}}],
                             'build-audits': [{'uses': 'actions/checkout@v6',
                                               'with': {'submodules': 'recursive'}},
                                              {'name': 'Setup Lean',
                                               'uses': './.github/actions/setup-lean',
                                               'with': {'cache-key-prefix': 'lake',
                                                        'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                        'sticky-disk-key-prefix': 'verify',
                                                        'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                        'cache-primary-key': 'lake-${{ runner.os '
                                                                             '}}-${{ '
                                                                             "hashFiles('lean-toolchain') "
                                                                             '}}-${{ '
                                                                             "hashFiles('lakefile.lean') "
                                                                             '}}-${{ '
                                                                             "hashFiles('lake-manifest.json') "
                                                                             '}}-${{ github.run_id '
                                                                             '}}'}},
                                              {'name': 'Download prepared Lean workspace build',
                                               'uses': 'actions/download-artifact@v7',
                                               'with': {'name': 'lean-workspace-build'}},
                                              {'name': 'Upload axiom dependency report',
                                               'uses': 'actions/upload-artifact@v7',
                                               'with': {'name': 'axiom-dependency-report',
                                                        'path': 'axiom-report.md\n'
                                                                'axiom-report-raw.log'}}],
                             'macro-fuzz': [{'uses': 'actions/checkout@v6',
                                             'with': {'submodules': 'recursive'}},
                                            {'name': 'Setup Lean',
                                             'uses': './.github/actions/setup-lean',
                                             'with': {'cache-key-prefix': 'lake',
                                                      'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                      'sticky-disk-key-prefix': 'verify',
                                                      'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                      'cache-primary-key': 'lake-${{ runner.os '
                                                                           '}}-${{ '
                                                                           "hashFiles('lean-toolchain') "
                                                                           '}}-${{ '
                                                                           "hashFiles('lakefile.lean') "
                                                                           '}}-${{ '
                                                                           "hashFiles('lake-manifest.json') "
                                                                           '}}-${{ github.run_id '
                                                                           '}}'}},
                                            {'name': 'Download prepared Lean workspace build',
                                             'uses': 'actions/download-artifact@v7',
                                             'with': {'name': 'lean-workspace-macro-fuzz-build'}},
                                            {'name': 'Run macro round-trip fuzz harness',
                                             'run': 'chmod +x ./.lake/build/bin/macro-roundtrip-fuzz\n'
                                                    './.lake/build/bin/macro-roundtrip-fuzz'}],
                             'build-compiler-binaries': [{'uses': 'actions/checkout@v6',
                                                          'with': {'submodules': 'recursive'}},
                                                         {'name': 'Setup Lean',
                                                          'uses': './.github/actions/setup-lean',
                                                          'with': {'cache-key-prefix': 'lake-compiler',
                                                                   'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                                   'sticky-disk-key-prefix': 'verify-compiler',
                                                                   'use-build-sticky-disk': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                                   'build-sticky-disk-key': "verify-build-compiler-${{ env.VERIFY_CACHE_BUCKET }}-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}-${{ hashFiles('lakefile.lean') }}-${{ hashFiles('lake-manifest.json') }}",
                                                                   'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                                   'cache-primary-key': 'lake-${{ runner.os '
                                                                                        '}}-${{ '
                                                                                        "hashFiles('lean-toolchain') "
                                                                                        '}}-${{ '
                                                                                        "hashFiles('lakefile.lean') "
                                                                                        '}}-${{ '
                                                                                        "hashFiles('lake-manifest.json') "
                                                                                        '}}-${{ '
                                                                                        'github.run_id '
                                                                                        '}}',
                                                                   'cache-extra-restore-keys': 'lake-${{ '
                                                                                               'runner.os '
                                                                                               '}}-${{ '
                                                                                               "hashFiles('lean-toolchain') "
                                                                                               '}}-${{ '
                                                                                               "hashFiles('lakefile.lean') "
                                                                                               '}}-${{ '
                                                                                               "hashFiles('lake-manifest.json') "
                                                                                               '}}-${{ '
                                                                                               'github.run_id '
                                                                                               '}}'}},
                                                         {'name': 'Download prepared Lean workspace build',
                                                          'uses': 'actions/download-artifact@v7',
                                                          'with': {'name': 'lean-workspace-build'}},
                                                         {'name': 'Restore compiler ccache fallback cache',
                                                          'uses': 'actions/cache/restore@v5',
                                                          'with': {'path': '${{ runner.temp }}/compiler-ccache-cache',
                                                                   'key': 'compiler-ccache-cache-${{ '
                                                                          'env.VERIFY_CACHE_BUCKET '
                                                                          '}}-${{ runner.os '
                                                                          '}}-${{ '
                                                                          "hashFiles('lean-toolchain') "
                                                                          '}}-${{ '
                                                                          "hashFiles('lakefile.lean') "
                                                                          '}}-${{ '
                                                                          "hashFiles('lake-manifest.json') "
                                                                          '}}-${{ github.run_id }}'}},
                                                         {'name': 'Upload compiler workspace build',
                                                          'uses': 'actions/upload-artifact@v7',
                                                          'with': {'name': 'lean-workspace-compiler-build',
                                                                   'path': 'lean-workspace-compiler-build.tar'}},
                                                         {'name': 'Save compiler ccache fallback cache',
                                                          'uses': 'actions/cache/save@v5',
                                                          'if': 'always() && (failure() || '
                                                                "steps.setup-lean.outputs.using-sticky-disks != 'true')",
                                                          'with': {'path': '${{ github.workspace }}/.cache/ccache',
                                                                   'key': 'compiler-ccache-cache-${{ '
                                                                          'env.VERIFY_CACHE_BUCKET '
                                                                          '}}-${{ runner.os '
                                                                          '}}-${{ '
                                                                          "hashFiles('lean-toolchain') "
                                                                          '}}-${{ '
                                                                          "hashFiles('lakefile.lean') "
                                                                          '}}-${{ '
                                                                          "hashFiles('lake-manifest.json') "
                                                                          '}}-${{ github.run_id }}'}},
                                                         {'name': 'Save Lake compiler cache',
                                                          'uses': 'actions/cache/save@v5',
                                                          'if': 'always() && '
                                                                "steps.setup-lean.outputs.using-sticky-disks "
                                                                "!= 'true'",
                                                          'with': {'path': '.lake',
                                                                   'key': 'lake-compiler-${{ runner.os '
                                                                          '}}-${{ '
                                                                          "hashFiles('lean-toolchain') "
                                                                          '}}-${{ '
                                                                          "hashFiles('lakefile.lean') "
                                                                          '}}-${{ '
                                                                          "hashFiles('lake-manifest.json') "
                                                                          '}}-${{ github.run_id }}'}}],
                             'generate-yul': [{'uses': 'actions/checkout@v6',
                                               'with': {'submodules': 'recursive'}},
                                              {'name': 'Setup Lean',
                                               'uses': './.github/actions/setup-lean',
                                               'with': {'cache-key-prefix': 'lake-compiler',
                                                        'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                        'sticky-disk-key-prefix': 'verify-compiler',
                                                        'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                        'cache-primary-key': 'lake-compiler-${{ '
                                                                             'runner.os }}-${{ '
                                                                             "hashFiles('lean-toolchain') "
                                                                             '}}-${{ '
                                                                             "hashFiles('lakefile.lean') "
                                                                             '}}-${{ '
                                                                             "hashFiles('lake-manifest.json') "
                                                                             '}}-${{ github.run_id '
                                                                             '}}',
                                                        'cache-extra-restore-keys': 'lake-${{ '
                                                                                    'runner.os '
                                                                                    '}}-${{ '
                                                                                    "hashFiles('lean-toolchain') "
                                                                                    '}}-${{ '
                                                                                    "hashFiles('lakefile.lean') "
                                                                                    '}}-${{ '
                                                                                    "hashFiles('lake-manifest.json') "
                                                                                    '}}-${{ '
                                                                                    'github.run_id '
                                                                                    '}}'}},
                                              {'name': 'Download prepared Lean workspace build',
                                               'uses': 'actions/download-artifact@v7',
                                               'with': {'name': 'lean-workspace-build'}},
                                              {'name': 'Download compiler workspace build',
                                               'uses': 'actions/download-artifact@v7',
                                               'with': {'name': 'lean-workspace-compiler-build'}},
                                              {'name': 'Download compiler binaries',
                                               'uses': 'actions/download-artifact@v7',
                                               'with': {'name': 'verity-compiler-binaries',
                                                        'path': 'compiler/bin'}},
                                              {'name': 'Upload generated Yul',
                                               'uses': 'actions/upload-artifact@v7',
                                               'with': {'name': 'generated-yul',
                                                        'path': 'compiler/yul'}}],
                             'generate-yul-patched': [{'uses': 'actions/checkout@v6',
                                                       'with': {'submodules': 'recursive'}},
                                                      {'name': 'Setup Lean',
                                                       'uses': './.github/actions/setup-lean',
                                                       'with': {'cache-key-prefix': 'lake-compiler',
                                                                'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                                'sticky-disk-key-prefix': 'verify-compiler',
                                                                'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                                'cache-primary-key': 'lake-compiler-${{ '
                                                                                     'runner.os '
                                                                                     '}}-${{ '
                                                                                     "hashFiles('lean-toolchain') "
                                                                                     '}}-${{ '
                                                                                     "hashFiles('lakefile.lean') "
                                                                                     '}}-${{ '
                                                                                     "hashFiles('lake-manifest.json') "
                                                                                     '}}-${{ '
                                                                                     'github.run_id '
                                                                                     '}}',
                                                                'cache-extra-restore-keys': 'lake-${{ '
                                                                                            'runner.os '
                                                                                            '}}-${{ '
                                                                                            "hashFiles('lean-toolchain') "
                                                                                            '}}-${{ '
                                                                                            "hashFiles('lakefile.lean') "
                                                                                            '}}-${{ '
                                                                                            "hashFiles('lake-manifest.json') "
                                                                                            '}}-${{ '
                                                                                            'github.run_id '
                                                                                            '}}'}},
                                                      {'name': 'Download prepared Lean workspace '
                                                               'build',
                                                       'uses': 'actions/download-artifact@v7',
                                                       'with': {'name': 'lean-workspace-build'}},
                                                      {'name': 'Download compiler workspace '
                                                               'build',
                                                       'uses': 'actions/download-artifact@v7',
                                                       'with': {'name': 'lean-workspace-compiler-build'}},
                                                      {'name': 'Download compiler binaries',
                                                       'uses': 'actions/download-artifact@v7',
                                                       'with': {'name': 'verity-compiler-binaries',
                                                                'path': 'compiler/bin'}},
                                                      {'name': 'Upload patched Yul',
                                                       'uses': 'actions/upload-artifact@v7',
                                                       'with': {'name': 'generated-yul-patched',
                                                                'path': 'compiler/yul-patched'}},
                                                      {'name': 'Upload patch coverage report',
                                                       'uses': 'actions/upload-artifact@v7',
                                                       'with': {'name': 'patch-coverage-report',
                                                                'path': 'compiler/patch-report.tsv'}}],
                             'gas-report': [{'uses': 'actions/checkout@v6',
                                             'with': {'submodules': 'recursive'}},
                                            {'name': 'Setup Lean',
                                             'uses': './.github/actions/setup-lean',
                                             'with': {'cache-key-prefix': 'lake-compiler',
                                                      'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                      'sticky-disk-key-prefix': 'verify-compiler',
                                                      'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                      'cache-primary-key': 'lake-compiler-${{ '
                                                                           'runner.os }}-${{ '
                                                                           "hashFiles('lean-toolchain') "
                                                                           '}}-${{ '
                                                                           "hashFiles('lakefile.lean') "
                                                                           '}}-${{ '
                                                                           "hashFiles('lake-manifest.json') "
                                                                           '}}-${{ github.run_id '
                                                                           '}}',
                                                      'cache-extra-restore-keys': 'lake-${{ '
                                                                                  'runner.os '
                                                                                  '}}-${{ '
                                                                                  "hashFiles('lean-toolchain') "
                                                                                  '}}-${{ '
                                                                                  "hashFiles('lakefile.lean') "
                                                                                  '}}-${{ '
                                                                                  "hashFiles('lake-manifest.json') "
                                                                                  '}}-${{ '
                                                                                  'github.run_id '
                                                                                  '}}'}},
                                            {'name': 'Download compiler workspace build',
                                             'uses': 'actions/download-artifact@v7',
                                             'with': {'name': 'lean-workspace-compiler-build'}},
                                            {'name': 'Upload static gas report',
                                             'uses': 'actions/upload-artifact@v7',
                                             'with': {'name': 'static-gas-report',
                                                      'path': 'gas-report-static.tsv'}},
                                            {'name': 'Upload patched static gas report',
                                             'uses': 'actions/upload-artifact@v7',
                                             'with': {'name': 'static-gas-report-patched',
                                                      'path': 'gas-report-static-patched.tsv'}}],
                             'compiler-audits': [{'uses': 'actions/checkout@v6',
                                                  'with': {'submodules': 'recursive'}},
                                                 {'name': 'Setup Lean',
                                                  'uses': './.github/actions/setup-lean',
                                                  'with': {'cache-key-prefix': 'lake-compiler',
                                                           'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                           'sticky-disk-key-prefix': 'verify-compiler',
                                                           'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                           'cache-primary-key': 'lake-compiler-${{ '
                                                                                'runner.os }}-${{ '
                                                                                "hashFiles('lean-toolchain') "
                                                                                '}}-${{ '
                                                                                "hashFiles('lakefile.lean') "
                                                                                '}}-${{ '
                                                                                "hashFiles('lake-manifest.json') "
                                                                                '}}-${{ github.run_id '
                                                                                '}}',
                                                           'cache-extra-restore-keys': 'lake-${{ '
                                                                                       'runner.os '
                                                                                       '}}-${{ '
                                                                                       "hashFiles('lean-toolchain') "
                                                                                       '}}-${{ '
                                                                                       "hashFiles('lakefile.lean') "
                                                                                       '}}-${{ '
                                                                                       "hashFiles('lake-manifest.json') "
                                                                                       '}}-${{ '
                                                                                       'github.run_id '
                                                                                       '}}'}},
                                                 {'name': 'Download prepared Lean workspace build',
                                                  'uses': 'actions/download-artifact@v7',
                                                  'with': {'name': 'lean-workspace-build'}},
                                                 {'name': 'Download compiler workspace build',
                                                  'uses': 'actions/download-artifact@v7',
                                                  'with': {'name': 'lean-workspace-compiler-build'}},
                                                 {'name': 'Setup solc',
                                                  'uses': './.github/actions/setup-solc'},
                                                 {'name': 'Upload parity-pack identity report',
                                                  'uses': 'actions/upload-artifact@v7',
                                                  'with': {'name': 'parity-pack-identity-report',
                                                           'path': 'compiler/parity-pack-identity-report.json'}}],
                             'compiler-regressions': [{'uses': 'actions/checkout@v6',
                                                       'with': {'submodules': 'recursive'}},
                                                      {'name': 'Setup Lean',
                                                       'uses': './.github/actions/setup-lean',
                                                       'with': {'cache-key-prefix': 'lake-compiler',
                                                                'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                                'sticky-disk-key-prefix': 'verify-compiler',
                                                                'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}',
                                                                'cache-primary-key': 'lake-compiler-${{ '
                                                                                     'runner.os '
                                                                                     '}}-${{ '
                                                                                     "hashFiles('lean-toolchain') "
                                                                                     '}}-${{ '
                                                                                     "hashFiles('lakefile.lean') "
                                                                                     '}}-${{ '
                                                                                     "hashFiles('lake-manifest.json') "
                                                                                     '}}-${{ '
                                                                                     'github.run_id '
                                                                                     '}}',
                                                                'cache-extra-restore-keys': 'lake-${{ '
                                                                                            'runner.os '
                                                                                            '}}-${{ '
                                                                                            "hashFiles('lean-toolchain') "
                                                                                            '}}-${{ '
                                                                                            "hashFiles('lakefile.lean') "
                                                                                            '}}-${{ '
                                                                                            "hashFiles('lake-manifest.json') "
                                                                                            '}}-${{ '
                                                                                            'github.run_id '
                                                                                            '}}'}},
                                                      {'name': 'Download prepared Lean workspace build',
                                                       'uses': 'actions/download-artifact@v7',
                                                       'with': {'name': 'lean-workspace-build'}},
                                                      {'name': 'Download compiler workspace build',
                                                       'uses': 'actions/download-artifact@v7',
                                                       'with': {'name': 'lean-workspace-compiler-build'}},
                                                      {'name': 'Build compiler CLI regression executable',
                                                       'run': 'stdbuf -oL -eL lake build compiler-main-test'},
                                         {'name': 'Run compiler CLI regression module',
                                          'run': 'chmod +x ./.lake/build/bin/compiler-main-test && stdbuf -oL -eL ./.lake/build/bin/compiler-main-test'},
                                                      {'name': 'Build CompilationModel feature '
                                                               'regression module',
                                                               'run': 'stdbuf -oL -eL lake build '
                                                               'Compiler.CompilationModelFeatureTest'}],
                             'lean-profile': [{'uses': 'actions/checkout@v6'},
                                             {'name': 'Setup Lean',
                                              'uses': './.github/actions/setup-lean',
                                               'with': {'use-sticky-disks': '${{ env.VERIFY_USE_STICKY_DISKS }}',
                                                        'sticky-disk-key-prefix': 'verify',
                                                        'disable-lake-cache-restore': '${{ env.VERIFY_DISABLE_LAKE_CACHE_RESTORE }}'}}],
                             'foundry-gas-calibration': [{'uses': 'actions/checkout@v6',
                                                          'with': {'submodules': 'recursive'}},
                                                         {'name': 'Setup Foundry environment',
                                                          'uses': './.github/actions/setup-foundry'}],
                             'foundry': [{'uses': 'actions/checkout@v6',
                                          'with': {'submodules': 'recursive'}},
                                         {'name': 'Setup Foundry environment',
                                          'uses': './.github/actions/setup-foundry'}],
                             'foundry-patched': [{'uses': 'actions/checkout@v6',
                                                  'with': {'submodules': 'recursive'}},
                                                 {'name': 'Download prepared Lean workspace build',
                                                  'uses': 'actions/download-artifact@v7',
                                                  'with': {'name': 'lean-workspace-build'}},
                                                 {'name': 'Download compiler workspace build',
                                                  'uses': 'actions/download-artifact@v7',
                                                  'with': {'name': 'lean-workspace-compiler-build'}},
                                                 {'name': 'Setup Foundry environment',
                                                  'uses': './.github/actions/setup-foundry',
                                                  'with': {'yul-artifact-name': 'generated-yul-patched',
                                                           'yul-artifact-path': 'compiler/yul-patched'}}],
                             'foundry-multi-seed': [{'uses': 'actions/checkout@v6',
                                                     'with': {'submodules': 'recursive'}},
                                                    {'name': 'Setup Foundry environment',
                                                     'uses': './.github/actions/setup-foundry'}],
                             'failure-hints': [{'name': 'Post CI failure hints',
                                                'uses': 'actions/github-script@v7',
                                                'env': {'NEEDS_JSON': '${{ toJson(needs) }}'},
                                                'with': {'script': 'const marker = "<!-- '
                                                                   'ci-failure-hints -->";\n'
                                                                   'const needs = '
                                                                   'JSON.parse(process.env.NEEDS_JSON '
                                                                   '|| "{}");\n'
                                                                   'const failed = '
                                                                   'Object.entries(needs)\n'
                                                                   '  .filter(([, info]) => info '
                                                                   '&& info.result === "failure")\n'
                                                                   '  .map(([name]) => name);\n'
                                                                   'if (failed.length === 0) {\n'
                                                                   '  core.info("No failed jobs; '
                                                                   'no hint comment needed.");\n'
                                                                   '  return;\n'
                                                                   '}\n'
                                                                   '\n'
                                                                   'const lines = [];\n'
                                                                   'lines.push(marker);\n'
                                                                   'lines.push("### CI Failure '
                                                                   'Hints");\n'
                                                                   'lines.push("");\n'
                                                                   'lines.push("Failed jobs: " + '
                                                                   'failed.map((n) => "`" + n + '
                                                                   '"`").join(", "));\n'
                                                                   'lines.push("");\n'
                                                                   'lines.push("Copy-paste local '
                                                                   'triage:");\n'
                                                                   'lines.push("```bash");\n'
                                                                   'lines.push("make check");\n'
                                                                   'lines.push("lake build");\n'
                                                                   'lines.push("FOUNDRY_PROFILE=difftest '
                                                                   'forge test -vv");\n'
                                                                   'lines.push("```");\n'
                                                                   'const body = '
                                                                   'lines.join("\\\\n");\n'
                                                                   '\n'
                                                                   'const owner = '
                                                                   'context.repo.owner;\n'
                                                                   'const repo = '
                                                                   'context.repo.repo;\n'
                                                                   'const issue_number = '
                                                                   'context.issue.number;\n'
                                                                   'const comments = await '
                                                                   'github.paginate(github.rest.issues.listComments, '
                                                                   '{\n'
                                                                   '  owner,\n'
                                                                   '  repo,\n'
                                                                   '  issue_number,\n'
                                                                   '  per_page: 100\n'
                                                                   '});\n'
                                                                   'const existing = '
                                                                   'comments.find((c) =>\n'
                                                                   '  c.user && c.user.type === '
                                                                   '"Bot" && typeof c.body === '
                                                                   '"string" && '
                                                                   'c.body.includes(marker)\n'
                                                                   ');\n'
                                                                   'if (existing) {\n'
                                                                   '  await '
                                                                   'github.rest.issues.updateComment({\n'
                                                                   '    owner,\n'
                                                                   '    repo,\n'
                                                                   '    comment_id: existing.id,\n'
                                                                   '    body\n'
                                                                   '  });\n'
                                                                   '} else {\n'
                                                                   '  await '
                                                                   'github.rest.issues.createComment({\n'
                                                                   '    owner,\n'
                                                                   '    repo,\n'
                                                                   '    issue_number,\n'
                                                                   '    body\n'
                                                                   '  });\n'
                                                                   '}'}}]},
 'expected_checks_commands': ['make check'],
 'required_makefile_check_commands': ['python3 scripts/check_property_manifest.py',
                                      'python3 scripts/check_property_coverage.py',
                                      'python3 scripts/check_contract_structure.py',
                                      'python3 scripts/check_paths.py',
                                      'python3 scripts/check_compilationmodel_split.py',
                                      'python3 scripts/check_axioms.py',
                                      'python3 scripts/generate_verification_status.py --check',
                                      'python3 scripts/check_verification_status_doc.py',
                                      'python3 scripts/generate_verify_sync_spec.py --check',
                                      'python3 scripts/check_verify_sync.py',
                                      'python3 scripts/check_bridge_coverage_sync.py',
                                      'python3 scripts/check_builtin_bridge_matrix_sync.py',
                                      'python3 '
                                      'scripts/check_interpreter_feature_boundary_catalog_sync.py',
                                      'python3 scripts/check_interpreter_feature_summary_sync.py',
                                      'python3 scripts/check_low_level_call_boundary_sync.py',
                                      'python3 scripts/check_linear_memory_boundary_sync.py',
                                      'python3 '
                                      'scripts/check_axiomatized_primitive_boundary_sync.py',
                                      'python3 scripts/check_struct_mapping_surface_sync.py',
                                      'python3 scripts/check_issue_templates.py',
                                      'python3 scripts/check_docs_workflow_sync.py',
                                      'python3 scripts/check_solc_pin.py',
                                      'python3 scripts/check_property_manifest_sync.py',
                                      'python3 scripts/check_macro_health.py',
                                      'python3 scripts/check_storage_layout.py',
                                      'python3 scripts/check_lean_hygiene.py',
                                      'python3 scripts/check_gas.py coverage',
                                      'python3 scripts/check_compiler_boundaries.py',
                                      'python3 scripts/check_split_compiler_test_artifacts.py',
                                      'python3 scripts/check_yul.py --builtin-boundary-only',
                                      'python3 scripts/check_rewrite_proof_metadata.py',
                                      'python3 scripts/generate_evmyullean_capability_report.py '
                                      '--check',
                                      'python3 scripts/generate_evmyullean_adapter_report.py '
                                      '--check',
                                      'python3 scripts/generate_print_axioms.py --check',
                                      'python3 scripts/check_proof_length.py',
                                      'python3 scripts/check_issue_1060_integrity.py',
                                      "python3 -m unittest discover -s scripts -p 'test_*.py' -v"],
 'expected_checks_other_commands': [],
 'expected_build_commands': ['check_lean_warning_regression.py --log lake-build.log'],
 'required_build_run_commands': ['lake build PrintAxioms'],
 'expected_build_audit_commands': ['check_split_package_builds.py',
                                   'check_macro_roundtrip_fuzz_coverage.py',
                                   'check_proof_length.py --format=markdown >> '
                                   '$GITHUB_STEP_SUMMARY',
                                   'report_property_coverage.py --format=markdown >> '
                                   '$GITHUB_STEP_SUMMARY',
                                   'check_storage_layout.py --format=markdown >> '
                                   '$GITHUB_STEP_SUMMARY'],
 'required_build_audit_run_commands': ['lake build PrintAxioms', 'lake env lean PrintAxioms.lean'],
 'expected_build_compiler_commands': [],
 'required_build_compiler_run_commands': ['verity-compiler',
                                          'verity-compiler-patched',
                                          'difftest-interpreter',
                                          'gas-report',
                                          '--output compiler/yul',
                                          '--output compiler/yul-patched',
                                          'lake exe gas-report --manifest '
                                          'packages/verity-examples/contracts.manifest > '
                                          'gas-report-static.tsv',
                                          'lake exe gas-report --manifest '
                                          'packages/verity-examples/contracts.manifest '
                                          '--enable-patches --patch-max-iterations 2 > '
                                          'gas-report-static-patched.tsv'],
 'expected_compiler_audit_commands': ['generate_yul_identity_diff_report.py --verity-dir '
                                      'compiler/yul-parity-pack --solc-dir '
                                      'compiler/yul-parity-reference --output '
                                      'compiler/parity-pack-identity-report.json',
                                      'check_parity_pack_metrics.py --report '
                                      'compiler/parity-pack-identity-report.json '
                                      '--max-only-in-verity 0 --max-only-in-solidity 0 '
                                      '--max-hash-mismatch 0 --format markdown >> '
                                      '"$GITHUB_STEP_SUMMARY"',
                                      'check_gas.py coverage --dir compiler/yul --dir '
                                      'compiler/yul-patched',
                                      'keccak256.py --self-test',
                                      'check_selectors.py --check-fixtures',
                                      'check_yul.py --dir compiler/yul --dir compiler/yul-patched '
                                      '--require-same-files compiler/yul compiler/yul-patched',
                                      'check_gas.py report',
                                      'check_patch_gas_delta.py --baseline-report '
                                      'gas-report-static.tsv --patched-report '
                                      'gas-report-static-patched.tsv --min-improved-contracts 0 '
                                      '--summary-markdown patch-gas-delta-summary.md >> '
                                      '"$GITHUB_STEP_SUMMARY"'],
 'required_compiler_audit_run_commands': ['--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai',
                                          '--backend-profile solidity-parity'],
 'expected_foundry': {'shards': 8, 'seed': 42},
 'expected_foundry_patched': {'seed': 42,
                              'shard_count': 1,
                              'shard_index': 0,
                              'no_match_test': 'Random10000'},
 'expected_foundry_multi_seed': {'seeds': [0, 1, 42, 123, 999, 12345, 67890]},
 'expected_foundry_gas_calibration': {'profile': 'difftest',
                                      'artifact': 'static-gas-report',
                                      'command': 'python3 scripts/check_gas.py calibration '
                                                 '--static-report gas-report-static.tsv'},
 'expected_uploaded_artifacts': {'build': ['lean-workspace-build'],
                                 'prepare-macro-fuzz': ['lean-workspace-macro-fuzz-build'],
                                 'build-audits': ['axiom-dependency-report'],
                                 'build-compiler-binaries': ['difftest-interpreter',
                                                             'verity-compiler-binaries',
                                                             'lean-workspace-compiler-build'],
                                 'generate-yul': ['generated-yul'],
                                 'generate-yul-patched': ['generated-yul-patched',
                                                          'patch-coverage-report'],
                                 'gas-report': ['static-gas-report',
                                                'static-gas-report-patched'],
                                 'compiler-audits': ['parity-pack-identity-report'],
                                 'lean-profile': ['lean-perf-queue']},
 'expected_uploaded_artifact_paths': {'build': ['lean-workspace-build.tar'],
                                      'prepare-macro-fuzz': ['lean-workspace-macro-fuzz-build.tar'],
                                      'build-audits': ['axiom-report.md\naxiom-report-raw.log'],
                                      'build-compiler-binaries': ['.lake/build/bin/difftest-interpreter',
                                                                  'compiler/bin',
                                                                  'lean-workspace-compiler-build.tar'],
                                      'generate-yul': ['compiler/yul'],
                                      'generate-yul-patched': ['compiler/yul-patched',
                                                               'compiler/patch-report.tsv'],
                                      'gas-report': ['gas-report-static.tsv',
                                                     'gas-report-static-patched.tsv'],
                                      'compiler-audits': ['compiler/parity-pack-identity-report.json'],
                                      'lean-profile': ['lean-perf-queue.md']},
 'expected_downloaded_artifacts': {'prepare-macro-fuzz': ['lean-workspace-build'],
                                   'build-audits': ['lean-workspace-build'],
                                   'macro-fuzz': ['lean-workspace-macro-fuzz-build'],
                                   'build-compiler-binaries': ['lean-workspace-build'],
                                   'generate-yul': ['lean-workspace-build',
                                                    'lean-workspace-compiler-build',
                                                    'verity-compiler-binaries'],
                                   'generate-yul-patched': ['lean-workspace-build',
                                                            'lean-workspace-compiler-build',
                                                            'verity-compiler-binaries'],
                                   'gas-report': ['lean-workspace-build',
                                                  'lean-workspace-compiler-build'],
                                   'compiler-audits': ['lean-workspace-build',
                                                       'lean-workspace-compiler-build',
                                                       'generated-yul',
                                                       'generated-yul-patched',
                                                       'static-gas-report',
                                                       'static-gas-report-patched',
                                                       'patch-coverage-report',
                                                       'verity-compiler-binaries'],
                                   'compiler-regressions': ['lean-workspace-build',
                                                            'lean-workspace-compiler-build'],
                                   'foundry-gas-calibration': ['static-gas-report'],
                                   'foundry-patched': ['lean-workspace-build',
                                                       'lean-workspace-compiler-build']},
 'expected_downloaded_artifact_paths': {'prepare-macro-fuzz': [None],
                                        'build-audits': [None],
                                        'macro-fuzz': [None],
                                        'build-compiler-binaries': [None],
                                        'generate-yul': [None, None, 'compiler/bin'],
                                        'generate-yul-patched': [None, None, 'compiler/bin'],
                                        'gas-report': [None,
                                                       None],
                                        'compiler-audits': [None,
                                                            None,
                                                            'compiler/yul',
                                                            'compiler/yul-patched',
                                                            None,
                                                            None,
                                                            'compiler',
                                                            'compiler/bin'],
                                        'compiler-regressions': [None,
                                                                 None],
                                        'foundry-gas-calibration': [None],
                                        'foundry-patched': [None,
                                                            None]}}


def build_spec() -> dict:
    return copy.deepcopy(SPEC)
