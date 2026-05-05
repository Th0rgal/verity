# Verity Self-Hosted Runner Validation Report

Date: 2026-05-05

This report compares the connected self-hosted runners with real Verity CI
work. The validation was run through GitHub Actions, with each job explicitly
forced onto a selected runner label set.

## Current Runner Architecture

```text
lfglabs-dev/verity GitHub Actions
  |
  |-- build-88-99-4-254-1
  |     host: 88.99.4.254
  |     architecture: Linux X64
  |     role: default heavy x64 Lean/build/proof jobs
  |     labels: self-hosted, Linux, X64, verity, build, cpu-8, mem-64g,
  |             build-heavy, ci-host-88-99-4-254, hetzner, hz2
  |
  |-- tmd-verity-fastlane-1
  |     host: 95.216.244.60
  |     architecture: Linux X64
  |     role: standby x64 fastlane fallback
  |     labels: self-hosted, Linux, X64, verity, fastlane, cpu-8,
  |             ci-host-95-216-244-60, hetzner, hz1
  |
  |-- dgx-spark-gpu-1
        host: spark-de79 over Tailscale
        architecture: Linux ARM64
        role: primary fastlane, trusted GPU jobs, explicit ARM64 Lean validation
        labels: self-hosted, Linux, ARM64, verity, fastlane, dgx, dgx-spark,
                gpu, nvidia, home, arm64-gb10
```

Production workflow routing remains capability based:

```yaml
runs-on: [self-hosted, linux, ARM64, dgx-spark, verity, fastlane]
runs-on: [self-hosted, linux, x64, verity, build]
runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
```

The DGX intentionally has `verity,fastlane` but not `build`. Ordinary short
fastlane jobs land there, while full proof/build jobs stay on the x64 build
runner.

## Validation Workflow

The repository now includes a manual-only validation workflow:

```text
.github/workflows/runner-lean-validation.yml
```

It accepts a JSON `runs-on` label list and runs a CI-equivalent Lean/proof
validation on that runner:

- `make check`
- full `lake build`
- Lean warning regression check
- `lake build PrintAxioms`
- split package, macro fuzz coverage, axiom, proof length, property coverage,
  and storage layout audits
- optional compiler-core validation:
  - build `verity-compiler`
  - build `verity-compiler-patched`
  - build `difftest-interpreter`
  - build `gas-report`
  - generate baseline and patched Yul
  - generate static gas reports
  - on x64, install a pinned job-local `solc` and run `check_yul.py`
  - on ARM64, run filename parity and EVM/Yul builtin boundary checks when
    `solc` is unavailable

The workflow is intentionally `workflow_dispatch` only. It is for validating
runner capability, benchmarking new hosts, and qualifying architecture changes.

## Host Inventory

| Runner | Host | CPU | RAM | Root disk free | Notes |
| --- | --- | --- | --- | --- | --- |
| `build-88-99-4-254-1` | `Ubuntu-2404-noble-amd64-base` | Intel i7-6700, 4C/8T | 62 GiB | about 680 GiB free | Healthy x64 build host. |
| `tmd-verity-fastlane-1` | `tmd` | Intel i7-7700, 4C/8T | 62 GiB | about 95 GiB free | Standby x64 fastlane fallback; still disk constrained. |
| `dgx-spark-gpu-1` | `spark-de79` | 20 ARM64 cores: Cortex-X925 + Cortex-A725 | 119 GiB | about 1.6 TiB free | Primary fastlane and explicit ARM64/GPU runner. |

## Cold-ish Validation Results

These are the most useful comparison numbers because they include substantial
real work rather than only warm cache no-ops.

| Step | DGX ARM64 | Hz2 build x64 | Hz1 fastlane x64 |
| --- | ---: | ---: | ---: |
| `make check` | 34s | 75s | 82s |
| `lake build` | 111s | 279s | 275s |
| `lake build PrintAxioms` | 231s | 588s | 572s |
| `PrintAxioms report` | 81s | 171s | 175s |
| `build verity-compiler` | 31s | 142s | not run |
| `build verity-compiler-patched` | 3s | 8s | not run |
| `build difftest-interpreter` | 101s | 402s | not run |
| `build gas-report` | 2s | 4s | not run |

Relevant runs:

| Runner | Run | Result | Notes |
| --- | --- | --- | --- |
| DGX ARM64 | `25387433137` | failed at final `solc` check | Lean and compiler-core work passed before the x64-only `solc` assumption. |
| DGX ARM64 | `25388394404` | success | ARM64-aware validation passed. |
| Hz2 build x64 | `25387433160` | failed at final `solc` check | Lean and compiler-core work passed before the runner-local `solc` installer was fixed. |
| Hz2 build x64 | `25389590164` | success | x64 validation passed with pinned job-local `solc`. |
| Hz1 fastlane x64 | `25387433172` | success | Lean/audit-only validation passed with compiler-core disabled. |

## Warm Validation Results

After caches were warm, both DGX and Hz2 completed the full validation
successfully:

| Runner | Run | Job wall clock | Notable timings |
| --- | --- | ---: | --- |
| DGX ARM64 | `25388394404` | 2m18s | `make check` 35s, `PrintAxioms report` 81s, compiler-core rebuilds 0-1s. |
| Hz2 build x64 | `25389590164` | 4m45s | `make check` 80s, `PrintAxioms report` 173s, compiler-core rebuilds 0-1s. |

## Findings

The DGX is materially faster for the real Lean and compiler-core tasks tested.
On the cold-ish validation run it was roughly:

- 2.2x faster for `make check`;
- 2.5x faster for full `lake build`;
- 2.5x faster for `lake build PrintAxioms`;
- 2.1x faster for the PrintAxioms report;
- 4.6x faster for the first `verity-compiler` build;
- 4.0x faster for the first `difftest-interpreter` build.

The DGX can run the Lean/proof-heavy part of Verity CI reliably on ARM64. It
also built the Verity compiler-core executables on ARM64 and generated Yul and
gas reports.

The DGX should still not become the default general Verity build runner yet. The
remaining x64-specific surface is real:

- production Solidity/Yul checking currently expects a Linux x64 `solc`;
- Foundry and other EVM tooling should be audited before default ARM64 use;
- generated compiler artifacts may be consumed by x64 assumptions elsewhere;
- the DGX is also a valuable GPU/inference host and should not receive
  accidental full-build CPU-only queue pressure;
- the DGX is reachable through private networking and should stay in a
  restricted runner group with trusted workflows only.

The x64 build host remains necessary as the default production proof runner for
now. The old x64 fastlane host remains useful as a fallback and for
host-pinned debugging, but primary fastlane routing now points at the DGX.

## Reliability Fixes Made During Validation

Cancelled runner jobs previously left child `lake` or interpreter processes
alive because GitHub's generated service used:

```ini
KillMode=process
```

All three hosts now have a systemd drop-in:

```ini
[Service]
KillMode=control-group
SendSIGKILL=yes
TimeoutStopSec=90s
```

The repository runner installer writes the same drop-in for future installs.

The validation workflow also found that `solc` setup should avoid host-global
installation and sudo assumptions. The final workflow installs a pinned `solc`
into `$RUNNER_TEMP/bin` and appends that directory to `GITHUB_PATH`, which
works on the non-root runner services.

## Recommended Architecture Change

Promote the DGX to primary fastlane and keep it as a first-class explicit
ARM64 Lean lane, but do not move all CI to it.

Recommended steady state:

```text
lfglabs-dev/verity
  |
  |-- hz1 fastlane
  |     labels: self-hosted, linux, x64, verity, fastlane
  |     use: standby fallback and temporary host-pinned debugging
  |
  |-- hz2 x64 build
  |     labels: self-hosted, linux, x64, verity, build
  |     use: default full proof/build CI and x64 external-tool validation
  |
  |-- DGX ARM64 Lean/GPU
        labels: self-hosted, linux, ARM64, dgx-spark, verity, fastlane, gpu
        optional future label: dgx-lean or verity-arm64
        use: primary fastlane, trusted/manual/scheduled ARM64 Lean proof
             validation, and GPU jobs
```

Concrete next repo change to consider:

- Keep production fastlane jobs routed to
  `[self-hosted, linux, ARM64, dgx-spark, verity, fastlane]`.
- Add a scheduled or manually triggered `DGX Lean validation` job that reuses
  the validation task set and routes to
  `[self-hosted, linux, ARM64, dgx-spark, gpu]`.
- Keep it separate from required PR checks until it has passed repeatedly and
  the x64 external-tool assumptions have been removed or split by architecture.
- If the label list becomes hard to read, add a new runner label such as
  `dgx-lean` or `verity-arm64` and route only explicit DGX Lean jobs to it.

## Adding New Servers

For a new CPU server:

1. Install the official GitHub runner as a systemd service with this repo's
   `scripts/install_self_hosted_runner.sh`.
2. Start with one build runner per 8-core host.
3. Add precise labels such as `verity,build,cpu-16,mem-128g,<host-label>`.
4. Run `runner-lean-validation.yml` against the proposed label set.
5. Compare `make check`, `lake build`, `lake build PrintAxioms`, and
   `PrintAxioms report` before adding the host to production routing.

Do not add several full build runners to the same host unless per-job
`LEAN_NUM_THREADS` is lowered and measured. Verity's Lean jobs are CPU and cache
intensive; oversubscription makes reliability and tail latency worse.

## Minimal Context For Future Agents

```md
Verity uses official GitHub Actions self-hosted runners installed as systemd
services. Route by labels and capability, not by hostname.

Current production:
- 88.99.4.254: one x64 build/proof runner, labels `verity,build,hetzner,hz2`
- 95.216.244.60: one x64 standby fastlane runner, labels
  `verity,fastlane,hetzner,hz1`
- spark-de79 DGX: one ARM64 primary fastlane/GPU/Lean validation runner,
  labels `verity,fastlane,dgx,dgx-spark,gpu,nvidia`

Rules:
- Keep fastlane and full proof/build jobs on separate labels.
- Do not run two full `LEAN_NUM_THREADS=8` Verity builds on one 4C/8T host.
- Add build capacity by adding machines before adding same-host runner count.
- DGX runs normal fastlane PR CI only. Use explicit `dgx-spark,gpu` or future
  `dgx-lean` / `verity-arm64` labels for heavier trusted ARM64/GPU jobs.
- Keep x64 build CI for `solc`, Foundry, and x64 artifact assumptions until
  those paths are split or proven portable.
- Keep runner systemd services hardened with `KillMode=control-group`.
- Maintain `/srv/verity-ci-cache`; sticky caches are useful but must be pruned.
- Use `.github/workflows/runner-lean-validation.yml` to qualify new machines.
```
