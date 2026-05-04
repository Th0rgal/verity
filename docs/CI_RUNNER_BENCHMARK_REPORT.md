# Verity Self-Hosted Runner Benchmark Report

Date: 2026-05-04

This report compares the three connected self-hosted runners by forcing the
same Verity repository tasks onto each runner with the manual
`runner-benchmark.yml` workflow.

## Current Runner Architecture

```text
lfglabs-dev/verity GitHub Actions
  |
  |-- build-88-99-4-254-1
  |     host: 88.99.4.254
  |     architecture: Linux X64
  |     role: heavy x64 Lean/build/proof jobs
  |     labels: self-hosted, Linux, X64, verity, build, cpu-8, mem-64g,
  |             build-heavy, ci-host-88-99-4-254, hetzner, hz2
  |
  |-- tmd-verity-fastlane-1
  |     host: 95.216.244.60
  |     architecture: Linux X64
  |     role: short checks, change detection, failure hints
  |     labels: self-hosted, Linux, X64, verity, fastlane, cpu-8,
  |             ci-host-95-216-244-60, hetzner, hz1
  |
  |-- dgx-spark-gpu-1
        host: spark-de79 over Tailscale
        architecture: Linux ARM64
        role: trusted manual GPU jobs and explicit ARM64 experiments
        labels: self-hosted, Linux, ARM64, dgx, dgx-spark, gpu, nvidia,
                home, arm64-gb10
```

Production workflow routing remains capability based:

```yaml
runs-on: [self-hosted, linux, x64, verity, fastlane]
runs-on: [self-hosted, linux, x64, verity, build]
runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
```

The DGX intentionally does not have the `verity`, `build`, or `fastlane`
labels, so ordinary Verity CI cannot land there accidentally.

## Host Inventory Observed During Benchmark

| Runner | Host | CPU | RAM | Root disk free | Notes |
| --- | --- | --- | --- | --- | --- |
| `build-88-99-4-254-1` | `Ubuntu-2404-noble-amd64-base` | Intel i7-6700, 4C/8T | 62 GiB | 682 GiB free, 19% used | Healthy disk, best current x64 build host. |
| `tmd-verity-fastlane-1` | `tmd` | Intel i7-7700, 4C/8T | 62 GiB | 94 GiB free, 93% used | Still disk constrained; keep fastlane-only. |
| `dgx-spark-gpu-1` | `spark-de79` | 20 ARM64 cores: Cortex-X925 + Cortex-A725 | 119 GiB | 1.6 TiB free, 56% used | Much faster on the tested Verity tasks; keep explicitly routed. |

## Benchmarked Tasks

Both tasks were real repository CI work, dispatched through GitHub Actions and
forced onto each runner:

- `checks`: `make check`
- `evmyullean-smoke`: `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeSmokeTest`

Lean task settings:

- `LEAN_NUM_THREADS=4`
- host-local sticky caches enabled
- benchmark cache keys were architecture-specific

## Results

Command elapsed time from `/usr/bin/time`:

| Runner | `make check` | EVM-Yul-Lean smoke target | Relevant run IDs |
| --- | ---: | ---: | --- |
| `dgx-spark-gpu-1` | 34.59s | 2m 25.79s | `25328725290`, `25328741226` |
| `build-88-99-4-254-1` | 1m 15.29s | 5m 24.54s | `25328710343`, `25328726708` |
| `tmd-verity-fastlane-1` | 1m 20.39s | 5m 13.74s | `25328712174`, `25328739523` |

Job wall-clock time including checkout and setup:

| Runner | `make check` job | EVM-Yul-Lean smoke job |
| --- | ---: | ---: |
| `dgx-spark-gpu-1` | 47s | 4m 12s |
| `build-88-99-4-254-1` | 1m 24s | 6m 57s |
| `tmd-verity-fastlane-1` | 1m 31s | 6m 53s |

## Interpretation

The DGX is clearly faster for the tested Python/check workload and the tested
Lean proof target, even at only `LEAN_NUM_THREADS=4`. It is a credible candidate
for dedicated ARM64 Lean proving lanes.

That does not mean the DGX should receive normal Verity CI yet. The current
full workflow still has x64-oriented assumptions in places, including
Linux-amd64 Solidity tooling, Foundry/differential test paths, generated
compiler artifacts, and existing cache expectations. The safe path is to add
explicit DGX/ARM64 Lean jobs first, not to add `verity,build` labels to the
DGX.

The two x64 Hetzner hosts are close on the tested Lean target. The `hz2` build
host remains the right default x64 build runner because it has far more free
disk and less unrelated service pressure. The `hz1` host should stay fastlane
only until its disk pressure is fixed.

## Reliability Finding

During benchmarking, `build-88-99-4-254-1` got stuck on a cancelled manual
`Verify proofs` clean build from `native-evmyullean-public-correctness`.
GitHub marked the job cancelled, but child `lake`/`difftest-interpreter`
processes continued under the runner and kept the runner busy. The root cause
was the GitHub-generated systemd unit using:

```ini
KillMode=process
```

That only kills the runner process on service stop. It can leave the job
process tree alive.

Applied live fix on all three runner hosts:

```ini
[Service]
KillMode=control-group
SendSIGKILL=yes
TimeoutStopSec=90s
```

The repository installer now writes the same systemd drop-in so future runner
installs inherit this behavior.

## Recommendations

1. Keep the current production routing:
   - `hz2`: one x64 `verity,build` runner
   - `hz1`: one x64 `verity,fastlane` runner
   - DGX: GPU/ARM64-only explicit runner

2. Add an explicit manual or scheduled ARM64 Lean lane for the DGX before using
   it for normal CI:

   ```yaml
   runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
   ```

   Start with:

   - `make check`
   - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeSmokeTest`
   - selected proof targets with no x64 external-tool dependency

3. Do not add `verity`, `build`, or `fastlane` to the DGX yet. If we want a
   Verity-specific DGX lane, add a new label such as `verity-arm64` or
   `dgx-lean` and route only explicit jobs to it.

4. Benchmark DGX Lean scaling separately with `LEAN_NUM_THREADS=8`, `12`, and
   `16`. The first run used `4` threads and was already faster; thread scaling
   should be measured before setting a default.

5. Keep `hz1` fastlane-only until disk usage is comfortably below 85%.
   At benchmark time it was still at 93% root usage.

6. Keep one full build runner per 8-core x64 host. More runner services on the
   same 4C/8T machines would oversubscribe Lean and make tail latency worse.

7. Keep `runner-benchmark.yml` manual-only. It is useful for onboarding new
   hosts and comparing labels, but it should not run on every push.

## Minimal Context For Future Agents

```md
Verity uses official GitHub Actions self-hosted runners installed as systemd
services. Route by labels and capability, not by hostname.

Current production:
- 88.99.4.254: one x64 build/proof runner, labels `verity,build,hetzner,hz2`
- 95.216.244.60: one x64 fastlane runner, labels `verity,fastlane,hetzner,hz1`
- spark-de79 DGX: one ARM64 GPU runner, labels `dgx,dgx-spark,gpu,nvidia`

Rules:
- Do not run two full `LEAN_NUM_THREADS=8` Verity builds on one 4C/8T host.
- Add build capacity by adding machines before adding same-host runner count.
- Keep DGX off normal CI; use explicit `dgx-spark,gpu` or future `dgx-lean`
  labels for trusted/manual ARM64/GPU jobs.
- Keep runner systemd services hardened with `KillMode=control-group` so
  cancelled jobs do not leave child processes running.
- Maintain `/srv/verity-ci-cache`; sticky caches are useful but must be pruned.
```
