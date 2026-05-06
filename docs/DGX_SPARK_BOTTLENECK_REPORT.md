# DGX Spark CI Bottleneck Report

Date: 2026-05-06  
Host: `spark-de79` / `dgx-spark-gpu-1`  
Repo revision measured: `3157166c` (`main`)  
Tooling: Lean 4.22.0, Lake 5.0.0, `LEAN_NUM_THREADS=4` except thread-scaling tests

## Method

I ran Verity CI-sized tasks directly on the DGX in an isolated checkout at `/tmp/verity-dgx-profile`, using the existing runner Lean package cache and a fresh `.lake/build` when measuring cold-ish build work. Each command was wrapped by `scripts/profile_ci_resources.py`, which records wall time, GNU `time -v`, `/proc/stat` CPU/iowait samples, `/proc/meminfo`, `/proc/diskstats`, and `nvidia-smi`.

Raw result JSON and logs were left on the DGX under `/tmp/verity-dgx-results` and copied locally to `/tmp/verity-dgx-results` during analysis.

## Stage Timings

| Stage | Command | Wall | Effective CPU | Peak RSS | Disk writes | GPU util |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Python/check gate | `make check` | 33.6s | 99% | 64 MiB | 7.8 MB | 0% |
| Root Lean build, cold-ish | `lake build` | 112.4s | 188% | 1.6 GiB | 232 MB | 0% |
| Root Lean build, warm | `lake build` | 0.5s | 90% | 526 MiB | 0 MB | 0% |
| Full proof/axiom target | `lake build PrintAxioms` | 238.5s | 399% | 3.0 GiB | 733 MB | 0% |
| Axiom report execution | `lake env lean PrintAxioms.lean` | 80.2s | 104% | 1.7 GiB | 5.8 MB | 0% |
| Compiler/interpreter exes | `lake build verity-compiler verity-compiler-patched difftest-interpreter gas-report` | 80.5s | 271% | 1.8 GiB | 1001 MB | 0% |

## Thread Scaling

| `LEAN_NUM_THREADS` | `lake build` wall | Effective CPU | Peak RSS |
| ---: | ---: | ---: | ---: |
| 1 | 161.3s | 127% | 1.6 GiB |
| 2 | 123.5s | 169% | 1.7 GiB |
| 4 | 112.4s | 188% | 1.6 GiB |
| 8 | 110.9s | 191% | 1.6 GiB |

More cores help up to about 4 Lean threads, then flatten. The 20-core DGX is not close to saturated for the root build; average host CPU was about 10% of 20 cores, i.e. roughly two cores. This is dependency graph and single-module elaboration limited, not hardware core-count limited.

## Module Hotspots

Selected module `:olean` rebuild times after priming dependencies with `lake build PrintAxioms`:

| Module | Rebuild time |
| --- | ---: |
| `PrintAxioms` | 81.0s |
| `Compiler.Proofs.IRGeneration.SourceSemantics` | 31.3s |
| `Compiler.Proofs.IRGeneration.FunctionBody` | 19.3s |
| `Compiler.MainTest` | 17.2s |
| `Compiler.Proofs.EndToEnd` | 13.1s |
| `Compiler.Proofs.IRGeneration.Function` | 8.4s |
| `Compiler.TypedIRCompilerCorrectness` | 8.1s |
| `Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas` | 7.5s |
| `Compiler.Proofs.YulGeneration.StatementEquivalence` | 4.8s |
| `Compiler.Proofs.YulGeneration.Preservation` | 4.0s |

## Bottlenecks

1. `lake build PrintAxioms` is the largest CI-sized stage measured at 238s. It uses about four effective cores and only 3 GiB RSS, so it is compute/elaboration bound, not RAM, disk, or GPU bound.
2. `lake env lean PrintAxioms.lean` costs another 80s and is effectively single-core. The biggest actionable single target is the generated `PrintAxioms` file/report path.
3. Root `lake build` has poor scaling beyond 2-4 Lean threads. Upgrading to more CPU cores will not materially improve it unless the Lean dependency graph or hotspot modules are split.
4. Compiler executable builds write about 1 GB and use ~2.7 effective cores, but iowait stayed near zero. Disk bandwidth is not the limiting factor on the DGX NVMe.
5. `make check` is single-core Python and already short. Optimizing it is lower leverage unless it starts growing.
6. GPU utilization was 0% for all Verity CI workloads tested. GPU upgrades will not speed up these Lean/Python/compiler tasks.

## Recommendations

1. Optimize `PrintAxioms` first: reduce generated theorem set size where possible, split the generated file by namespace/package, or cache/report only changed theorem groups. This is the biggest direct win.
2. Split large Lean hotspots, especially `IRGeneration.SourceSemantics`, `IRGeneration.FunctionBody`, `Compiler.MainTest`, and `EndToEnd`, so Lake has more independent ready work and less single-module elaboration.
3. Keep `LEAN_NUM_THREADS` around 4 for DGX Verity CI. Higher values add little for root builds and can increase contention for other DGX work.
4. Do not buy more RAM or faster storage for this workload. Peak observed memory was under 9 GiB host-used during these runs on a 119 GiB machine, and iowait was consistently near zero.
5. Keep the DGX useful as a fast ARM64 Lean lane, but treat it as CPU-bound Lean infrastructure, not GPU acceleration infrastructure.
