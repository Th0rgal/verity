# Verity Runner Hardware Analysis

Date: 2026-05-06

This note explains why the DGX Spark is much faster than the two current
Hetzner x64 runners on real Verity CI work, what the slow CI tasks actually do,
where GPU acceleration can help, and which hardware classes are likely to beat
the current DGX result.

Baseline timings come from
[`docs/CI_RUNNER_BENCHMARK_REPORT.md`](CI_RUNNER_BENCHMARK_REPORT.md).

## Current Hardware

Live host inspection and vendor specifications line up as follows:

| Runner | Host | CPU | Cores exposed to Linux | Max CPU clock | Cache | Memory | Disk state |
| --- | --- | --- | ---: | ---: | --- | --- | --- |
| `dgx-spark-gpu-1` | `spark-de79` | NVIDIA GB10 / Grace Blackwell Arm CPU: 10 Cortex-X925 + 10 Cortex-A725 | 20 physical cores, no SMT | X925 up to 4.004 GHz, A725 up to 2.860 GHz | 25 MiB aggregate L2, 24 MiB L3 | 119 GiB available to Linux; 128 GiB LPDDR5x unified, 273 GB/s vendor bandwidth | 3.7 TiB root, about 1.6 TiB free |
| `build-88-99-4-254-1` | `88.99.4.254` | Intel Core i7-6700, Skylake | 4 cores / 8 SMT threads | up to 4.0 GHz | 1 MiB aggregate L2, 8 MiB L3 | 62 GiB DDR4/DDR3L-class, 34.1 GB/s vendor max bandwidth | 873 GiB root, about 699 GiB free |
| `tmd-verity-fastlane-1` | `95.216.244.60` | Intel Core i7-7700, Kaby Lake | 4 cores / 8 SMT threads | up to 4.2 GHz | 1 MiB aggregate L2, 8 MiB L3 | 62 GiB DDR4/DDR3L-class, dual-channel | 1.4 TiB root, about 132 GiB free |

The most important comparison is not clock speed. It is:

- DGX has 20 real CPU cores, while each Hetzner host has 4 physical cores plus
  SMT.
- DGX has much more memory bandwidth: NVIDIA publishes 273 GB/s for the Spark,
  while the i7-6700 class is 34.1 GB/s max memory bandwidth and the i7-7700 is
  similar dual-channel DDR4 generation hardware.
- DGX has newer high-performance CPU cores and much larger per-job headroom.
- DGX has a much larger, healthier local disk and cache area.

## Measured Verity Speedup

Cold-ish validation measurements:

| Step | DGX ARM64 | Hz2 i7-6700 | Hz1 i7-7700 | DGX vs best x64 |
| --- | ---: | ---: | ---: | ---: |
| `make check` | 34s | 75s | 82s | 2.2x |
| `lake build` | 111s | 279s | 275s | 2.5x |
| `lake build PrintAxioms` | 231s | 588s | 572s | 2.5x |
| `PrintAxioms report` | 81s | 171s | 175s | 2.1x |
| `build verity-compiler` | 31s | 142s | not run | 4.6x |
| `build difftest-interpreter` | 101s | 402s | not run | 4.0x |

The DGX is faster on the CPU-bound Lean and compiler-core tasks. These numbers
do not require GPU acceleration to explain them.

## Why The DGX Is Faster

### More Real CPU Parallelism

Verity's full proof/build jobs use `LEAN_NUM_THREADS=8`. On the Intel hosts,
that asks an 8-thread Lean job to run on a 4-core CPU with SMT. SMT is useful,
but two hardware threads on one core do not behave like two independent cores
for proof elaboration, hashing, allocation, parsing, code generation, and
artifact writes.

On the DGX, an 8-thread Lean job has 20 physical Arm cores available. The job
can use eight real cores while the OS, GitHub runner, Lake, Python checks, and
I/O helpers still have spare cores. That directly improves both average runtime
and tail latency.

### Memory Bandwidth And Cache Pressure

Lean proof builds allocate and traverse a lot of structured data: syntax trees,
environments, expressions, constraints, theorem metadata, imported module
state, and generated `.olean`/native build artifacts. This is not a tiny
compute kernel that lives entirely in L1.

The DGX Spark's LPDDR5x system memory is published at 273 GB/s. The i7-6700 is
published at 34.1 GB/s max memory bandwidth. Even allowing for real-world
differences, the DGX has a much wider memory system for the kind of
multi-threaded compiler workload Verity runs.

The DGX also has materially more CPU cache than the Intel hosts: live `lscpu`
reports 25 MiB aggregate L2 and 24 MiB L3, versus 1 MiB aggregate L2 and 8 MiB
L3 on each Intel host.

### Newer Cores

The Intel machines are 2015-2017 desktop CPUs. The i7-6700 is Skylake, and the
i7-7700 is Kaby Lake. The DGX Spark CPU complex is current Arm high-performance
silicon built into NVIDIA GB10. For Lean, the relevant win is modern
single-thread throughput combined with enough physical cores to avoid
oversubscription.

### Healthier Storage And Caches

Verity benefits from sticky Lake and compiler caches, but stale cache pressure
can hurt both speed and reliability. The DGX root disk is large and currently
has about 1.6 TiB free. The standby x64 fastlane host is still much tighter at
about 132 GiB free and has historically needed cleanup.

This is not the main reason `lake build` is 2.5x faster, but it helps prevent
cache churn and reduces the chance that a run slows down because the host is
fighting disk pressure.

## What Actually Takes Time In Verity CI

### Fastlane

The fastlane jobs mostly run Python and repository consistency checks:

- workflow/spec synchronization;
- generated documentation checks;
- property manifest and coverage checks;
- path, package-boundary, storage-layout, and macro-health checks;
- Python unit tests.

These are mostly CPU-light, filesystem-heavy, and process-startup-heavy. They
benefit from the DGX because it has fast cores, idle headroom, and healthy disk,
but they do not need a GPU.

### Full `lake build`

This is the main proof/type-checking workload. It builds about 276 Lean source
files in this worktree, including contracts, compiler modules, proof modules,
and supporting packages.

Most of the time is spent in Lean frontend/elaboration/type-checking/proof
checking work and writing build artifacts. For proof-heavy modules, "compile"
does not just mean machine-code generation. It means checking definitions,
theorems, tactics, imports, generated terms, and module dependencies so Lean can
emit trusted artifacts.

This task benefits from:

- strong per-core CPU performance;
- enough physical cores for `LEAN_NUM_THREADS`;
- memory bandwidth;
- fast local caches and storage;
- avoiding two large Lean builds on the same small CPU.

It does not naturally benefit from the DGX GPU today.

### `lake build PrintAxioms` And `PrintAxioms report`

This is also Lean-heavy. Building `PrintAxioms` prepares the Lean executable or
environment needed for the axiom audit. Running the report walks theorem and
dependency information and prints/checks axiom usage.

It is CPU and memory intensive. It can parallelize partly through Lean/Lake
builds, but the report generation itself has serial sections and dependency
traversal. GPU acceleration is not a natural fit unless this tooling is
redesigned around a GPU-friendly batch kernel, which is unlikely to be worth it.

### Compiler-Core Binaries

Targets such as `verity-compiler`, `verity-compiler-patched`,
`difftest-interpreter`, and `gas-report` include Lean build work and native
binary generation/linking. The DGX result was 4x or better on the first builds,
which suggests the current x64 hosts are bottlenecked by physical cores, memory
bandwidth, and native compile/link throughput.

GPU acceleration does not help the normal Lean/C++ build path. A faster CPU,
faster linker/toolchain setup, and better ccache behavior help.

### Foundry, `solc`, And EVM Differential Work

These jobs are still x64-production-oriented. They include external tools,
generated Yul, Solidity compiler checks, Foundry tests, and interpreter runs.
Some of that work is serial, some is test-parallel, and much of it assumes x64
Linux binaries today.

Do not route these to DGX by default until ARM64 tool availability and parity
are fully boring.

## What Could Use The GPU

The DGX GPU is valuable, but not for normal Lean proof checking today.

Good GPU candidates:

- ML workloads, inference, model evaluation, and fine-tuning;
- LLM-assisted proof search experiments;
- neural premise selection, theorem ranking, or tactic suggestion;
- large embedding/indexing jobs over theorem/proof/code corpora;
- fuzzing or search loops where a learned model guides candidate generation;
- GPU-native benchmarking unrelated to the standard CI proof check.

Poor GPU candidates:

- `lake build`;
- Lean elaboration/type checking;
- `PrintAxioms`;
- Python sync checks;
- C++/Lean compiler binary builds;
- `solc` and Foundry validation.

The practical split should be: keep standard correctness CI CPU-driven; use the
DGX GPU for optional or explicit AI/proof-assistant experiments.

## Hardware That Could Be Faster

The DGX is dramatically faster than the current 4-core Intel hosts, but it is
not the ceiling for Lean CI. The best next CPU runner is probably a modern
high-clock x86 workstation/server, not another small GPU appliance.

### Best Practical Next CPU Host

A modern 16-core Zen 5 host, for example AMD Ryzen 9 9950X-class hardware, is a
strong candidate:

- 16 cores / 32 threads;
- up to 5.7 GHz boost;
- 4.3 GHz base;
- 64 MiB L3;
- AVX512 support;
- commodity x64 Linux compatibility.

Expected outcome: likely faster than DGX for many x64 Lean and compiler-core
jobs if cooling and storage are good, because it combines high single-thread
performance, enough real cores for `LEAN_NUM_THREADS=8`, and native x64 tooling.
It would also remove the ARM64/x64 split for `solc`, Foundry, and binary
artifact assumptions.

### Best Workstation-Class Build Host

AMD Ryzen Threadripper 9970X-class hardware is more expensive but attractive
for many concurrent proof/build lanes:

- 32 cores / 64 threads;
- up to 5.4 GHz boost;
- 4.0 GHz base;
- 128 MiB L3;
- 4-channel DDR5 RDIMM;
- many PCIe lanes for NVMe cache disks.

Expected outcome: probably faster than DGX for full Verity CI and much better
for running multiple isolated build lanes, as long as each lane still has sane
`LEAN_NUM_THREADS` limits.

### Best Server-Class Host

AMD EPYC 9575F-class hardware is the high-end server option:

- 64 cores / 128 threads;
- up to 5.0 GHz boost;
- 4.5 GHz all-core boost;
- 256 MiB L3;
- 12-channel DDR5 with 614 GB/s per-socket published bandwidth.

Expected outcome: likely faster than DGX for aggregate CI throughput and maybe
for individual proof builds, especially with multiple runners. It is probably
overkill unless Verity needs many simultaneous full proof jobs or the same host
will serve multiple repositories.

### What I Would Buy/Test First

For Verity specifically:

1. Add one modern x64 Zen 5 CPU runner with NVMe and at least 64-128 GiB RAM.
   A Ryzen 9 9950X-class dedicated box is the most pragmatic first target.
2. Keep one runner service initially and test `LEAN_NUM_THREADS=8`, `12`, and
   `16`.
3. Compare `lake build`, `lake build PrintAxioms`, `PrintAxioms report`,
   compiler-core binary builds, and Foundry/`solc`.
4. Only add a second runner service if the host has enough cores and the first
   run does not saturate memory bandwidth or disk.

## Architecture Recommendation

Keep the current routing:

```yaml
fastlane: [self-hosted, linux, ARM64, dgx-spark, verity, fastlane]
build:    [self-hosted, linux, x64, verity, build]
gpu:      [self-hosted, linux, ARM64, dgx-spark, gpu]
```

Then add one new modern x64 `verity,build` host before considering a larger
topology change.

Recommended future topology:

```text
DGX Spark
  use: primary fastlane, explicit GPU jobs, scheduled/manual ARM64 Lean validation
  avoid: default full build, Foundry, x64 external-tool assumptions

Current i7-6700 host
  use: default x64 build until replaced; later fallback/secondary validation

Current i7-7700 host
  use: standby fastlane fallback and host-pinned debugging

New Zen 5 x64 host
  use: primary full x64 proof/build/compiler/Foundry CI
  labels: self-hosted, linux, x64, verity, build, cpu-16-or-better, mem-64g-or-better
```

Do not move all CI to the DGX. Promote it for the jobs where it is already
proven and valuable: fastlane, GPU workflows, and explicit ARM64 Lean
validation. For required production proof/build CI, the next best improvement
is a modern x64 CPU runner.

## Sources

- NVIDIA DGX Spark User Guide, hardware and performance specifications:
  <https://docs.nvidia.com/dgx/dgx-spark/hardware.html>
- Intel Core i7-6700 product specifications:
  <https://www.intel.com/content/www/us/en/products/sku/88196/intel-core-i76700-processor-8m-cache-up-to-4-00-ghz/specifications.html>
- Intel Core i7-7700 product specifications:
  <https://www.intel.com/content/www/us/en/products/sku/97128/intel-core-i77700-processor-8m-cache-up-to-4-20-ghz/specifications.html>
- AMD Ryzen 9 9950X product specifications:
  <https://www.amd.com/en/products/processors/desktops/ryzen/9000-series/amd-ryzen-9-9950x.html>
- AMD Ryzen Threadripper 9970X product specifications:
  <https://www.amd.com/en/products/processors/ryzen-threadripper/9000-series/amd-ryzen-threadripper-9970x.html>
- AMD EPYC 9575F product specifications:
  <https://www.amd.com/en/products/processors/server/epyc/9005-series/amd-epyc-9575f.html>
