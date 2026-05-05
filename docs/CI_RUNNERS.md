# Verity CI Runner Architecture

This repository uses the official GitHub Actions runner installed directly as
`systemd` services on owned machines. Do not add ARC, GARM, Kubernetes, Docker
runner wrappers, Nomad, or autoscaling until the operational pain clearly
justifies that extra layer.

## Current Topology

```text
GitHub Actions for lfglabs-dev/verity
  |
  |-- build-88-99-4-254-1
  |     host: 88.99.4.254
  |     role: heavy Lean/build/proof jobs
  |     labels: self-hosted, linux, x64, verity, build, hetzner, hz2
  |
  |-- tmd-verity-fastlane-1
  |     host: 95.216.244.60
  |     role: standby x64 fastlane fallback
  |     labels: self-hosted, linux, x64, verity, fastlane, hetzner, hz1
  |
  |-- dgx-spark-gpu-1
        host: spark-de79 over Tailscale
        role: primary fastlane, trusted GPU jobs, explicit ARM64 Lean validation
        labels: self-hosted, linux, ARM64, verity, fastlane, dgx, dgx-spark,
                gpu, nvidia
```

The workflows route by capability, not by hostname:

```yaml
runs-on: [self-hosted, linux, ARM64, dgx-spark, verity, fastlane]
runs-on: [self-hosted, linux, x64, verity, build]
runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
```

Host labels such as `hz1`, `hz2`, and `ci-host-*` are inventory labels. Use
them only for temporary debugging or deliberate host pinning.

## Mindset

- Keep fast jobs and long proof/build jobs on separate runner labels.
- Prefer one full Verity build runner per 8-core host. Lean jobs commonly use
  `LEAN_NUM_THREADS=8`; two such jobs on one 8-core host oversubscribe CPU,
  memory bandwidth, and the Lake cache.
- Add more build capacity by adding more machines first. Add more runner
  services on the same machine only after lowering per-job thread counts or
  proving the jobs are light enough.
- Use precise repo-specific labels. A Verity workflow should require `verity`
  so generic self-hosted jobs from other repositories cannot land here by
  accident.
- Keep `/srv/verity-ci-cache` on a large disk and maintain it. Sticky Lake
  caches make CI fast, but stale `lake-build`, `compiler-ccache`, artifacts,
  Docker cache, and `/tmp/verity-main-test-*` directories must be pruned.
- Do not run untrusted public fork PRs on these machines. Self-hosted runners
  execute repository code on owned hosts.
- The DGX is especially sensitive. It now runs the lightweight Verity
  fastlane jobs, so keep that route limited to short Python/GitHub API checks
  and do not add full build/proof, Foundry, or external x64 tooling work to
  the DGX without a separate validation lane.

## Adding A CPU Server

1. Create or reuse a dedicated runner user, runner root, and cache root.
2. Register exactly one build runner first.
3. Add host inventory labels.
4. Confirm the runner appears online and idle in GitHub.
5. Trigger `Verify proofs` with `workflow_dispatch`.

Use the repo script as root:

```bash
RUNNER_URL=https://github.com/lfglabs-dev/verity \
RUNNER_TOKEN=<registration-token> \
RUNNER_PROFILE=build \
RUNNER_COUNT=1 \
RUNNER_NAME_PREFIX=<short-hostname>-verity-build \
RUNNER_LABELS_1=verity,build,hetzner,<host-label>,cpu-8,mem-64g \
scripts/install_self_hosted_runner.sh
```

If the new host has more cores, prefer labels that describe reality, for
example `cpu-16,mem-128g`. Do not change workflow routing to those labels until
you intentionally want to require that capacity.

## Adding The DGX Spark

The DGX should be isolated from normal Verity CI. Register it for trusted GPU
workflows and explicit ARM64 Lean validation. At organization level, place it
in a restricted runner group instead of the default group.

```bash
RUNNER_URL=https://github.com/lfglabs-dev/verity \
RUNNER_TOKEN=<registration-token> \
RUNNER_PROFILE=dgx-gpu \
RUNNER_ARCH=arm64 \
RUNNER_COUNT=1 \
RUNNER_NAME_PREFIX=dgx-spark-gpu \
RUNNER_LABELS_1=verity,fastlane,dgx,dgx-spark,gpu,nvidia,home,arm64-gb10 \
scripts/install_self_hosted_runner.sh
```

GPU and ARM64 Lean validation jobs should route explicitly:

```yaml
runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
```

Fastlane jobs intentionally route to the DGX:

```yaml
runs-on: [self-hosted, linux, ARM64, dgx-spark, verity, fastlane]
```

Do not let ordinary Verity `build` jobs use the DGX labels. Do not add the
`build` label to the DGX runner unless you have separately proven the ARM64
Lean build is reliable for required CI and intentionally want full Verity CI to
schedule there.

If DGX Lean validation becomes a regular lane, prefer adding a dedicated label
such as `dgx-lean` or `verity-arm64` instead of reusing `verity,build`. That
keeps x64 production proof CI separate from ARM64 validation and avoids routing
jobs with x64-only `solc`, Foundry, or artifact assumptions to the DGX.

The repository includes a manual-only smoke test:

```bash
gh workflow run dgx-smoke.yml
```

The repository also includes a manual-only runner benchmark workflow for
forcing real Verity tasks onto a chosen label set:

```bash
gh workflow run runner-benchmark.yml \
  -f task=checks \
  -f runner_labels_json='["self-hosted","linux","ARM64","dgx-spark","gpu"]'
```

Use it when adding a new host or comparing runner profiles. Keep it
`workflow_dispatch` only.

For deeper runner qualification, use the manual Lean validation workflow:

```bash
gh workflow run runner-lean-validation.yml \
  -f runner_labels_json='["self-hosted","linux","ARM64","dgx-spark","gpu"]' \
  -f include_compiler_core=true
```

This runs `make check`, full `lake build`, PrintAxioms/audit checks, and
compiler-core validation. On ARM64 it skips x64-only `solc` validation and runs
portable generated-Yul checks instead.

The latest benchmark report is in
[`docs/CI_RUNNER_BENCHMARK_REPORT.md`](CI_RUNNER_BENCHMARK_REPORT.md).

## Maintenance Expectations

Each CI host should have the weekly Verity maintenance timer installed. It
should:

- run `scripts/ci_local_persistence.sh cleanup`;
- prune stale Lake and compiler ccache buckets;
- remove stale Verity temp directories;
- vacuum journald by age and size;
- prune unused Docker image and builder cache.

The target health state is:

- all registered runners online;
- no stale offline runner registrations;
- `95.216.244.60` stays online as an x64 fastlane fallback and has enough free
  disk for temporary host-pinned debugging;
- `88.99.4.254` has enough free disk for sticky build caches;
- no more than one active full `LEAN_NUM_THREADS=8` build job per 8-core host.

Runner services should also have the Verity systemd stop hardening drop-in
installed:

```ini
[Service]
KillMode=control-group
SendSIGKILL=yes
TimeoutStopSec=90s
```

GitHub's generated service uses `KillMode=process`, which can leave cancelled
job children running. The repository installer writes this drop-in for future
runner installs.
