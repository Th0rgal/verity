# Self-Hosted CI Runner

This repository can run `verify.yml` on a dedicated Linux server using two
GitHub Actions self-hosted runners that share a persistent cache root.

## Runner layout

- Runner `1`: `self-hosted,linux,x64,verity,build,cpu-8,mem-64g`
- Runner `2`: `self-hosted,linux,x64,verity,build,build-heavy,cpu-8,mem-64g`
- Shared cache root: `/srv/verity-ci-cache`

`build-heavy` is reserved for the most expensive jobs so they do not run
concurrently on both runner services.

## Workflow behavior

- `verify.yml` runs on the dedicated server.
- `docs.yml` and `issue-intake-guard.yml` stay on GitHub-hosted runners.
- Lean and compiler caches persist on disk under `/srv/verity-ci-cache`.
- Pull request cache buckets can seed themselves from `main` via the existing
  cache key scheme.
- Jobs still use a fresh checkout; only the expensive tool and build state is
  persisted.

## Server bootstrap

Run the bootstrap script on the CI host as `root`:

```bash
cd /path/to/verity
./scripts/install_self_hosted_runner.sh
```

That prepares:

- package dependencies (`clang`, `lld`, `ccache`, `jq`, `libgmp`, `libuv`, and friends)
- the `github-runner` user
- `/opt/actions-runner`
- `/srv/verity-ci-cache`

## Register the runners

1. In GitHub, open:
   `Repository Settings -> Actions -> Runners -> New self-hosted runner`
2. Copy a registration token for the repository.
3. Run:

```bash
RUNNER_URL=https://github.com/lfglabs-dev/verity \
RUNNER_TOKEN=<registration-token> \
./scripts/install_self_hosted_runner.sh
```

The script installs two systemd-managed runner services and starts them.

## Notes

- The shared cache root is intentionally outside the checkout workspace so it
  survives `actions/checkout`.
- Branch and PR caches are isolated by key, but they can still seed from
  `main`.
- If this repository needs to accept untrusted fork PRs, do not expose secrets
  or unrestricted network access to this server.
