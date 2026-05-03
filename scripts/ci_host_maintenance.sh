#!/usr/bin/env bash
set -euo pipefail

CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAKE_BUILD_MAX_AGE_DAYS="${LAKE_BUILD_MAX_AGE_DAYS:-21}"
COMPILER_CCACHE_MAX_AGE_DAYS="${COMPILER_CCACHE_MAX_AGE_DAYS:-21}"
ARTIFACT_MAX_AGE_HOURS="${ARTIFACT_MAX_AGE_HOURS:-24}"
JOURNAL_VACUUM_TIME="${JOURNAL_VACUUM_TIME:-14d}"
JOURNAL_VACUUM_SIZE="${JOURNAL_VACUUM_SIZE:-1G}"
DOCKER_PRUNE_FILTER="${DOCKER_PRUNE_FILTER:-until=168h}"

usage() {
  cat <<'EOF'
Usage:
  scripts/ci_host_maintenance.sh run
  scripts/ci_host_maintenance.sh install-systemd

Subcommands:
  run              Prune stale Verity CI cache entries, vacuum journald, and prune unused Docker data.
  install-systemd  Install and enable a weekly systemd timer for this script.

Environment:
  CACHE_ROOT                    Default: /srv/verity-ci-cache
  LAKE_BUILD_MAX_AGE_DAYS       Default: 21
  COMPILER_CCACHE_MAX_AGE_DAYS  Default: 21
  ARTIFACT_MAX_AGE_HOURS        Default: 24
  JOURNAL_VACUUM_TIME           Default: 14d
  JOURNAL_VACUUM_SIZE           Default: 1G
  DOCKER_PRUNE_FILTER           Default: until=168h
EOF
}

require_root() {
  if [ "$(id -u)" -ne 0 ]; then
    echo "Run this script as root." >&2
    exit 1
  fi
}

prune_tree() {
  local dir="$1"
  local max_age_days="$2"
  local label="$3"

  if [ ! -d "$dir" ]; then
    return
  fi

  local count=0
  while IFS= read -r -d '' entry; do
    rm -rf "$entry"
    count=$((count + 1))
  done < <(find "$dir" -mindepth 1 -maxdepth 1 -mtime +"$max_age_days" -print0 2>/dev/null)

  echo "${label}: removed ${count} entries older than ${max_age_days} days"
}

run_maintenance() {
  require_root

  mkdir -p "$CACHE_ROOT"
  prune_tree "$CACHE_ROOT/lake-build" "$LAKE_BUILD_MAX_AGE_DAYS" "lake-build cache"
  prune_tree "$CACHE_ROOT/compiler-ccache" "$COMPILER_CCACHE_MAX_AGE_DAYS" "compiler ccache"

  if [ -x "$SCRIPT_DIR/ci_local_persistence.sh" ]; then
    "$SCRIPT_DIR/ci_local_persistence.sh" cleanup --max-age-hours "$ARTIFACT_MAX_AGE_HOURS"
  fi

  if command -v journalctl >/dev/null 2>&1; then
    journalctl --vacuum-time="$JOURNAL_VACUUM_TIME"
    journalctl --vacuum-size="$JOURNAL_VACUUM_SIZE"
  fi

  if command -v docker >/dev/null 2>&1; then
    docker image prune -af --filter "$DOCKER_PRUNE_FILTER"
    docker builder prune -af --filter "$DOCKER_PRUNE_FILTER"
  fi
}

install_systemd() {
  require_root

  local script_path
  script_path="$(readlink -f "$0")"

  cat > /etc/systemd/system/verity-ci-host-maintenance.service <<EOF
[Unit]
Description=Verity CI host maintenance
Documentation=file://${script_path}

[Service]
Type=oneshot
ExecStart=${script_path} run
EOF

  cat > /etc/systemd/system/verity-ci-host-maintenance.timer <<'EOF'
[Unit]
Description=Weekly Verity CI host maintenance

[Timer]
OnCalendar=Sun *-*-* 04:30:00
Persistent=true
RandomizedDelaySec=30m

[Install]
WantedBy=timers.target
EOF

  systemctl daemon-reload
  systemctl enable --now verity-ci-host-maintenance.timer
  systemctl list-timers verity-ci-host-maintenance.timer
}

case "${1:-}" in
  run)
    run_maintenance
    ;;
  install-systemd)
    install_systemd
    ;;
  *)
    usage >&2
    exit 1
    ;;
esac
