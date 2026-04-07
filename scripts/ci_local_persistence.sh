#!/usr/bin/env bash
set -euo pipefail

ARTIFACT_ROOT="/srv/verity-ci-cache/artifacts"

usage() {
  cat <<'EOF'
Usage:
  scripts/ci_local_persistence.sh mount    --root ROOT --key KEY --path PATH [--fallback-key KEY]
  scripts/ci_local_persistence.sh publish  --run-id ID --name NAME --path PATH
  scripts/ci_local_persistence.sh fetch    --run-id ID --name NAME [--timeout SECONDS]
  scripts/ci_local_persistence.sh cleanup  [--max-age-hours HOURS]

Subcommands:
  mount    Symlink a persistent host-local directory into the workspace.
  publish  Copy a build artifact (file or directory) to the shared local store.
  fetch    Wait for a local artifact to become ready, then extract/copy it.
  cleanup  Remove artifact directories older than a threshold.
EOF
}

sanitize_key() {
  printf '%s' "$1" | tr -cs 'A-Za-z0-9._-' '_'
}

is_dir_empty() {
  local dir="$1"
  if [ ! -d "$dir" ]; then
    return 0
  fi
  ! find "$dir" -mindepth 1 -print -quit | grep -q .
}

mount_persistent_dir() {
  local root="" key="" path="" fallback_key=""

  while [ "$#" -gt 0 ]; do
    case "$1" in
      --root)
        root="$2"
        shift 2
        ;;
      --key)
        key="$2"
        shift 2
        ;;
      --path)
        path="$2"
        shift 2
        ;;
      --fallback-key)
        fallback_key="$2"
        shift 2
        ;;
      *)
        echo "Unknown argument: $1" >&2
        usage >&2
        exit 1
        ;;
    esac
  done

  if [ -z "$root" ] || [ -z "$key" ] || [ -z "$path" ]; then
    usage >&2
    exit 1
  fi

  local primary_dir fallback_dir=""
  primary_dir="${root}/$(sanitize_key "$key")"
  mkdir -p "$primary_dir"

  if [ -n "$fallback_key" ]; then
    fallback_dir="${root}/$(sanitize_key "$fallback_key")"
  fi

  mkdir -p "$(dirname "$path")"
  rm -rf "$path"
  ln -s "$primary_dir" "$path"

  if ! is_dir_empty "$primary_dir"; then
    exit 0
  fi

  if [ -z "$fallback_dir" ] || [ "$fallback_dir" = "$primary_dir" ] || [ ! -d "$fallback_dir" ] || is_dir_empty "$fallback_dir"; then
    exit 0
  fi

  cp -a "$fallback_dir/." "$primary_dir/"
}

publish_artifact() {
  local run_id="" name="" path=""

  while [ "$#" -gt 0 ]; do
    case "$1" in
      --run-id) run_id="$2"; shift 2 ;;
      --name)   name="$2";   shift 2 ;;
      --path)   path="$2";   shift 2 ;;
      *) echo "Unknown argument: $1" >&2; usage >&2; exit 1 ;;
    esac
  done

  if [ -z "$run_id" ] || [ -z "$name" ] || [ -z "$path" ]; then
    echo "publish requires --run-id, --name, and --path" >&2
    usage >&2
    exit 1
  fi

  local target_dir="${ARTIFACT_ROOT}/${run_id}/${name}"
  rm -rf "$target_dir"
  mkdir -p "$target_dir"

  if [ -f "$path" ]; then
    cp -f "$path" "$target_dir/$(basename "$path")"
  elif [ -d "$path" ]; then
    cp -a "$path/." "$target_dir/"
  else
    echo "::error::publish: path does not exist: $path"
    exit 1
  fi

  touch "$target_dir/.ready"
  echo "Published artifact '${name}' to ${target_dir}"
}

fetch_artifact() {
  local run_id="" name="" timeout=60

  while [ "$#" -gt 0 ]; do
    case "$1" in
      --run-id)  run_id="$2";  shift 2 ;;
      --name)    name="$2";    shift 2 ;;
      --timeout) timeout="$2"; shift 2 ;;
      *) echo "Unknown argument: $1" >&2; usage >&2; exit 1 ;;
    esac
  done

  if [ -z "$run_id" ] || [ -z "$name" ]; then
    echo "fetch requires --run-id and --name" >&2
    usage >&2
    exit 1
  fi

  local source_dir="${ARTIFACT_ROOT}/${run_id}/${name}"
  local ready_marker="${source_dir}/.ready"

  local waited=0
  while [ ! -f "$ready_marker" ] && [ "$waited" -lt "$timeout" ]; do
    sleep 2
    waited=$((waited + 2))
  done

  if [ ! -f "$ready_marker" ]; then
    echo "::warning::Local artifact '${name}' not ready after ${timeout}s; falling back to GitHub"
    return 2
  fi

  # Find tarball in the artifact directory
  local tarball=""
  for f in "$source_dir"/*.tar; do
    if [ -f "$f" ]; then
      tarball="$f"
      break
    fi
  done

  if [ -n "$tarball" ]; then
    tar -xf "$tarball"
    echo "Restored artifact '${name}' from local tarball"
  else
    # Directory artifact: copy contents into a local directory named after the artifact
    mkdir -p "$name"
    cp -a "$source_dir/." "$name/"
    rm -f "$name/.ready"
    echo "Restored artifact '${name}' from local directory"
  fi
}

cleanup_artifacts() {
  local max_age_hours=24

  while [ "$#" -gt 0 ]; do
    case "$1" in
      --max-age-hours) max_age_hours="$2"; shift 2 ;;
      *) echo "Unknown argument: $1" >&2; usage >&2; exit 1 ;;
    esac
  done

  if [ ! -d "$ARTIFACT_ROOT" ]; then
    mkdir -p "$ARTIFACT_ROOT"
    return 0
  fi

  local count=0
  while IFS= read -r -d '' dir; do
    rm -rf "$dir"
    count=$((count + 1))
  done < <(find "$ARTIFACT_ROOT" -maxdepth 1 -mindepth 1 -type d -mmin +"$((max_age_hours * 60))" -print0 2>/dev/null)

  if [ "$count" -gt 0 ]; then
    echo "Cleaned up ${count} stale artifact directories"
  fi
}

subcommand="${1:-}"
case "$subcommand" in
  mount)
    shift
    mount_persistent_dir "$@"
    ;;
  publish)
    shift
    publish_artifact "$@"
    ;;
  fetch)
    shift
    fetch_artifact "$@"
    ;;
  cleanup)
    shift
    cleanup_artifacts "$@"
    ;;
  *)
    usage >&2
    exit 1
    ;;
esac
