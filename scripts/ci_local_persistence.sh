#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  scripts/ci_local_persistence.sh mount --root ROOT --key KEY --path PATH [--fallback-key KEY]

Mount a persistent host-local directory into the checked-out workspace by
symlinking PATH to ROOT/<sanitized-key>. If the target directory is empty and a
fallback key is provided, seed it from ROOT/<sanitized-fallback-key>.
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

subcommand="${1:-}"
case "$subcommand" in
  mount)
    shift
    mount_persistent_dir "$@"
    ;;
  *)
    usage >&2
    exit 1
    ;;
esac
