#!/usr/bin/env bash
set -euo pipefail

workflow="${WORKFLOW:-verify.yml}"
ref="${1:-$(git branch --show-current 2>/dev/null || echo main)}"
dest="${2:-.}"
run_id="${RUN_ID:-}"

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

find_artifact_dir() {
  local root="$1"
  local suffix="$2"
  local hit
  hit="$(find "$root" -type d -path "*/$suffix" | head -n 1 || true)"
  if [ -n "$hit" ]; then
    printf '%s\n' "$hit"
  else
    printf '%s\n' "$root"
  fi
}

require_cmd gh
require_cmd git

repo="$(gh repo view --json nameWithOwner --jq .nameWithOwner)"
if [ -z "$run_id" ]; then
  run_id="$(
    gh run list \
      --repo "$repo" \
      --workflow "$workflow" \
      --branch "$ref" \
      --json databaseId,status,conclusion \
      --jq 'map(select(.status == "completed" and .conclusion == "success")) | .[0].databaseId'
  )"
fi

if [ -z "$run_id" ] || [ "$run_id" = "null" ]; then
  echo "no successful $workflow run found for ref '$ref'" >&2
  exit 1
fi

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

echo "Downloading artifacts from run $run_id in $repo"
gh run download "$run_id" --repo "$repo" -n generated-yul -D "$tmp_dir/generated-yul"
gh run download "$run_id" --repo "$repo" -n generated-yul-patched -D "$tmp_dir/generated-yul-patched"
gh run download "$run_id" --repo "$repo" -n verity-compiler-binaries -D "$tmp_dir/verity-compiler-binaries"

mkdir -p "$dest/compiler/yul" "$dest/compiler/yul-patched" "$dest/.lake/build/bin"

baseline_src="$(find_artifact_dir "$tmp_dir/generated-yul" "compiler/yul")"
patched_src="$(find_artifact_dir "$tmp_dir/generated-yul-patched" "compiler/yul-patched")"
bin_src="$(find_artifact_dir "$tmp_dir/verity-compiler-binaries" "compiler/bin")"

cp -R "$baseline_src/." "$dest/compiler/yul/"
cp -R "$patched_src/." "$dest/compiler/yul-patched/"
cp -R "$bin_src/." "$dest/.lake/build/bin/"

chmod +x \
  "$dest/.lake/build/bin/verity-compiler" \
  "$dest/.lake/build/bin/verity-compiler-patched" \
  "$dest/.lake/build/bin/difftest-interpreter"

echo "Restored compiler artifacts into:"
echo "  $dest/compiler/yul"
echo "  $dest/compiler/yul-patched"
echo "  $dest/.lake/build/bin"
