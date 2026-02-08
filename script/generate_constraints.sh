#!/usr/bin/env bash
set -euo pipefail

MANIFEST="specs/manifest.txt"

if [[ ! -f "$MANIFEST" ]]; then
  echo "Missing $MANIFEST (expected spec_path output_path per line)" >&2
  exit 1
fi

while IFS= read -r line; do
  line="${line%%#*}"
  line="${line#"${line%%[![:space:]]*}"}"
  line="${line%"${line##*[![:space:]]}"}"
  [[ -z "$line" ]] && continue

  set -- $line
  spec_path="${1:-}"
  out_path="${2:-}"

  if [[ -z "$spec_path" || -z "$out_path" ]]; then
    echo "Invalid manifest line: '$line' (expected spec_path output_path)" >&2
    exit 1
  fi

  python3 research/poc_constraints/dsl_to_constraints.py "$spec_path" "$out_path"
done < "$MANIFEST"
