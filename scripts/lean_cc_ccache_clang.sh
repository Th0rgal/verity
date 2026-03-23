#!/usr/bin/env bash
set -euo pipefail

# Skip ccache for link invocations (ccache cannot cache them).
# Detect linking by checking if -c flag is absent — compilation passes
# always include -c, while link invocations never do.
is_compile=false
for arg in "$@"; do
  if [ "$arg" = "-c" ]; then
    is_compile=true
    break
  fi
done

if $is_compile; then
  exec ccache clang -fuse-ld=lld "$@"
else
  exec clang -fuse-ld=lld "$@"
fi
