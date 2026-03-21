#!/usr/bin/env bash
set -euo pipefail

exec ccache clang -fuse-ld=lld "$@"
