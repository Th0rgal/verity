#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOOK_PATH="$ROOT_DIR/.git/hooks/pre-push"

cat > "$HOOK_PATH" <<'HOOK'
#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

scripts/run_1060_fast_gate.sh
HOOK

chmod +x "$HOOK_PATH"
echo "Installed pre-push hook: $HOOK_PATH"
echo "Hook runs: scripts/run_1060_fast_gate.sh"
