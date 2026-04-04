#!/usr/bin/env bash
set -euo pipefail

if [ "$(id -u)" -ne 0 ]; then
  echo "Run this script as root." >&2
  exit 1
fi

RUNNER_USER="${RUNNER_USER:-github-runner}"
RUNNER_GROUP="${RUNNER_GROUP:-$RUNNER_USER}"
RUNNER_ROOT="${RUNNER_ROOT:-/opt/actions-runner}"
CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"
RUNNER_URL="${RUNNER_URL:-}"
RUNNER_TOKEN="${RUNNER_TOKEN:-}"
RUNNER_GROUP_NAME="${RUNNER_GROUP_NAME:-Default}"
RUNNER_NAME_PREFIX="${RUNNER_NAME_PREFIX:-$(hostname)-verity}"
RUNNER_VERSION="${RUNNER_VERSION:-}"
RUNNER_COUNT="${RUNNER_COUNT:-2}"

runner_labels_for_index() {
  case "$1" in
    1)
      printf '%s' "${RUNNER_LABELS_1:-verity,build,cpu-8,mem-64g}"
      ;;
    2)
      printf '%s' "${RUNNER_LABELS_2:-verity,build,build-heavy,cpu-8,mem-64g}"
      ;;
    *)
      printf '%s' "${RUNNER_LABELS_EXTRA:-verity,build,cpu-8,mem-64g}"
      ;;
  esac
}

install_packages() {
  apt-get update
  apt-get install -y \
    build-essential \
    ccache \
    clang \
    curl \
    git \
    jq \
    libc++-dev \
    libc++abi-dev \
    libicu-dev \
    libssl-dev \
    libuv1-dev \
    lld \
    make \
    python3 \
    python3-venv \
    tar \
    unzip \
    zstd
}

ensure_runner_user() {
  if ! id "$RUNNER_USER" >/dev/null 2>&1; then
    useradd --create-home --shell /bin/bash "$RUNNER_USER"
  fi
  mkdir -p "$RUNNER_ROOT" "$CACHE_ROOT"
  chown -R "$RUNNER_USER:$RUNNER_GROUP" "$RUNNER_ROOT" "$CACHE_ROOT"
}

resolve_runner_version() {
  if [ -n "$RUNNER_VERSION" ]; then
    return
  fi
  RUNNER_VERSION="$(
    curl -fsSL https://api.github.com/repos/actions/runner/releases/latest |
      jq -r '.tag_name' |
      sed 's/^v//'
  )"
  if [ -z "$RUNNER_VERSION" ] || [ "$RUNNER_VERSION" = "null" ]; then
    echo "Unable to resolve the latest actions runner version." >&2
    exit 1
  fi
}

install_runner_files() {
  local runner_dir="$1"
  local archive="actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz"
  local url="https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/${archive}"

  mkdir -p "$runner_dir"
  if [ -x "$runner_dir/bin/Runner.Listener" ]; then
    return
  fi

  sudo -u "$RUNNER_USER" bash -lc "
    set -euo pipefail
    cd '$runner_dir'
    curl -fsSL '$url' -o '$archive'
    tar -xzf '$archive'
    rm -f '$archive'
  "
}

configure_runner() {
  local index="$1"
  local runner_dir="$RUNNER_ROOT/$index"
  local runner_name="${RUNNER_NAME_PREFIX}-${index}"
  local labels
  labels="$(runner_labels_for_index "$index")"

  install_runner_files "$runner_dir"

  if [ -z "$RUNNER_URL" ] || [ -z "$RUNNER_TOKEN" ]; then
    echo "Prepared $runner_dir with labels: $labels"
    echo "Set RUNNER_URL and RUNNER_TOKEN to finish registration."
    return
  fi

  sudo -u "$RUNNER_USER" bash -lc "
    set -euo pipefail
    cd '$runner_dir'
    if [ -f .runner ]; then
      exit 0
    fi
    ./config.sh \
      --unattended \
      --replace \
      --url '$RUNNER_URL' \
      --token '$RUNNER_TOKEN' \
      --name '$runner_name' \
      --runnergroup '$RUNNER_GROUP_NAME' \
      --labels '$labels' \
      --work '_work'
  "

  "$runner_dir/svc.sh" install "$RUNNER_USER"
  "$runner_dir/svc.sh" start
}

install_packages
ensure_runner_user
resolve_runner_version

for index in $(seq 1 "$RUNNER_COUNT"); do
  configure_runner "$index"
done

cat <<EOF
Host preparation is complete.
Runner root: $RUNNER_ROOT
Shared cache root: $CACHE_ROOT
Runner version: $RUNNER_VERSION

If RUNNER_URL and RUNNER_TOKEN were set, the runner services are now installed.
Otherwise, rerun with:
  RUNNER_URL=https://github.com/<owner>/<repo> \\
  RUNNER_TOKEN=<registration-token> \\
  $0
EOF
