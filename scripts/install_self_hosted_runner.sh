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
RUNNER_PROFILE_INPUT="${RUNNER_PROFILE:-}"
RUNNER_NAME_PREFIX_INPUT="${RUNNER_NAME_PREFIX:-}"
RUNNER_ARCH_INPUT="${RUNNER_ARCH:-}"
RUNNER_PROFILE="${RUNNER_PROFILE:-build}"
RUNNER_ARCH="${RUNNER_ARCH:-x64}"
HOST_IP="${HOST_IP:-}"
if [ -z "$HOST_IP" ]; then
  HOST_IP="$(hostname -I 2>/dev/null | awk '{print $1}')"
fi
HOST_NAME="$(hostname)"
RUNNER_DETECTED_PROFILE="${RUNNER_HOST_PROFILE:-$HOST_IP}"
if [ -z "${RUNNER_HOST_PROFILE:-}" ] && [ "$HOST_NAME" = "spark-de79" ]; then
  RUNNER_DETECTED_PROFILE="spark-de79"
fi

case "$RUNNER_DETECTED_PROFILE" in
  88.99.4.254|healthy-build)
    RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-build}"
    RUNNER_COUNT="${RUNNER_COUNT:-1}"
    RUNNER_LABELS_1="${RUNNER_LABELS_1:-verity,build,build-heavy,hetzner,hz2,cpu-8,mem-64g,ci-host-88-99-4-254}"
    ;;
  95.216.244.60|mixed-8core)
    RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-fastlane}"
    RUNNER_COUNT="${RUNNER_COUNT:-1}"
    RUNNER_LABELS_1="${RUNNER_LABELS_1:-verity,fastlane,hetzner,hz1,cpu-8,ci-host-95-216-244-60}"
    ;;
  spark-de79|dgx-spark)
    RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-dgx-gpu}"
    RUNNER_ARCH="${RUNNER_ARCH_INPUT:-arm64}"
    RUNNER_COUNT="${RUNNER_COUNT:-1}"
    RUNNER_LABELS_1="${RUNNER_LABELS_1:-dgx,dgx-spark,gpu,nvidia,home,arm64-gb10}"
    ;;
esac
RUNNER_NAME_PREFIX="${RUNNER_NAME_PREFIX_INPUT:-$(hostname)-verity-${RUNNER_PROFILE}}"
RUNNER_VERSION="${RUNNER_VERSION:-}"
case "$RUNNER_ARCH" in
  x64|arm64|arm) ;;
  *)
    echo "Unsupported RUNNER_ARCH: $RUNNER_ARCH" >&2
    echo "Use one of: x64, arm64, arm." >&2
    exit 1
    ;;
esac
case "$RUNNER_PROFILE" in
  fastlane|build|dgx-gpu) ;;
  *)
    echo "Unsupported RUNNER_PROFILE: $RUNNER_PROFILE" >&2
    echo "Use one of: fastlane, build, dgx-gpu." >&2
    exit 1
    ;;
esac
if [ -z "${RUNNER_COUNT:-}" ]; then
  case "$RUNNER_PROFILE" in
    fastlane|build|dgx-gpu)
      RUNNER_COUNT=1
      ;;
    *)
      RUNNER_COUNT=1
      ;;
  esac
fi

runner_labels_for_index() {
  case "$RUNNER_PROFILE" in
    fastlane)
      case "$1" in
        1)
          printf '%s' "${RUNNER_LABELS_1:-verity,fastlane,hetzner}"
          ;;
        *)
          printf '%s' "${RUNNER_LABELS_EXTRA:-verity,fastlane,hetzner}"
          ;;
      esac
      ;;
    dgx-gpu)
      case "$1" in
        1)
          printf '%s' "${RUNNER_LABELS_1:-dgx,dgx-spark,gpu,nvidia}"
          ;;
        *)
          printf '%s' "${RUNNER_LABELS_EXTRA:-dgx,dgx-spark,gpu,nvidia}"
          ;;
      esac
      ;;
    *)
      case "$1" in
        1)
          printf '%s' "${RUNNER_LABELS_1:-verity,build,hetzner,cpu-8,mem-64g}"
          ;;
        2)
          printf '%s' "${RUNNER_LABELS_2:-verity,build,build-heavy,hetzner,cpu-8,mem-64g}"
          ;;
        *)
          printf '%s' "${RUNNER_LABELS_EXTRA:-verity,build,build-heavy,hetzner,cpu-8,mem-64g}"
          ;;
      esac
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
    libgmp-dev \
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
  local archive="actions-runner-linux-${RUNNER_ARCH}-${RUNNER_VERSION}.tar.gz"
  local url="https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/${archive}"

  mkdir -p "$runner_dir"
  chown -R "$RUNNER_USER:$RUNNER_GROUP" "$runner_dir"
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

installed_service_name() {
  local runner_dir="$1"
  if [ -f "$runner_dir/.service" ]; then
    tr -d '\r\n' < "$runner_dir/.service"
  fi
}

service_known_to_systemd() {
  local service_name="$1"
  [ -n "$service_name" ] || return 1
  systemctl list-unit-files "$service_name" >/dev/null 2>&1 || systemctl status "$service_name" >/dev/null 2>&1
}

harden_runner_service() {
  local service_name="$1"
  local dropin_dir="/etc/systemd/system/${service_name}.d"
  local dropin_file="${dropin_dir}/10-verity-runner-stop.conf"

  mkdir -p "$dropin_dir"
  cat > "$dropin_file" <<'EOF'
[Service]
# GitHub's generated service defaults to KillMode=process, which can leave
# cancelled job child processes running and keep a runner effectively busy.
KillMode=control-group
SendSIGKILL=yes
TimeoutStopSec=90s
EOF
  systemctl daemon-reload
}

stop_runner_service_if_present() {
  local runner_dir="$1"
  local service_name="$2"
  if service_known_to_systemd "$service_name"; then
    (
      cd "$runner_dir"
      ./svc.sh stop || systemctl stop "$service_name" || true
    )
  fi
}

ensure_runner_service() {
  local runner_dir="$1"
  local service_name="$2"
  if ! service_known_to_systemd "$service_name"; then
    (
      cd "$runner_dir"
      ./svc.sh install "$RUNNER_USER"
    )
  fi
  harden_runner_service "$service_name"
  (
    cd "$runner_dir"
    ./svc.sh start
  )
}

configure_runner() {
  local index="$1"
  local runner_dir="$RUNNER_ROOT/$index"
  local runner_name="${RUNNER_NAME_PREFIX}-${index}"
  local service_name="actions.runner.$(printf '%s' "${RUNNER_URL#https://github.com/}" | tr '/' '-').${runner_name}.service"
  local installed_service_unit
  local labels_file="$runner_dir/.configured-labels"
  local labels
  labels="$(runner_labels_for_index "$index")"
  installed_service_unit="$(installed_service_name "$runner_dir")"

  install_runner_files "$runner_dir"

  if [ -z "$RUNNER_URL" ] || [ -z "$RUNNER_TOKEN" ]; then
    echo "Prepared $runner_dir with labels: $labels"
    echo "Set RUNNER_URL and RUNNER_TOKEN to finish registration."
    return
  fi

  if [ -f "$runner_dir/.runner" ]; then
    if [ ! -f "$labels_file" ] || [ "$(cat "$labels_file")" != "$labels" ]; then
      if [ -n "$installed_service_unit" ]; then
        stop_runner_service_if_present "$runner_dir" "$installed_service_unit"
      fi
      if [ -n "$service_name" ] && [ "$service_name" != "$installed_service_unit" ]; then
        stop_runner_service_if_present "$runner_dir" "$service_name"
      fi
      if [ -n "$installed_service_unit" ] && service_known_to_systemd "$installed_service_unit"; then
        (
          cd "$runner_dir"
          ./svc.sh uninstall || true
        )
      elif [ -n "$service_name" ] && service_known_to_systemd "$service_name"; then
        systemctl disable --now "$service_name" || true
      fi
      sudo -u "$RUNNER_USER" bash -lc "
        set -euo pipefail
        cd '$runner_dir'
        ./config.sh remove --local
      "
    else
      if [ -n "$installed_service_unit" ] && service_known_to_systemd "$installed_service_unit"; then
        ensure_runner_service "$runner_dir" "$installed_service_unit"
        return
      fi
      if [ -n "$service_name" ] && service_known_to_systemd "$service_name"; then
        ensure_runner_service "$runner_dir" "$service_name"
        return
      fi
      ensure_runner_service "$runner_dir" "$service_name"
      return
    fi
  fi

  sudo -u "$RUNNER_USER" bash -lc "
    set -euo pipefail
    cd '$runner_dir'
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
  printf '%s\n' "$labels" > "$labels_file"
  chown "$RUNNER_USER:$RUNNER_GROUP" "$labels_file"

  ensure_runner_service "$runner_dir" "$service_name"
}

decommission_runner() {
  local runner_dir="$1"
  local installed_service_unit

  if [ ! -d "$runner_dir" ]; then
    return
  fi

  installed_service_unit="$(installed_service_name "$runner_dir")"
  if [ -n "$installed_service_unit" ]; then
    stop_runner_service_if_present "$runner_dir" "$installed_service_unit"
    if service_known_to_systemd "$installed_service_unit"; then
      (
        cd "$runner_dir"
        ./svc.sh uninstall || systemctl disable --now "$installed_service_unit" || true
      )
    fi
  fi

  if [ -f "$runner_dir/.runner" ]; then
    sudo -u "$RUNNER_USER" bash -lc "
      set -euo pipefail
      cd '$runner_dir'
      ./config.sh remove --local
    " || true
  fi

  rm -rf "$runner_dir"
  echo "Decommissioned surplus runner directory: $runner_dir"
}

decommission_surplus_runners() {
  local runner_dir index

  if [ ! -d "$RUNNER_ROOT" ]; then
    return
  fi

  for runner_dir in "$RUNNER_ROOT"/*; do
    [ -d "$runner_dir" ] || continue
    index="$(basename "$runner_dir")"
    case "$index" in
      ''|*[!0-9]*)
        continue
        ;;
    esac
    if [ "$index" -gt "$RUNNER_COUNT" ]; then
      decommission_runner "$runner_dir"
    fi
  done
}

install_packages
ensure_runner_user
resolve_runner_version

for index in $(seq 1 "$RUNNER_COUNT"); do
  configure_runner "$index"
done
decommission_surplus_runners

cat <<EOF
Host preparation is complete.
Runner root: $RUNNER_ROOT
Shared cache root: $CACHE_ROOT
Runner profile: $RUNNER_PROFILE
Runner architecture: $RUNNER_ARCH
Runner version: $RUNNER_VERSION

If RUNNER_URL and RUNNER_TOKEN were set, the runner services are now installed.
Otherwise, rerun with:
  RUNNER_URL=https://github.com/<owner>/<repo> \\
  RUNNER_TOKEN=<registration-token> \\
  RUNNER_PROFILE=fastlane|build|dgx-gpu \\
  RUNNER_ARCH=x64|arm64 \\
  $0
EOF
