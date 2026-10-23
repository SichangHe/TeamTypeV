#!/usr/bin/env bash
# Run the required catch-up acceptance checks sequentially; print only failures.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
logs=${CATCHUP_CHECK_LOG_DIR:-$(mktemp -d /tmp/teamtype-catchup-checks.XXXXXX)}
mkdir -p "$logs"
export TEAMTYPE_BINARY=${TEAMTYPE_BINARY:-$root/target/debug/teamtype}
check() {
    local name=$1
    shift
    if "$@" >"$logs/$name.log" 2>&1; then
        return 0
    else
        echo "FAIL: $name; full log: $logs/$name.log" >&2
        tail -80 "$logs/$name.log" >&2
        return 1
    fi
}
check fmt timeout 60s cargo fmt --all --check
check build timeout 1200s cargo build --profile test -p teamtype --jobs 2
check test timeout 1200s cargo test --workspace --jobs 2
check clippy timeout 1200s cargo clippy --all-targets --jobs 2 -- -D warnings
check people timeout 600s bash verification/live/people.sh
check history timeout 600s bash verification/live/history.sh
