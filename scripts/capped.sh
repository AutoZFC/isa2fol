#!/usr/bin/env bash
# Run a command inside a memory-capped systemd user scope.
#
# The cap is the point: when it is hit the OOM killer acts INSIDE the cgroup, so
# the build dies instead of tmux or the editing session.
#
#   scripts/capped.sh cargo test --release
#   MEM=4G JOBS=2 scripts/capped.sh cargo build --release
#
# JOBS caps BOTH rustc codegen units and test threads. Test threads matter more
# than they look: `unit::check` shells out to the fol-zfc proof_checker, so a
# parallel test run holds one checker process per thread, each carrying a whole
# proof in memory.
set -euo pipefail

MEM=${MEM:-8G}
JOBS=${JOBS:-4}

if ! command -v systemd-run >/dev/null 2>&1; then
    echo "capped.sh: systemd-run not found; refusing to run uncapped" >&2
    exit 127
fi
# `is-system-running` exits NON-ZERO for `degraded`, which is a running instance
# with some unrelated unit failed. Test the state, not the exit code.
state=$(systemctl --user is-system-running 2>/dev/null || true)
case "$state" in
    running | degraded | starting | maintenance | stopping) ;;
    *)
        echo "capped.sh: systemd --user is '${state:-absent}'; refusing to run uncapped" >&2
        exit 127
        ;;
esac

export RUST_TEST_THREADS="$JOBS"
export CARGO_BUILD_JOBS="$JOBS"

exec systemd-run --user --scope --quiet \
    -p MemoryMax="$MEM" \
    -p MemorySwapMax=0 \
    -- "$@"
