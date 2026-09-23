#!/usr/bin/env bash
# Per-user toolchain for isa2fol: rustup/cargo, bazelisk, and the fol-zfc
# proof_checker that `unit::check` shells out to. No sudo: everything lands in
# $HOME. Idempotent -- re-running skips whatever is already present.
set -euo pipefail

LOG=${LOG:-/tmp/isa2fol-toolchain.log}
exec > >(tee -a "$LOG") 2>&1
echo "=== $(date -Is) 01-install-toolchain.sh ==="

FOLZFC=${FOLZFC:-$HOME/repos/fol-zfc-comb}
BIN="$HOME/.local/bin"
CARGO_HOME=${CARGO_HOME:-$HOME/.cargo}

for t in gcc g++ make curl git unzip zip python3 systemd-run; do
    command -v "$t" >/dev/null || { echo "FATAL: $t missing"; exit 1; }
done
[ -d "$FOLZFC" ] || { echo "FATAL: no fol-zfc at $FOLZFC"; exit 1; }
mkdir -p "$BIN"

echo "--- [1/3] rust"
if command -v cargo >/dev/null || [ -x "$CARGO_HOME/bin/cargo" ]; then
    echo "skip: cargo present"
else
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --profile minimal --default-toolchain stable
fi
export PATH="$CARGO_HOME/bin:$PATH"
cargo --version
rustc --version

echo "--- [2/3] bazelisk"
if [ -x "$BIN/bazel" ]; then
    echo "skip: $BIN/bazel present"
else
    ver=v1.25.0
    curl -fsSL -o "$BIN/bazel.tmp" \
        "https://github.com/bazelbuild/bazelisk/releases/download/$ver/bazelisk-linux-amd64"
    chmod +x "$BIN/bazel.tmp"
    mv "$BIN/bazel.tmp" "$BIN/bazel"
fi
export PATH="$BIN:$PATH"

echo "--- [3/3] proof_checker"
CK="$FOLZFC/bazel-bin/src/tools/proof_checker"
if [ -x "$CK" ]; then
    echo "skip: $CK present"
else
    # fol-zfc's .bazelrc sets -Werror. gcc 11 emits a FALSE stringop-overflow on
    # `buf.insert(buf.end(), kMagic, ...)` after a reserve (library.cpp:473).
    # Downgrade that ONE warning on the command line; do not edit the checkout.
    ( cd "$FOLZFC" && bazel build -c opt \
        --cxxopt=-Wno-error=stringop-overflow \
        //src/tools:proof_checker )
fi
[ -x "$CK" ] || { echo "FATAL: proof_checker not built"; exit 1; }
"$CK" --help 2>&1 | head -3 || true

echo
echo "=== done ==="
echo "cargo:         $(command -v cargo)"
echo "bazel:         $(command -v bazel)"
echo "proof_checker: $CK"
echo
echo "isa2fol resolves the checker relative to the repo, which does NOT match"
echo "this layout. Export it:"
echo "  export PROOF_CHECKER=$CK"
