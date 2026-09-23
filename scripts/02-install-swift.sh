#!/usr/bin/env bash
#
# Swift toolchain for isa2fol. No sudo: everything lands in $HOME, matching
# 01-install-toolchain.sh. Idempotent -- re-running skips what is present.
#
# Run with:  bash scripts/02-install-swift.sh
#
# Ubuntu 22.04's stock dev packages already satisfy Swift's runtime deps
# (libcurl4 libxml2 libedit2 libsqlite3-0 libncurses6 libpython3.10 zlib1g
# binutils), which is why this needs no package manager at all.

set -euo pipefail

VER="${SWIFT_VERSION:-6.4.0}"          # pinned, not "latest": a setup script
                                       # must build the same thing next month
LOG="${LOG:-/tmp/isa2fol-swift.log}"
BIN="$HOME/.local/bin"
ROOT="$HOME/.local/swift-$VER"
LINK="$HOME/.local/swift"
TARBALL="swift-$VER-RELEASE-ubuntu22.04.tar.gz"
URL="https://download.swift.org/swift-$VER-release/ubuntu2204/swift-$VER-RELEASE/$TARBALL"

exec > >(tee -a "$LOG") 2>&1
step() { printf '\n\033[1;34m==> %s\033[0m\n' "$*"; }
info() { printf '    %s\n' "$*"; }
die()  { printf '\n\033[1;31mERROR: %s\033[0m\n' "$*" >&2; exit 1; }

echo "=== $(date -Is) 02-install-swift.sh  (swift $VER) ==="

step "Preconditions"
[ "$(id -u)" -ne 0 ] || die "do not run as root; this installs into \$HOME"
[ "$(uname -m)" = x86_64 ] || die "this script builds for x86_64, got $(uname -m)"
for t in curl tar gpg; do command -v "$t" >/dev/null || die "$t missing"; done
. /etc/os-release
[ "${VERSION_ID:-}" = "22.04" ] || info "WARNING: built for Ubuntu 22.04, this is ${VERSION_ID:-?}"
for p in libcurl4 libxml2 libedit2 libsqlite3-0 libncurses6 zlib1g binutils; do
    dpkg -s "$p" >/dev/null 2>&1 || die "missing runtime dep: $p (needs: sudo apt-get install $p)"
done
avail=$(df -Pk "$HOME" | awk 'NR==2{print int($4/1024/1024)}')
[ "$avail" -ge 5 ] || die "need ~5G free in \$HOME, have ${avail}G"
info "ok: x86_64, ubuntu ${VERSION_ID:-?}, ${avail}G free"

step "Toolchain"
if [ -x "$ROOT/usr/bin/swift" ]; then
    info "skip: $ROOT present"
else
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    info "downloading $TARBALL (~1.1G)"
    curl -fSL --retry 3 -o "$tmp/$TARBALL" "$URL"
    curl -fSL --retry 3 -o "$tmp/$TARBALL.sig" "$URL.sig"

    info "verifying signature against swift.org keys"
    # --compressed is NOT optional: swift.org serves all-keys.asc with
    # Content-Encoding: gzip, and without it gpg sees a gzip blob and reports
    # "no valid OpenPGP data found". Import unconditionally -- a guard on
    # "key present" matches an EXPIRED 2015 key and skips the current one.
    curl -fsSL --compressed --retry 3 -o "$tmp/all-keys.asc" \
        https://www.swift.org/keys/all-keys.asc
    gpg --import "$tmp/all-keys.asc" 2>&1 | tail -2
    gpg --verify "$tmp/$TARBALL.sig" "$tmp/$TARBALL" \
        || die "signature verification FAILED -- do not install this tarball"

    info "extracting to $ROOT"
    mkdir -p "$ROOT"
    tar -xzf "$tmp/$TARBALL" -C "$ROOT" --strip-components=1
    [ -x "$ROOT/usr/bin/swift" ] || die "extracted tree has no usr/bin/swift"
fi

step "Links"
mkdir -p "$BIN"
ln -sfn "$ROOT" "$LINK"
for b in swift swiftc swift-format; do
    [ -e "$LINK/usr/bin/$b" ] && ln -sfn "$LINK/usr/bin/$b" "$BIN/$b"
done
info "$LINK -> $ROOT"
info "$BIN/swift -> $LINK/usr/bin/swift"

step "Verify"
export PATH="$BIN:$PATH"
swift --version || die "swift not runnable"

# A symlinked toolchain must still find its own stdlib and SwiftPM resources.
# Building a throwaway package is the only check that actually proves it.
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
( cd "$t" && swift package init --type library --name Probe >/dev/null \
  && swift build 2>&1 | tail -2 && swift test 2>&1 | tail -2 ) \
  || die "toolchain is installed but cannot build a package"

echo
echo "=== done ==="
echo "swift:   $(command -v swift)  ($(swift --version 2>/dev/null | head -1))"
echo "root:    $ROOT"
echo
echo "Add to your shell profile if it is not already there:"
echo "  export PATH=\"\$HOME/.local/bin:\$PATH\""
