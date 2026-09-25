#!/usr/bin/env bash
#
# Regenerate data/zf_export -- the theory and proof export of the Isabelle/ZF sessions
# -- from ONE Isabelle run. It is a local cache and is never committed:
# ZF.List's proof of nth_upt alone exports as a 3.1 GB file.
#
# Run with:  bash scripts/03-export-zf.sh        (up to MEM of RAM)
#
# ⚠ ONE RUN, NEVER A MERGE. A proof serial is a per-process counter, so files from
#   two runs disagree about what a serial names. data/zf_export was once assembled
#   from two runs: a named statement pointed at another theorem's proof and 402
#   citations dangled. The export is written to a fresh directory and swapped in
#   whole, so a partial export never sits at data/zf_export.
# ⚠ ML_system_64. The default 32-bit Poly/ML runs out of store exporting ZF.List.

set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
ISABELLE="${ISABELLE:-isabelle}"
VERSION=Isabelle2025-2                 # pinned: the reader is written against its encoders
OUT="$ROOT/data/zf_export"
STATE="$ROOT/data/.isabelle"           # the build's $HOME: its heaps and databases, never yours
OPTIONS=(-o ML_system_64=true -o export_theory -o export_proofs -o record_proofs=2)
# src/ZF/ROOT has nine sessions. ⚠ ZF-UNITY is NOT exported: Isabelle's exporter rewrites one box
# (Comp.Increasing_preserves_Stable) past 64 GB, walking the proof as a tree. It builds in 17 s
# with export off. Add it back only with an exporter that keeps proofs shared.
SESSIONS=(ZF ZF-AC ZF-Coind ZF-Constructible ZF-IMP ZF-Induct ZF-Resid ZF-ex)
export MEM="${MEM:-64G}"

step() { printf '\n\033[1;34m==> %s\033[0m\n' "$*"; }
die()  { printf '\n\033[1;31mERROR: %s\033[0m\n' "$*" >&2; exit 1; }

step "Preconditions"
command -v "$ISABELLE" >/dev/null || die "no '$ISABELLE' on PATH; set ISABELLE=/path/to/$VERSION/bin/isabelle"
found=$("$ISABELLE" version)
[ "$found" = "$VERSION" ] || die "need $VERSION, '$ISABELLE' is $found"

tmp=$(mktemp -d "$ROOT/data/.zf_export.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$STATE"

step "Build ${SESSIONS[*]} with export enabled"
"$ROOT/scripts/capped.sh" env HOME="$STATE" "$ISABELLE" build "${OPTIONS[@]}" "${SESSIONS[@]}"

step "Export theory/ and proofs/ of Pure and every session"
for session in Pure "${SESSIONS[@]}"; do
    "$ROOT/scripts/capped.sh" env HOME="$STATE" "$ISABELLE" export -n -o ML_system_64=true \
        -O "$tmp" -x '*:theory/**' -x '*:proofs/**' "$session" >/dev/null
done

step "Swap in"
rm -rf "$OUT.old"
if [ -e "$OUT" ]; then mv "$OUT" "$OUT.old"; fi
mv "$tmp" "$OUT"
rm -rf "$OUT.old"
printf '    %s proof files, %s\n' "$(find "$OUT" -path '*/proofs/*' -type f | wc -l)" "$(du -sh "$OUT" | cut -f1)"
