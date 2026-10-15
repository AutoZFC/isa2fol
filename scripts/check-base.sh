#!/bin/bash
# Kernel-check every base/ tier as a CHAINED unit: its dependencies' headers, then `--`, then their
# proofs. Run bare, a tier reports `Failed`, which reads as staleness and is not.
# A tier passes only when the checker exits 0 AND stderr is empty. Exits 1 if any tier does not.
set -u
R=$(cd "$(dirname "$0")/.." && pwd)
CK=${PROOF_CHECKER:-$HOME/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker}
[ -x "$CK" ] || { echo "no proof_checker at $CK; set PROOF_CHECKER" >&2; exit 2; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
bad=0

check() {
  local name=$1 unit=$2; shift 2
  local defs=() proofs=()
  for d in "$@"; do defs+=("$R/$d.fol.def"); proofs+=("$R/$d.fol.proof"); done
  local args=("$R/$unit.fol.def" "$R/$unit.fol.proof")
  [ $# -gt 0 ] && args+=("${defs[@]}" -- "${proofs[@]}")
  PROOF_CHECKER_MAX_WARNINGS=100000 "$CK" "${args[@]}" > "$OUT/$name.out" 2> "$OUT/$name.err"
  local rc=$? err
  err=$(wc -c < "$OUT/$name.err")
  printf '%-11s exit %s  stderr %s  %s\n' "$name" "$rc" "$err" "$(grep -m1 -E '^Proved' "$OUT/$name.out")"
  if [ "$rc" -ne 0 ] || [ "$err" -ne 0 ]; then bad=1; head -c 2000 "$OUT/$name.err"; fi
}

A=base/axioms; T=base/tiers
check axioms     $A
check pairs      $T/pairs      $A
check witness    $T/witness    $A $T/pairs
check logic      $T/logic      $A
check cong       $T/cong       $A
check s2s3       $T/s2s3       $A $T/pairs $T/witness
check primitives $T/primitives $A
check regroup    $T/regroup
check tuples     $T/tuples     $A $T/pairs $T/witness
check classes    $T/classes    $A $T/pairs $T/witness $T/logic $T/cong $T/s2s3 $T/tuples
check metafun    $T/metafun    $A $T/pairs $T/witness $T/logic $T/cong $T/s2s3 $T/primitives $T/tuples $T/classes
check inf        $T/inf        $A $T/pairs $T/witness $T/logic $T/cong $T/s2s3 $T/primitives $T/tuples $T/classes
check zf         $T/zf         $A $T/pairs $T/witness $T/logic $T/cong $T/s2s3 $T/primitives $T/tuples $T/classes $T/inf
exit $bad
