#!/bin/bash
# Kernel-check base/ once: each tier with `--lib`, against the libraries of the tiers it builds on, its own library
# written to LIBDIR (default .build/base-libs). Exits 1 if any tier is not valid.
# Sourced (check-unit.sh), it only defines TIERS, base_libraries and checked.
set -u
R=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
CK=${PROOF_CHECKER:-$HOME/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker}

# Each tier, then the tiers whose libraries it loads, in loading order.
TIERS=(
  "axioms"
  "pairs axioms"
  "witness axioms pairs"
  "logic axioms"
  "cong axioms"
  "s2s3 axioms pairs witness"
  "primitives axioms"
  "regroup"
  "tuples axioms pairs witness"
  "classes axioms pairs witness logic cong s2s3 primitives tuples"
  "metafun axioms pairs witness logic cong s2s3 primitives tuples classes"
  "inf axioms pairs witness logic cong s2s3 primitives tuples classes"
  "zf axioms pairs witness logic cong s2s3 primitives tuples classes metafun inf"
)

# base_libraries LIBDIR: every tier's library, in an order that loads each after the tiers it builds on.
base_libraries() {
  local entry
  for entry in "${TIERS[@]}"; do printf '%s\n' "$1/${entry%% *}.fol.lib"; done
}

# checked NAME DEF PROOF LIB [LIBRARY...]: valid only when the checker exits 0, stderr is empty, and Proved and Schemas
# proved list every claim and schema DEF declares. Prints one line; on failure, the start of stderr, and LIB removed so
# that nothing loads it.
checked() {
  local name=$1 def=$2 proof=$3 lib=$4
  shift 4
  local out err rc claims schemas proved sproved size
  out=$(mktemp) err=$(mktemp)
  PROOF_CHECKER_MAX_WARNINGS=100000 "$CK" --lib "$lib" "$def" "$proof" "$@" > "$out" 2> "$err"
  rc=$?
  claims=$(grep -c '^claim ' "$def")
  schemas=$(grep -c '^schema ' "$def")
  proved=$(sed -n 's/^Proved (\([0-9]*\)):$/\1/p' "$out")
  sproved=$(sed -n 's/^Schemas proved (\([0-9]*\)):$/\1/p' "$out")
  size=$(wc -c < "$err")
  printf '%-24s exit %s  stderr %s  Proved (%s of %s)  Schemas proved (%s of %s)\n' \
    "$name" "$rc" "$size" "${proved:-0}" "$claims" "${sproved:-0}" "$schemas"
  if [ "$rc" -eq 0 ] && [ "$size" -eq 0 ] && [ "${proved:-0}" -eq "$claims" ] && [ "${sproved:-0}" -eq "$schemas" ]; then
    rm -f -- "$out" "$err"
    return 0
  fi
  grep -E '^(Conditional|Unproved|Schemas conditional|Schemas unproved)' "$out"
  head -c 2000 "$err"
  rm -f -- "$out" "$err" "$lib"
  return 1
}

[ "${BASH_SOURCE[0]}" = "$0" ] || return 0

[ -x "$CK" ] || { echo "no proof_checker at $CK; set PROOF_CHECKER" >&2; exit 2; }
LIBDIR=${1:-$R/.build/base-libs}
mkdir -p "$LIBDIR"
bad=0
for entry in "${TIERS[@]}"; do
  read -r -a words <<< "$entry"
  tier=${words[0]}
  file=$R/base/tiers/$tier
  [ "$tier" = axioms ] && file=$R/base/axioms
  libs=()
  for d in "${words[@]:1}"; do libs+=("$LIBDIR/$d.fol.lib"); done
  checked "$tier" "$file.fol.def" "$file.fol.proof" "$LIBDIR/$tier.fol.lib" "${libs[@]}" || bad=1
done
exit $bad
