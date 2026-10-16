#!/bin/bash
# Kernel-check an emitted unit (`isa2fol lower EXPORT --emit DIR`): each part of DIR/parts, in its order, with `--lib`,
# against base's libraries and those of the parts its line names. A part naming a part that is not valid is not checked.
# BASE_LIBS is a directory check-base.sh wrote; without it, base is checked into DIR/base first. Exits 0 only when every
# part is valid.
set -u
R=$(cd "$(dirname "$0")/.." && pwd)
. "$R/scripts/check-base.sh"
[ $# -ge 1 ] && [ $# -le 2 ] || { echo "usage: $0 DIR [BASE_LIBS]" >&2; exit 2; }
DIR=$1
[ -f "$DIR/parts" ] || { echo "no $DIR/parts" >&2; exit 2; }
[ -x "$CK" ] || { echo "no proof_checker at $CK; set PROOF_CHECKER" >&2; exit 2; }
BASE=${2:-$DIR/base}
if [ $# -lt 2 ]; then
  "$R/scripts/check-base.sh" "$BASE" > "$DIR/base.log" || { echo "base is not valid:"; cat "$DIR/base.log"; exit 1; }
fi
mapfile -t base_libs < <(base_libraries "$BASE")
declare -A valid
bad=0
while IFS= read -r line; do
  name=${line%%:*}
  waits=""
  libs=("${base_libs[@]}")
  for p in ${line#*:}; do
    if [ "${valid[$p]:-}" != 1 ]; then waits=$p; break; fi
    libs+=("$DIR/$p.fol.lib")
  done
  if [ -n "$waits" ]; then
    printf '%-24s not checked: waits on %s\n' "$name" "$waits"
    bad=1
    continue
  fi
  if checked "$name" "$DIR/$name.fol.def" "$DIR/$name.fol.proof" "$DIR/$name.fol.lib" "${libs[@]}"; then
    valid[$name]=1
  else
    bad=1
  fi
done < "$DIR/parts"
exit $bad
