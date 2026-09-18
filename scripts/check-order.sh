#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
REG="$ROOT/registry"
fail() { echo "check-order: $*" >&2; exit 1; }

LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if (FNR > 1) track[$1]=$2+0; next }
  FILENAME == ARGV[2] { if (FNR > 1) { source[$1]=1; sourceTrack[$1]=$2; sourcePosition[$1]=$3+0 } next }
  FNR == 1 { next }
  {
    expected="PG-" $2 "-"
    suffix=substr($1, length(expected)+1)
    if (index($1, expected)!=1 || suffix !~ /^[0-9]+$/ || length(suffix)<4) bad("page ID/source mismatch " $1)
    if (!($2 in source)) bad("unknown page source " $2)
    if ($3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]$/) bad("bad page order key " $3)
    if (($2 in lastLocal) && $3 <= lastLocal[$2]) bad("page order is not strictly increasing in " $2)
    tuple=sprintf("%09d.%09d.%s", track[sourceTrack[$2]], sourcePosition[$2], $3)
    if (rows && tuple <= previous) bad("page rows are not in global source order")
    lastLocal[$2]=$3; previous=tuple; rows++
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/tracks.tsv" "$REG/sources.tsv" "$REG/pages.tsv" || fail "page identity or order invalid"

LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if (FNR > 1) track[$1]=$2+0; next }
  FILENAME == ARGV[2] { if (FNR > 1) { source[$1]=1; sourceTrack[$1]=$2; sourcePosition[$1]=$3+0 } next }
  FILENAME == ARGV[3] { if (FNR > 1) { page[$1]=1; pageSource[$1]=$2; pageOrder[$1]=$3 } next }
  FNR == 1 { next }
  {
    expected="CL-" $2 "-"
    suffix=substr($1, length(expected)+1)
    if (index($1, expected)!=1 || suffix !~ /^[0-9]+$/ || length(suffix)<4) bad("claim ID/source mismatch " $1)
    if (!($2 in source) || !($4 in page) || pageSource[$4]!=$2) bad("claim source/page mismatch " $1)
    if ($3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]\.[0-9][0-9][0-9][0-9]$/) bad("bad claim order key " $3)
    if (substr($3,1,6) != pageOrder[$4] && ($4 in pageOrder)) bad("claim/page order mismatch " $1)
    if (($2 in lastLocal) && $3 <= lastLocal[$2]) bad("claim order is not strictly increasing in " $2)
    tuple=sprintf("%09d.%09d.%s", track[sourceTrack[$2]], sourcePosition[$2], $3)
    if (rows && tuple <= previous) bad("claim rows are not in global source order")
    lastLocal[$2]=$3; previous=tuple; rows++
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/tracks.tsv" "$REG/sources.tsv" "$REG/pages.tsv" "$REG/claims.tsv" || fail "claim identity or order invalid"

LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  FILENAME == ARGV[1] { if (FNR > 1) track[$1]=$2+0; next }
  FILENAME == ARGV[2] { if (FNR > 1) { sourceTrack[$1]=$2; sourcePosition[$1]=$3+0 } next }
  FILENAME == ARGV[3] {
    if (FNR > 1) {
      claim[$1]=1; claimSource[$1]=$2
      claimTuple[$1]=sprintf("%09d.%09d.%s", track[sourceTrack[$2]], sourcePosition[$2], $3)
    }
    next
  }
  FNR == 1 { next }
  !($1 in claim) || !($3 in claim) { bad("unknown dependency claim") }
  $2 !~ /^(requires|required_by|consequence_of)$/ { bad("bad dependency role " $2) }
  $1 == $3 { bad("self dependency") }
  seen[$1 SUBSEP $3]++ { bad("duplicate dependency edge") }
  claimTuple[$3] >= claimTuple[$1] { bad("dependency target is not earlier in global source order") }
  $2 == "required_by" && ($4 == "" || $4 == "NONE") { bad("required_by needs review rationale") }
  sourceTrack[claimSource[$1]] != sourceTrack[claimSource[$3]] && ($4 == "" || $4 == "NONE") { bad("cross-track dependency needs review rationale") }
  $4 != "NONE" && !token($4) { bad("bad dependency rationale token") }
  { if ($2 == "required_by") edge[$3 SUBSEP $1]=1; else edge[$1 SUBSEP $3]=1; node[$1]=node[$3]=1 }
  function visit(n, k, part, to) {
    if (mark[n] == 1) { bad("dependency cycle"); return }
    if (mark[n] == 2) return
    mark[n]=1
    for (k in edge) { split(k,part,SUBSEP); if (part[1] == n) { to=part[2]; visit(to) } }
    mark[n]=2
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { for (n in node) visit(n); exit failed }
' "$REG/tracks.tsv" "$REG/sources.tsv" "$REG/claims.tsv" "$REG/dependencies.tsv" || fail "dependency order invalid"

echo "check-order: ok"
