#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
REG="$ROOT/registry"
fail() { echo "check-source-items: $*" >&2; exit 1; }

LC_ALL=C awk -F '\t' '
  function slug(s) { s=tolower(s); gsub(/[^a-z0-9]+/, "-", s); gsub(/^-|-$/, "", s); return s }
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  FILENAME == ARGV[1] { if (FNR>1) { track[$1]=$2+0 } next }
  FILENAME == ARGV[2] { if (FNR>1) { source[$1]=1; sourceTrack[$1]=$2; sourcePosition[$1]=$3+0 } next }
  FILENAME == ARGV[3] { if (FNR>1) { page[$1]=1; pageSource[$1]=$2; pageOrder[$1]=$3 } next }
  FNR == 1 { next }
  {
    expected="IT-" $2 "-"; suffix=substr($1,length(expected)+1)
    if (index($1,expected)!=1 || suffix !~ /^[0-9]+$/ || length(suffix)<4) bad("item ID/source mismatch " $1)
    if (!($2 in source)) bad("unknown item source " $2)
    if (!($4 in page) || pageSource[$4]!=$2) bad("item source/page mismatch " $1)
    if ($3 !~ /^[0-9]{6}\.[0-9]{4}$/ && $3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]\.[0-9][0-9][0-9][0-9]$/) bad("bad item order key " $1)
    if (substr($3,1,6)!=pageOrder[$4]) bad("item/page order mismatch " $1)
    if ($5 !~ /^(theorem|lemma|corollary|proposition|definition|problem|conjecture|example|exercise|remark|note|equation|figure|footnote|table|unlabeled)$/) bad("bad item kind " $1)
    if (($5=="unlabeled") != ($6=="NONE")) bad("item label/kind mismatch " $1)
    if ($6!="NONE" && index($8,$6)==0) bad("item locator does not contain exact label " $1)
    if ($7=="") bad("empty item title " $1)
    if ($8=="") bad("empty item locator " $1)
    if ($9 ~ /^Chapter [0-9]+$/) {
      chapter=substr($9,9)+0
      canonical=sprintf("Chapter %02d",chapter)
      if ($9!=canonical) bad("numeric chapter group is not zero-padded " $1)
    }
    if ($9=="" || $10!=slug($9)) bad("item public group/slug mismatch " $1)
    if (!token($11)) bad("bad item review token " $1)
    if (seenId[$1]++) bad("duplicate item ID " $1)
    tuple=sprintf("%09d.%09d.%s",track[sourceTrack[$2]],sourcePosition[$2],$3)
    if (rows && tuple<=previous) bad("items are not in global source order")
    previous=tuple; rows++
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/tracks.tsv" "$REG/sources.tsv" "$REG/pages.tsv" "$REG/source-items.tsv" || fail "source item registry invalid"

LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if (FNR>1) { item[$1]=1; itemSource[$1]=$2; itemOrder[$1]=$3; itemPage[$1]=$4 } next }
  FILENAME == ARGV[2] { if (FNR>1) { claim[$1]=1; claimSource[$1]=$2; claimOrder[$1]=$3; claimPage[$1]=$4; active[$1]=($12=="false") } next }
  FNR == 1 { next }
  {
    if (!($1 in item)) bad("unknown item relation " $1)
    if (!($3 in claim)) bad("unknown item claim " $3)
    if ($2 !~ /^[1-9][0-9]*$/ || $2+0 != ++position[$1]) bad("item relation positions are not contiguous " $1)
    if (seenPair[$1 SUBSEP $3]++) bad("duplicate item/claim relation")
    if (claimUse[$3]++) bad("claim occurs in more than one item " $3)
    if (itemSource[$1]!=claimSource[$3] || itemPage[$1]!=claimPage[$3]) bad("item/claim source or page mismatch " $3)
    if ($2==1 && itemOrder[$1]!=claimOrder[$3]) bad("item order does not match first claim " $1)
    itemUse[$1]++
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END {
    for (id in item) if (!itemUse[id]) bad("item has no claims " id)
    for (id in active) if (claimUse[id]!=1) bad("claim lacks exactly one source item " id)
    exit failed
  }
' "$REG/source-items.tsv" "$REG/claims.tsv" "$REG/item-claims.tsv" || fail "source item coverage invalid"

echo "check-source-items: ok"
