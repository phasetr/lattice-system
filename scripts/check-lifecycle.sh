#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
REG="$ROOT/registry"
fail() { echo "check-lifecycle: $*" >&2; exit 1; }
{ IFS= read -r _; IFS= read -r phase; } < "$REG/phase.tsv"

LC_ALL=C awk -F '\t' -v phase="$phase" '
  function oid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  function lifecycleRank(s) { return s=="registered"?1:s=="source_frozen"?2:s=="census_pass1"?3:s=="census_pass2"?4:s=="census_reconciled"?5:s=="vocabulary_reviewed"?6:s=="skeleton_frozen"?7:s=="proof_active"?8:s=="complete"?9:0 }
  function phaseRank(s) { return s=="bootstrap"?2:s=="census"?5:s=="vocabulary"?6:s=="skeleton"?7:s=="proof"?9:0 }
  FILENAME == ARGV[1] { if (FNR > 1) { pdf[$1]=$15; text[$1]=$16; coverage[$1]=$17; source[$1]=1 } next }
  FILENAME == ARGV[2] { if (FNR > 1) invariant[$1]=1; next }
  FNR == 1 { next }
  {
    id=$1; life=$2; rank=lifecycleRank(life)
    if (!rank || rank > phaseRank(phase)) bad("source lifecycle exceeds checker capability " id)
    if (life=="registered" && (coverage[id]!="pending" || pdf[id]!="" || text[id]!="")) bad("registered source must be unfrozen and pending " id)
    if (life=="source_frozen" && (coverage[id]!="pending" || !oid(pdf[id]) || !oid(text[id]))) bad("source_frozen requires OIDs and pending coverage " id)
    if (life=="census_pass1" && coverage[id]!="pass1") bad("census_pass1 coverage mismatch " id)
    if (life=="census_pass2" && coverage[id]!="pass2") bad("census_pass2 coverage mismatch " id)
    if (life=="census_reconciled" && coverage[id]!="reconciled") bad("census_reconciled coverage mismatch " id)
    if (rank>=6 && coverage[id]!="frozen") bad("post-census lifecycle requires frozen coverage " id)
    if (rank>=3 && (!oid(pdf[id]) || !oid(text[id]) || length(pdf[id])!=length(text[id]))) bad("census lifecycle requires frozen source OIDs " id)
    if (rank>=5 && !(id in invariant)) bad("reconciled source lacks invariant row " id)
    if (rank<5 && (id in invariant)) bad("unreconciled source has invariant row " id)
    progress[id]=rank
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { for (id in source) if (!(id in progress)) bad("source lacks lifecycle " id); exit failed }
' "$REG/sources.tsv" "$REG/source-invariants.tsv" "$REG/source-progress.tsv" || fail "source lifecycle invalid"

LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if (FNR > 1) rank[$1]=$2 ~ /^(vocabulary_reviewed|skeleton_frozen|proof_active|complete)$/; next }
  FILENAME == ARGV[2] { if (FNR > 1) { source[$1]=$2; active[$1]=($12=="false") } next }
  FILENAME == ARGV[3] { if (FNR > 1) { basis[$1]=$2; reviewed[$1]++ } next }
  FILENAME == ARGV[4] { if (FNR > 1) vocabulary[$1]=1; next }
  FILENAME == ARGV[5] { if (FNR > 1) { claimUse[$1]++; vocabularyUse[$2]++ } next }
  END {
    for (id in active) {
      if (rank[source[id]] && active[id] && reviewed[id]!=1) bad("active claim lacks exactly one vocabulary review " id)
      if (!active[id] && reviewed[id]) bad("tombstoned claim has vocabulary review " id)
      if (basis[id]=="mathlib_only" && claimUse[id]) bad("mathlib-only claim has project vocabulary " id)
      if (rank[source[id]] && basis[id]=="project_vocabulary" && !claimUse[id]) bad("project-vocabulary claim lacks vocabulary use " id)
    }
    for (id in vocabulary) if (!vocabularyUse[id]) bad("unused vocabulary declaration " id)
    exit failed
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
' "$REG/source-progress.tsv" "$REG/claims.tsv" "$REG/claim-vocabulary-review.tsv" "$REG/vocabulary.tsv" "$REG/claim-vocabulary.tsv" || fail "vocabulary lifecycle coverage invalid"

echo "check-lifecycle: ok"
