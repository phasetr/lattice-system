#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
REG="$ROOT/registry"
fail() { echo "check-sources: $*" >&2; exit 1; }

LC_ALL=C awk -F '\t' '
  FNR == 1 { next }
  $1 !~ /^TR-[A-Z][A-Z0-9_]*$/ { bad("bad track ID " $1) }
  $2 !~ /^[1-9][0-9]*$/ || $2+0 != ++position { bad("track positions are not contiguous") }
  $3 == "" { bad("empty track title") }
  $4 !~ /^[a-z0-9]+(-[a-z0-9]+)*$/ { bad("bad track public slug " $4) }
  seenId[$1]++ { bad("duplicate track ID " $1) }
  seenSlug[$4]++ { bad("duplicate track public slug " $4) }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { if (NR == 1) bad("no tracks registered"); exit failed }
' "$REG/tracks.tsv" || fail "track registry invalid"

LC_ALL=C awk -F '\t' '
  function oid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  function slug(s) { return s ~ /^[a-z0-9]+(-[a-z0-9]+)*$/ }
  NR == FNR { if (FNR > 1) { track[$1]=$2+0; trackCount++ } next }
  FNR == 1 { next }
  $1 !~ /^[A-Z][A-Z0-9_]*$/ { bad("bad source ID " $1) }
  !($2 in track) { bad("unknown source track " $2) }
  $3 !~ /^[1-9][0-9]*$/ || $3+0 != ++position[$2] { bad("source positions are not contiguous in " $2) }
  $4 !~ /^(book|paper|preprint|other)$/ { bad("bad source kind " $4) }
  !token($5) { bad("bad citation key") }
  $6 == "" || $7 == "" { bad("empty source title or authors") }
  $8 !~ /^[0-9][0-9][0-9][0-9]$/ { bad("bad source year") }
  $9 == "" { bad("empty source edition") }
  $10 !~ /^(isbn|doi|arxiv|none)$/ { bad("bad identifier kind") }
  $10 == "none" && ($11 != "NONE" || $12 != "NONE") { bad("none identifier requires NONE value and URL") }
  $10 != "none" && (($11 == "" || $11 == "NONE") || $12 !~ /^https:\/\//) { bad("identified source requires identifier and HTTPS public URL") }
  !slug($13) { bad("bad source public slug") }
  $14 == "" { bad("empty local reference key") }
  (($15 == "") != ($16 == "")) { bad("source OIDs must transition atomically") }
  $15 != "" && (!oid($15) || !oid($16) || length($15)!=length($16)) { bad("bad source OID pair") }
  $17 !~ /^(pending|pass1|pass2|reconciled|frozen)$/ { bad("bad source coverage " $17) }
  seenId[$1]++ { bad("duplicate source ID " $1) }
  seenCitation[$5]++ { bad("duplicate citation key " $5) }
  seenSlug[$13]++ { bad("duplicate source public slug " $13) }
  {
    tuple=sprintf("%09d.%09d", track[$2], $3)
    if (rows && tuple <= previous) bad("sources are not in global track order")
    previous=tuple; rows++
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { if (!rows) bad("no sources registered"); exit failed }
' "$REG/tracks.tsv" "$REG/sources.tsv" || fail "source registry invalid"

LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  NR == FNR { if (FNR > 1) source[$1]=1; next }
  FNR == 1 { next }
  !($1 in source) { bad("unknown progress source " $1) }
  $2 !~ /^(registered|source_frozen|census_pass1|census_pass2|census_reconciled|vocabulary_reviewed|skeleton_frozen|proof_active|complete)$/ { bad("bad source lifecycle " $2) }
  !token($3) { bad("bad source progress review token") }
  seen[$1]++ { bad("duplicate source progress " $1) }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { for (id in source) if (!(id in seen)) bad("source lacks progress row " id); exit failed }
' "$REG/sources.tsv" "$REG/source-progress.tsv" || fail "source progress invalid"

LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  function oid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  NR == FNR { if (FNR > 1) source[$1]=1; next }
  FNR == 1 { next }
  !($1 in source) { bad("unknown invariant source " $1) }
  $2 !~ /^[1-9][0-9]*$/ || $3 !~ /^[0-9]+$/ || $4 !~ /^[0-9]+$/ || $5 !~ /^[0-9]+$/ || $6 !~ /^[0-9]+$/ { bad("bad source invariant count") }
  $4+0 > $3+0 { bad("formalization target count exceeds active claim count") }
  $6+0 > $2+0 { bad("no-claim page count exceeds physical page count") }
  !oid($7) { bad("bad census OID") }
  !token($8) { bad("bad invariant review token") }
  seen[$1]++ { bad("duplicate source invariant " $1) }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/sources.tsv" "$REG/source-invariants.tsv" || fail "source invariants invalid"

echo "check-sources: ok"
