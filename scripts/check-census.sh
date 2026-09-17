#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
fail() { echo "check-census: $*" >&2; exit 1; }

FIXTURE_MODE=0
EXPECTED_PAGES=534
EXPECTED_CLAIMS=3172
EXPECTED_EQUATIONS=1401
if [[ ${1:-} == --fixture ]]; then
  [[ $# -eq 5 ]] || fail "usage: check-census.sh --fixture ROOT EXPECTED_PAGES EXPECTED_CLAIMS EXPECTED_EQUATIONS"
  ROOT=$(cd "$2" && pwd) || fail "invalid fixture root"
  case "$ROOT/" in "$PROJECT_ROOT/fixtures/"*) ;; *) fail "fixture root must be below fixtures/" ;; esac
  EXPECTED_PAGES=$3
  EXPECTED_CLAIMS=$4
  EXPECTED_EQUATIONS=$5
  [[ "$EXPECTED_PAGES" =~ ^[1-9][0-9]*$ && "$EXPECTED_CLAIMS" =~ ^[0-9]+$ && "$EXPECTED_EQUATIONS" =~ ^[0-9]+$ ]] || fail "fixture counts must be nonnegative integers and pages must be positive"
  FIXTURE_MODE=1
else
  ROOT=${1:-$PROJECT_ROOT}
  ROOT=$(cd "$ROOT" && pwd) || fail "invalid repository root"
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] || fail "ROOT must be the repository top"
fi

REG="$ROOT/registry"
REF="$ROOT/references/tasaki-2020.tsv"
{ IFS= read -r _; IFS= read -r phase; } < "$REG/phase.tsv"
if [[ "$phase" == bootstrap ]]; then
  [[ "$FIXTURE_MODE" -eq 0 ]] || fail "census fixture must use census phase"
  echo "check-census: bootstrap; census completion gate not active"
  exit 0
fi
case "$phase" in census|vocabulary|skeleton|proof) ;; *) fail "unknown post-bootstrap phase: $phase" ;; esac

if [[ "$FIXTURE_MODE" -eq 0 ]]; then
  awk -F '\t' '
    NR == 1 && ($0 != "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes" || NF != 7) { bad=1 }
    NR == 2 && (NF != 7 || $1 != "TASAKI2020" || $2 != "Hal.Tasaki.P534.Physics_and_Mathematics_of_Quantum_Many_Body_Systems.pdf" || $3 != "2020.springer.ebook.9783030412654" || $4 != "91d1237a6384d470bcdc453f058f8e08603767c5" || $5 != "342ef0ce220dd3ed1c6cc0cdfab5a4d86bbd044f" || $6 != "frozen") { bad=1 }
    END { if (NR != 2 || bad) exit 1 }
  ' "$REF" || fail "production source identity, fingerprints, or coverage are not frozen exactly"
else
  awk -F '\t' '
    NR == 1 && ($0 != "source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes" || NF != 7) { bad=1 }
    NR == 2 {
      edition=tolower($3)
      if (NF != 7 || $1 != "TASAKI2020" || edition ~ /^(unspecified|pending|unknown|none)$/ || $4 !~ /^[0-9a-f]+$/ || $5 !~ /^[0-9a-f]+$/ || length($4) != length($5) || (length($4) != 40 && length($4) != 64) || $6 != "frozen") bad=1
    }
    END { if (NR != 2 || bad) exit 1 }
  ' "$REF" || fail "fixture source is not verified and frozen"
fi

LC_ALL=C awk -F '\t' -v expected="$EXPECTED_PAGES" '
  FNR == 1 { next }
  {
    n++
    expectedId=sprintf("PG-TASAKI2020-%04d", n)
    expectedOrder=sprintf("%06d", n)
    if ($1 != expectedId || $2 != "TASAKI2020" || $3 != expectedOrder || $5 != n "") bad=1
    if ($4 == "" || $4 == "unspecified" || $6 == "" || $7 == "" || $8 != "complete" || $9 != "complete") bad=1
    if ($10 !~ /^[0-9a-f]+$/ || (length($10) != 40 && length($10) != 64)) bad=1
  }
  END { if (n != expected || bad) exit 1 }
' "$REG/pages.tsv" || fail "page census is not exact, contiguous, two-pass complete, and source-frozen"

LC_ALL=C awk -F '\t' -v expectedClaims="$EXPECTED_CLAIMS" -v expectedEquations="$EXPECTED_EQUATIONS" '
  NR == FNR {
    if (FNR > 1) pageOrder[$1]=$3
    next
  }
  FNR == 1 { next }
  {
    claims++
    if ($2 != "TASAKI2020" || $4 == "" || $5 == "" || $8 == "" || $12 != "false" || $13 != "NONE" || $14 != "NONE" || $15 != "NONE") bad=1
    order=$3
    prefix=substr(order, 1, 6)
    if (!($4 in pageOrder) || length(order) != 11 || substr(order, 7, 1) != "." || prefix != pageOrder[$4]) bad=1
    if (claims > 1 && order <= previousOrder) bad=1
    previousOrder=order
    if ($7 == "equation") {
      equations++
      label=$5
      if (sub(/^.*; equation /, "", label) != 1 || label !~ /^\([^()]+\)$/) bad=1
      pair=$4 SUBSEP label
      if (seenPair[pair]++) bad=1
    }
  }
  END { if (claims == 0 || claims != expectedClaims || equations != expectedEquations || bad) exit 1 }
' "$REG/pages.tsv" "$REG/claims.tsv" || fail "claim count, active state, source order, page coupling, or equation label/page pairs are not exact"

if [[ "$phase" == census ]]; then
  for table in slices dependencies bindings axioms claim-axioms; do
    [[ $(awk 'END { print NR }' "$REG/$table.tsv") -eq 1 ]] || fail "census requires header-only $table.tsv"
  done
fi

echo "check-census: ok"
