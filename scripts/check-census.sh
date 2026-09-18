#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd)
fail() { echo "check-census: $*" >&2; exit 1; }

FIXTURE_MODE=0
EXPECTED_PAGES=534
EXPECTED_CLAIMS=3172
EXPECTED_EQUATIONS=1401
if [[ ${1:-} == --fixture ]]; then
  [[ $# -eq 2 || $# -eq 5 ]] || fail "usage: check-census.sh --fixture ROOT [EXPECTED_PAGES EXPECTED_CLAIMS EXPECTED_EQUATIONS]"
  ROOT=$(cd "$2" && pwd) || fail "invalid fixture root"
  [[ -n "${LATTICE_TEST_ROOT:-}" ]] || fail "fixture mode requires LATTICE_TEST_ROOT"
  TEST_ROOT=$(cd "$LATTICE_TEST_ROOT" && pwd) || fail "invalid LATTICE_TEST_ROOT"
  case "$TEST_ROOT" in "$PROJECT_ROOT"|"$PROJECT_ROOT"/*) fail "LATTICE_TEST_ROOT must be repository-external" ;; esac
  [[ "$TEST_ROOT" != / ]] || fail "LATTICE_TEST_ROOT must not contain the repository"
  case "$PROJECT_ROOT" in "$TEST_ROOT"|"$TEST_ROOT"/*) fail "LATTICE_TEST_ROOT must not contain the repository" ;; esac
  case "$ROOT/" in "$TEST_ROOT/"*) ;; *) fail "fixture root must be below LATTICE_TEST_ROOT" ;; esac
  FIXTURE_MODE=1
  if [[ $# -eq 5 ]]; then
    EXPECTED_PAGES=$3; EXPECTED_CLAIMS=$4; EXPECTED_EQUATIONS=$5
    [[ "$EXPECTED_PAGES" =~ ^[1-9][0-9]*$ && "$EXPECTED_CLAIMS" =~ ^[0-9]+$ && "$EXPECTED_EQUATIONS" =~ ^[0-9]+$ ]] || fail "fixture counts must be nonnegative integers and pages must be positive"
  fi
else
  ROOT=${1:-$PROJECT_ROOT}
  ROOT=$(cd "$ROOT" && pwd) || fail "invalid repository root"
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] || fail "ROOT must be the repository top"
fi

REG="$ROOT/registry"
{ IFS= read -r _; IFS= read -r phase; } < "$REG/phase.tsv"
if [[ "$phase" == bootstrap ]]; then
  [[ "$FIXTURE_MODE" -eq 0 ]] || fail "census fixture must use a post-bootstrap capability"
  echo "check-census: bootstrap capability; census completion gate not active"
  exit 0
fi
case "$phase" in census|vocabulary|skeleton|proof) ;; *) fail "unknown post-bootstrap checker capability: $phase" ;; esac

if [[ -f "$REG/sources.tsv" ]]; then
  "$PROJECT_ROOT/scripts/check-schema.sh" "$ROOT" >/dev/null
  "$PROJECT_ROOT/scripts/check-sources.sh" "$ROOT" >/dev/null
  "$PROJECT_ROOT/scripts/check-order.sh" "$ROOT" >/dev/null
  "$PROJECT_ROOT/scripts/check-lifecycle.sh" "$ROOT" >/dev/null

  while IFS=$'\t' read -r source lifecycle review_ref; do
    [[ "$source" == source_id ]] && continue
    case "$lifecycle" in
      census_reconciled|vocabulary_reviewed|skeleton_frozen|proof_active|complete)
        IFS=$'\t' read -r invariant_source expected_pages expected_claims expected_equations expected_empty_pages expected_oid invariant_review < <(awk -F '\t' -v s="$source" '$1==s { print; exit }' "$REG/source-invariants.tsv")
        [[ "${invariant_source:-}" == "$source" ]] || fail "reconciled source lacks invariants: $source"
        LC_ALL=C awk -F '\t' -v source="$source" -v expected="$expected_pages" '
          FNR == 1 || $2 != source { next }
          {
            n++
            if ($1!=sprintf("PG-%s-%04d",source,n) || $3!=sprintf("%06d",n) || $5!=n "") bad=1
            if ($4=="" || $4=="unspecified" || $6=="" || $7=="" || $8!="complete" || $9!="complete") bad=1
            if ($10 !~ /^[0-9a-f]+$/ || (length($10)!=40 && length($10)!=64)) bad=1
          }
          END { if (n!=expected || bad) exit 1 }
        ' "$REG/pages.tsv" || fail "page census invariant failed for $source; page census is not exact, contiguous, two-pass complete, and source-frozen"
        LC_ALL=C awk -F '\t' -v source="$source" -v expectedClaims="$expected_claims" -v expectedEquations="$expected_equations" -v expectedEmpty="$expected_empty_pages" '
          NR == FNR { if (FNR>1 && $2==source) page[$1]=1; next }
          FNR == 1 || $2 != source { next }
          $12=="false" {
            active++; usedPage[$4]=1
            if ($4=="" || $5=="" || $8=="" || $13!="NONE" || $14!="NONE" || $15!="NONE") bad=1
            if ($7=="equation") { equations++; label=$5; if (sub(/^.*; equation /,"",label)!=1 || label !~ /^\([^()]+\)$/) bad=1; pair=$4 SUBSEP label; if (seenPair[pair]++) bad=1 }
          }
          END { for (id in page) if (!(id in usedPage)) empty++; if (active!=expectedClaims || equations!=expectedEquations || empty!=expectedEmpty || bad) exit 1 }
        ' "$REG/pages.tsv" "$REG/claims.tsv" || fail "claim census invariant failed for $source; claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
        actual_oid=$(LC_ALL=C awk -F '\t' -v source="$source" 'FNR>1 && $2==source { print }' "$REG/pages.tsv" "$REG/claims.tsv" | git hash-object --stdin)
        [[ "$actual_oid" == "$expected_oid" ]] || fail "census OID mismatch for $source"
        ;;
    esac
  done < "$REG/source-progress.tsv"
  if [[ "$phase" == census ]]; then
    for table in slices dependencies bindings axioms claim-axioms; do
      [[ $(awk 'END { print NR }' "$REG/$table.tsv") -eq 1 ]] || fail "census capability requires header-only $table.tsv"
    done
  fi
  echo "check-census: ok"
  exit 0
fi

# Compatibility path for frozen R1/R2 fixtures only.
REF="$ROOT/references/tasaki-2020.tsv"
[[ -f "$REF" ]] || fail "legacy fixture lacks references/tasaki-2020.tsv"
if [[ "$FIXTURE_MODE" -eq 0 ]]; then
  awk -F '\t' 'NR==1&&($0!="source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes"||NF!=7){bad=1} NR==2&&(NF!=7||$1!="TASAKI2020"||$2!="Hal.Tasaki.P534.Physics_and_Mathematics_of_Quantum_Many_Body_Systems.pdf"||$3!="2020.springer.ebook.9783030412654"||$4!="91d1237a6384d470bcdc453f058f8e08603767c5"||$5!="342ef0ce220dd3ed1c6cc0cdfab5a4d86bbd044f"||$6!="frozen"){bad=1} END{if(NR!=2||bad)exit 1}' "$REF" || fail "production source identity, fingerprints, or coverage are not frozen exactly"
else
  awk -F '\t' 'NR==1&&($0!="source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes"||NF!=7){bad=1} NR==2{e=tolower($3);if(NF!=7||$1!="TASAKI2020"||e~/^(unspecified|pending|unknown|none)$/||$4!~/^[0-9a-f]+$/||$5!~/^[0-9a-f]+$/||length($4)!=length($5)||(length($4)!=40&&length($4)!=64)||$6!="frozen")bad=1} END{if(NR!=2||bad)exit 1}' "$REF" || fail "fixture source is not verified and frozen"
fi
LC_ALL=C awk -F '\t' -v expected="$EXPECTED_PAGES" 'FNR==1{next}{n++;if($1!=sprintf("PG-TASAKI2020-%04d",n)||$2!="TASAKI2020"||$3!=sprintf("%06d",n)||$4==""||$4=="unspecified"||$5!=n""||$6==""||$7==""||$8!="complete"||$9!="complete"||$10!~/^[0-9a-f]+$/||(length($10)!=40&&length($10)!=64))bad=1}END{if(n!=expected||bad)exit 1}' "$REG/pages.tsv" || fail "page census is not exact, contiguous, two-pass complete, and source-frozen"
LC_ALL=C awk -F '\t' -v expectedClaims="$EXPECTED_CLAIMS" -v expectedEquations="$EXPECTED_EQUATIONS" 'NR==FNR{if(FNR>1)pageOrder[$1]=$3;next}FNR==1{next}{claims++;if($2!="TASAKI2020"||$3!~/^[0-9][0-9][0-9][0-9][0-9][0-9]\.[0-9][0-9][0-9][0-9]$/||!($4 in pageOrder)||$5==""||$8==""||$12!="false"||$13!="NONE"||$14!="NONE"||$15!="NONE")bad=1;order=$3;if(substr(order,1,6)!=pageOrder[$4])bad=1;if(claims>1&&order<=previous)bad=1;previous=order;if($7=="equation"){equations++;label=$5;if(sub(/^.*; equation /,"",label)!=1||label!~/^\([^()]+\)$/)bad=1;pair=$4 SUBSEP label;if(seen[pair]++)bad=1}}END{if(claims==0||claims!=expectedClaims||equations!=expectedEquations||bad)exit 1}' "$REG/pages.tsv" "$REG/claims.tsv" || fail "claim count, active state, source order, page coupling, or equation label/page pairs are not exact"
if [[ "$phase" == census ]]; then for table in slices dependencies bindings axioms claim-axioms; do [[ $(awk 'END{print NR}' "$REG/$table.tsv") -eq 1 ]] || fail "census requires header-only $table.tsv"; done; fi
echo "check-census: ok"
