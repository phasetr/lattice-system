#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
ROOT=$(cd "$ROOT" && pwd)
# Fixtures use only core propositions and natural numbers. Avoid importing the
# complete Mathlib umbrella into the full-proof axiom inspection environment.
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.skeleton.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP

PASSES=0
FAILURES=0
REACHED=$TMP/reached.txt
: > "$REACHED"

expect_pass() {
  local label=$1 output
  shift
  output=$("$@" 2>&1) || {
    echo "test-skeleton-semantic: expected pass: $label" >&2
    echo "$output" >&2
    exit 1
  }
  PASSES=$((PASSES + 1))
}
# A negative fixture is evidence only when it reaches the gate it targets, so
# the matched diagnostic line is recorded and reported, not merely matched.
expect_fail() {
  local label=$1 diagnostic=$2 output reached
  shift 2
  if output=$("$@" 2>&1); then echo "test-skeleton-semantic: expected failure: $label" >&2; exit 1; fi
  [[ "$output" == *"$diagnostic"* ]] || { echo "test-skeleton-semantic: wrong diagnostic: $label" >&2; echo "$output" >&2; exit 1; }
  reached=$(printf '%s\n' "$output" | grep -F "$diagnostic" | head -n 1)
  printf '%s\t%s\n' "$label" "$reached" >> "$REACHED"
  FAILURES=$((FAILURES + 1))
}
clone() { cp -R "$1" "$2"; }
rewrite() { local file=$1 program=$2; awk -F '\t' -v OFS='\t' "$program" "$file" > "$file.tmp"; mv "$file.tmp" "$file"; }
append() { local file=$1; shift; { awk '{print}' "$file"; printf '%s\n' "$@"; } > "$file.tmp"; mv "$file.tmp" "$file"; }
abort() { echo "test-skeleton-semantic: $*" >&2; exit 1; }
# Claim modules are always written whole; portable `sed` cannot insert lines.
write_module() {
  local file=$1 imports=$2
  shift 2
  {
    printf '%s\n' module ''
    printf 'public import %s\n' $imports
    printf '%s\n' '' '@[expose] public section' '' 'namespace Fixture' ''
    printf '%s\n' "$@"
    printf '%s\n' 'end Fixture'
  } > "$file"
}
write_claims() { local file=$1; shift; write_module "$file" Mathlib.Init "$@"; }
# Registry OIDs are produced by this checker, so a fixture that ships real OIDs
# harvests them from the same environment dump it is later compared against.
harvest() {
  local dir=$1 out=$2
  LATTICE_SKELETON_ACTUAL_OUT=$out "$ROOT/scripts/check-skeleton.sh" --fixture "$dir" >/dev/null 2>&1 || true
  [[ -s "$out" ]] || abort "no environment dump harvested from $dir"
}
declaration_oid() {
  local dump=$1 declaration=$2 column=$3 value
  value=$(awk -F '\t' -v d="$declaration" -v c="$column" '$2==d{print $c}' "$dump")
  [[ "$value" =~ ^[0-9a-f]{40}$ ]] || abort "no object ID for $declaration column $column"
  printf '%s' "$value"
}
# Freeze every binding OID from a harvested dump, then prove no wildcard is left.
freeze_bindings() {
  local file=$1 dump=$2
  awk -F '\t' -v OFS='\t' -v dump="$dump" '
    BEGIN { while ((getline line < dump) > 0) { split(line, f, "\t"); type[f[2]]=f[4]; value[f[2]]=f[5] } }
    FNR==1 { print; next }
    {
      if ($2 in type) { $7=type[$2]; $8=value[$2] }
      if ($3!="NONE" && $3 in type) $11=type[$3]
      if ($13!="NONE" && $13 in type) $14=type[$13]
      print
    }
  ' "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
  grep -q PENDING "$file" && abort "frozen bindings still carry a wildcard OID"
  return 0
}
SETUP=('/-- Reviewed setup proposition. -/' 'def Setup : Prop := False' '')
STATEMENT=('/-- Reviewed proposition using its setup as an antecedent. -/' 'def Statement : Prop := Setup → False' '')
PROOF=('set_option warningAsError false in' '/-- Registered direct proof hole. -/'
  'theorem StatementProof : Statement := by sorry' '')

GOOD=$TMP/good
mkdir -p "$GOOD/registry" "$GOOD/Fixture"
printf '%s\n' phase skeleton > "$GOOD/registry/phase.tsv"
printf '%s\n' \
  $'source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage' \
  $'SRA\tTR-A\t1\tbook\tA\tA\tA\t2026\ted1\tnone\tNONE\tNONE\ta\tref\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tfrozen' \
  $'SRB\tTR-B\t1\tpaper\tB\tB\tB\t2026\ted1\tnone\tNONE\tNONE\tb\tref\t3333333333333333333333333333333333333333\t4444444444444444444444444444444444444444\tfrozen' > "$GOOD/registry/sources.tsv"
printf '%s\n' $'source_id\tlifecycle\treview_ref' \
  $'SRA\tskeleton_frozen\tfixture-review' $'SRB\tvocabulary_reviewed\tfixture-review' > "$GOOD/registry/source-progress.tsv"
printf '%s\n' \
  $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' \
  $'CL-SRA-0001\tSRA\t000001.0001\tPG-SRA-0001\tfixture setup\tdefinition\tdefinition\tSetup.\t1111111111111111111111111111111111111111\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
  $'CL-SRA-0002\tSRA\t000001.0002\tPG-SRA-0001\tfixture assertion\tassertion\ttheorem\tAssertion.\t2222222222222222222222222222222222222222\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
  $'CL-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tstaged later source\tassertion\ttheorem\tLater.\t3333333333333333333333333333333333333333\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' > "$GOOD/registry/claims.tsv"
printf '%s\n' $'item_id\tposition\tclaim_id' \
  $'IT-SRA-0001\t1\tCL-SRA-0001' $'IT-SRA-0001\t2\tCL-SRA-0002' \
  $'IT-SRB-0001\t1\tCL-SRB-0001' > "$GOOD/registry/item-claims.tsv"
printf '%s\n' $'claim_id\trole\ttarget_claim_id\trationale' > "$GOOD/registry/dependencies.tsv"
printf '%s\n' $'claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref' \
  $'CL-SRA-0002\t1\tCL-SRA-0001\tassumption\tsame_item\tfixture-review' > "$GOOD/registry/claim-context.tsv"
printf '%s\n' \
  $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref' \
  $'CL-SRA-0001\tFixture.Setup\tNONE\tFixture.Claims\tdefinition\tdefinition_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tfixture-review' \
  $'CL-SRA-0002\tFixture.Statement\tFixture.StatementProof\tFixture.Claims\tdefinition\tproof_proposition\tPENDING\tPENDING\tproof_stub\ttheorem\tPENDING\tNONE\tNONE\tNONE\tfixture-review' > "$GOOD/registry/bindings.tsv"
printf '%s\n' $'axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid' > "$GOOD/registry/axioms.tsv"
printf '%s\n' $'claim_id\taxiom_id' > "$GOOD/registry/claim-axioms.tsv"
printf '%s\n' \
  $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' > "$GOOD/registry/vocabulary.tsv"
printf '%s\n' $'module\tsource_path\trole' \
  $'Fixture.Production\tFixture/Production.lean\troot' > "$GOOD/registry/modules.tsv"
printf '%s\n' $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' \
  $'Fixture.Production\t1\tMathlib.Init\ttrue\tfalse\tfalse' > "$GOOD/registry/imports.tsv"
printf '%s\n' $'module\tsource_path\trole' \
  $'Fixture.Claims\tFixture/Claims.lean\tleaf' \
  $'Fixture.Skeleton\tFixture/Skeleton.lean\tumbrella' > "$GOOD/registry/statement-modules.tsv"
printf '%s\n' $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' \
  $'Fixture.Claims\t1\tMathlib.Init\ttrue\tfalse\tfalse' \
  $'Fixture.Skeleton\t1\tFixture.Claims\ttrue\tfalse\tfalse' > "$GOOD/registry/statement-imports.tsv"
printf '%s\n' module '' 'public import Mathlib.Init' '' '/-! Production fixture. -/' > "$GOOD/Fixture/Production.lean"
write_claims "$GOOD/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}"
printf '%s\n' module '' 'public import Fixture.Claims' '' '/-! Skeleton fixture umbrella. -/' > "$GOOD/Fixture/Skeleton.lean"

expect_pass good "$ROOT/scripts/check-skeleton.sh" --fixture "$GOOD"

# A reviewed dependency edge admits the same reference that claim-context does.
clone "$GOOD" "$TMP/dependency"
rewrite "$TMP/dependency/registry/claim-context.tsv" 'NR==1{print}'
append "$TMP/dependency/registry/dependencies.tsv" $'CL-SRA-0002\trequires\tCL-SRA-0001\tNONE'
expect_pass dependency-admitted "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/dependency"

# A reviewed nonvacuity witness that is neither `True` nor self-fulfilling.
NONVACUITY=('/-- Reviewed nonvacuity witness. -/' 'theorem StatementNonvacuity : Setup → Statement := fun h _ => h' '')
clone "$GOOD" "$TMP/nonvacuity"
rewrite "$TMP/nonvacuity/registry/bindings.tsv" 'NR==3{$13="Fixture.StatementNonvacuity";$14="PENDING"}{print}'
write_claims "$TMP/nonvacuity/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" "${NONVACUITY[@]}"
expect_pass nonvacuity-good "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity"

clone "$TMP/nonvacuity" "$TMP/nonvacuity-true"
write_claims "$TMP/nonvacuity-true/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- True surrogate offered as nonvacuity. -/' 'theorem StatementNonvacuity : True := trivial' ''
clone "$TMP/nonvacuity" "$TMP/nonvacuity-self"
write_claims "$TMP/nonvacuity-self/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Self-fulfilling statement offered as nonvacuity. -/' \
  'theorem StatementNonvacuity (h : Statement) : Statement := h' ''
clone "$TMP/nonvacuity" "$TMP/nonvacuity-unrelated"
write_claims "$TMP/nonvacuity-unrelated/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Unrelated triviality offered as nonvacuity. -/' \
  'theorem StatementNonvacuity : (1 : Nat) = 1 := rfl' ''
clone "$TMP/nonvacuity" "$TMP/nonvacuity-conjunct"
write_claims "$TMP/nonvacuity-conjunct/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Hypothesis restated beside a True conjunct. -/' \
  'theorem StatementNonvacuity (h : Statement) : Statement ∧ True := ⟨h, trivial⟩' ''

# A definition can hide the `(h : P) : P` shape from a plain binder telescope,
# so the reviewed wrapper is itself a registered claim statement here.
clone "$TMP/nonvacuity" "$TMP/nonvacuity-wrapped"
append "$TMP/nonvacuity-wrapped/registry/claims.tsv" \
  $'CL-SRA-0003\tSRA\t000001.0003\tPG-SRA-0001\tfixture wrapper\tdefinition\tdefinition\tWrapper.\t5555555555555555555555555555555555555555\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE'
append "$TMP/nonvacuity-wrapped/registry/item-claims.tsv" $'IT-SRA-0001\t3\tCL-SRA-0003'
append "$TMP/nonvacuity-wrapped/registry/bindings.tsv" \
  $'CL-SRA-0003\tFixture.SelfFulfilling\tNONE\tFixture.Claims\tdefinition\tdefinition_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tfixture-review'
append "$TMP/nonvacuity-wrapped/registry/dependencies.tsv" $'CL-SRA-0003\trequires\tCL-SRA-0002\tNONE'
write_claims "$TMP/nonvacuity-wrapped/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Reviewed wrapper around a self-implication. -/' \
  'def SelfFulfilling : Prop := Statement → Statement' '' \
  '/-- Self-implication offered as nonvacuity through a wrapper. -/' \
  'theorem StatementNonvacuity (h : Statement) : SelfFulfilling := fun _ => h' ''

# The shipped R4 configuration freezes all four binding OIDs, so the suite runs
# the real registry shape rather than the `PENDING` wildcard R4 forbids.
FROZEN=$TMP/frozen
clone "$TMP/nonvacuity" "$FROZEN"
harvest "$FROZEN" "$TMP/frozen-dump.tsv"
freeze_bindings "$FROZEN/registry/bindings.tsv" "$TMP/frozen-dump.tsv"
ZERO_OID=0000000000000000000000000000000000000000
clone "$FROZEN" "$TMP/frozen-statement-type"
rewrite "$TMP/frozen-statement-type/registry/bindings.tsv" "NR==3{\$7=\"$ZERO_OID\"}{print}"
clone "$FROZEN" "$TMP/frozen-statement-value"
rewrite "$TMP/frozen-statement-value/registry/bindings.tsv" "NR==3{\$8=\"$ZERO_OID\"}{print}"
clone "$FROZEN" "$TMP/frozen-proof-type"
rewrite "$TMP/frozen-proof-type/registry/bindings.tsv" "NR==3{\$11=\"$ZERO_OID\"}{print}"
clone "$FROZEN" "$TMP/frozen-nonvacuity"
rewrite "$TMP/frozen-nonvacuity/registry/bindings.tsv" "NR==3{\$14=\"$ZERO_OID\"}{print}"

# A value OID computed from the declaration type would pin nothing, so the
# checker itself is mutated to show the frozen fixture detects that.
CHECKER_COPY=$TMP/checker-copy
CHECKER_MUTANT=$TMP/checker-mutant
mkdir -p "$CHECKER_COPY" "$CHECKER_MUTANT"
cp -R "$ROOT/Checker" "$CHECKER_COPY/Checker"
cp -R "$ROOT/Checker" "$CHECKER_MUTANT/Checker"
awk '{ if ($0 ~ /valueEncoding info\]/) { sub(/valueEncoding info\]/, "encodeExpr info.levelParams info.type]"); hits++ } print }
     END { exit hits != 1 }' "$ROOT/Checker/Skeleton.lean" > "$CHECKER_MUTANT/Checker/Skeleton.lean" ||
  abort "value-encoding mutation did not apply exactly once"

# A registered axiom states an interface, so its type is frozen like any other
# registered declaration; the same name may not quietly assert something else.
AXIOM_FROZEN=$TMP/axiom-frozen
clone "$GOOD" "$AXIOM_FROZEN"
append "$AXIOM_FROZEN/registry/axioms.tsv" \
  $'AX-FIXTURE-0001\tFixture.interfaceAxiom\tFixture.Claims\tstate\tfixture\tfixture\treopen\tPENDING'
append "$AXIOM_FROZEN/registry/claim-axioms.tsv" $'CL-SRA-0002\tAX-FIXTURE-0001'
AXIOM_PROOF=('set_option warningAsError false in' '/-- Registered direct proof hole using the axiom. -/'
  'theorem StatementProof : Statement := by have := interfaceAxiom; sorry' '')
write_claims "$AXIOM_FROZEN/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  '/-- Registered interface axiom. -/' 'axiom interfaceAxiom : Setup' '' "${AXIOM_PROOF[@]}"
harvest "$AXIOM_FROZEN" "$TMP/axiom-dump.tsv"
axiom_type_oid=$(declaration_oid "$TMP/axiom-dump.tsv" Fixture.interfaceAxiom 4)
rewrite "$AXIOM_FROZEN/registry/axioms.tsv" "NR==2{\$8=\"$axiom_type_oid\"}{print}"
clone "$AXIOM_FROZEN" "$TMP/axiom-restated"
write_claims "$TMP/axiom-restated/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  '/-- Registered interface axiom restated as a stronger assertion. -/' \
  'axiom interfaceAxiom : False' '' "${AXIOM_PROOF[@]}"

# A proof obligation is pinned to the bound statement itself: a disjunction, a
# self-implication, and `True` are all weaker obligations that must be rejected.
clone "$GOOD" "$TMP/proof-disjunction"
write_claims "$TMP/proof-disjunction/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'set_option warningAsError false in' '/-- Obligation weakened to a disjunction. -/' \
  'theorem StatementProof : Statement ∨ True := by sorry' ''
clone "$GOOD" "$TMP/proof-implication"
write_claims "$TMP/proof-implication/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'set_option warningAsError false in' '/-- Obligation weakened to a self-implication. -/' \
  'theorem StatementProof : Statement → Statement := fun _ => by sorry' ''
clone "$GOOD" "$TMP/proof-true"
write_claims "$TMP/proof-true/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'set_option warningAsError false in' '/-- Obligation weakened to True. -/' \
  'theorem StatementProof : True := by sorry' ''

# `required_by` is the reviewed exception that pulls a later claim forward, so
# the admitted edge must run from the earlier owner to the later target.
FORWARD_CLAIMS=('/-- Reviewed proposition that stands alone. -/' 'def Statement : Prop := False → False' ''
  'set_option warningAsError false in' '/-- Registered direct proof hole. -/'
  'theorem StatementProof : Statement := by sorry' ''
  '/-- Reviewed setup pulled forward from the later claim. -/' 'def Setup : Prop := Statement → False' '')
clone "$GOOD" "$TMP/required-by"
rewrite "$TMP/required-by/registry/claim-context.tsv" 'NR==1{print}'
append "$TMP/required-by/registry/dependencies.tsv" $'CL-SRA-0002\trequired_by\tCL-SRA-0001\tfrontier-exception'
write_claims "$TMP/required-by/Fixture/Claims.lean" "${FORWARD_CLAIMS[@]}"
clone "$GOOD" "$TMP/required-by-backward"
rewrite "$TMP/required-by-backward/registry/claim-context.tsv" 'NR==1{print}'
append "$TMP/required-by-backward/registry/dependencies.tsv" $'CL-SRA-0001\trequired_by\tCL-SRA-0002\tfrontier-exception'

# A definitional binding carries its setup use in the declaration type, which is
# a different expression from the value the earlier scan looked at.
TYPE_CONTEXT=('/-- Reviewed context datum whose setup use is in its type. -/'
  'def Context : Setup → False := False.elim' '')
CONTEXT_ROW=$'CL-SRA-0003\t1\tCL-SRA-0001\tassumption\tsame_item\tfixture-review'
clone "$GOOD" "$TMP/type-context"
append "$TMP/type-context/registry/claims.tsv" \
  $'CL-SRA-0003\tSRA\t000001.0003\tPG-SRA-0001\tfixture context\tdefinition\tdefinition\tContext.\t5555555555555555555555555555555555555555\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE'
append "$TMP/type-context/registry/item-claims.tsv" $'IT-SRA-0001\t3\tCL-SRA-0003'
append "$TMP/type-context/registry/bindings.tsv" \
  $'CL-SRA-0003\tFixture.Context\tNONE\tFixture.Claims\tdefinition\tdefinition_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tfixture-review'
write_claims "$TMP/type-context/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" "${TYPE_CONTEXT[@]}"
clone "$TMP/type-context" "$TMP/type-context-unadmitted"
append "$TMP/type-context/registry/claim-context.tsv" "$CONTEXT_ROW"

# A term-level `let` supplies a value, not an antecedent, so it cannot satisfy a
# reviewed `assumption` context.
clone "$GOOD" "$TMP/let-guard"
write_claims "$TMP/let-guard/Fixture/Claims.lean" "${SETUP[@]}" \
  '/-- Reviewed proposition mentioning its setup only in a let value. -/' \
  'def Statement : Prop := let _s : Prop := Setup; False' '' "${PROOF[@]}"

# A primary statement may name registered R3 vocabulary; an unregistered project
# constant is rejected even when it elaborates.
VOCABULARY=$TMP/vocabulary
clone "$GOOD" "$VOCABULARY"
write_module "$VOCABULARY/Fixture/Vocab.lean" Mathlib.Init \
  '/-- Registered R3 vocabulary datum. -/' 'def Ground : Prop := False' ''
append "$VOCABULARY/registry/modules.tsv" $'Fixture.Vocab\tFixture/Vocab.lean\tleaf'
append "$VOCABULARY/registry/imports.tsv" $'Fixture.Vocab\t1\tMathlib.Init\ttrue\tfalse\tfalse'
append "$VOCABULARY/registry/statement-imports.tsv" $'Fixture.Claims\t2\tFixture.Vocab\ttrue\tfalse\tfalse'
append "$VOCABULARY/registry/vocabulary.tsv" \
  $'VO-FX-0001\tFixture.Ground\tFixture.Vocab\tdefinition\tprimary\tNONE\tPENDING\tPENDING\tfixture\tnone'
write_module "$VOCABULARY/Fixture/Claims.lean" 'Mathlib.Init Fixture.Vocab' "${SETUP[@]}" \
  '/-- Reviewed proposition naming registered vocabulary. -/' \
  'def Statement : Prop := Setup → Ground' '' "${PROOF[@]}"
clone "$VOCABULARY" "$TMP/vocabulary-unregistered"
rewrite "$TMP/vocabulary-unregistered/registry/vocabulary.tsv" 'NR==1{print}'

# A real imported kernel axiom must not disappear merely because it is absent
# from the project axiom registry. Deprecation is disabled only on these two
# intentionally invalid fixture declarations so they reach the axiom gate.
clone "$GOOD" "$TMP/nonstandard-primary-axiom"
write_claims "$TMP/nonstandard-primary-axiom/Fixture/Claims.lean" \
  'set_option linter.deprecated false in' \
  '/-- Unsupported kernel axiom in a negative primary fixture. -/' \
  'def Setup : Prop := Lean.trustCompiler = True.intro' '' \
  "${STATEMENT[@]}" "${PROOF[@]}"
clone "$TMP/nonvacuity" "$TMP/nonstandard-nonvacuity-axiom"
write_claims "$TMP/nonstandard-nonvacuity-axiom/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  'set_option linter.deprecated false in' \
  '/-- Unsupported kernel axiom in a negative nonvacuity fixture. -/' \
  'theorem StatementNonvacuity : Setup → Statement := fun h _ => (fun (_ : True) => h) Lean.trustCompiler' ''

clone "$GOOD" "$TMP/contract"
rewrite "$TMP/contract/registry/bindings.tsv" 'NR==1{print}'
rewrite "$TMP/contract/registry/statement-modules.tsv" 'NR==1{print}'
clone "$GOOD" "$TMP/missing"; rewrite "$TMP/missing/registry/bindings.tsv" 'NR!=3{print}'
clone "$GOOD" "$TMP/duplicate"; awk '1;NR==2{print}' "$TMP/duplicate/registry/bindings.tsv" > "$TMP/duplicate/registry/bindings.tmp"; mv "$TMP/duplicate/registry/bindings.tmp" "$TMP/duplicate/registry/bindings.tsv"
clone "$GOOD" "$TMP/count"; rewrite "$TMP/count/registry/claims.tsv" 'NR==3{$6="out_of_scope";$10="fixture-scope";$11="fixture-review"}{print}'
clone "$GOOD" "$TMP/name"; rewrite "$TMP/name/registry/bindings.tsv" 'NR==3{$2="Fixture.Missing"}{print}'
clone "$GOOD" "$TMP/module"; rewrite "$TMP/module/registry/bindings.tsv" 'NR==3{$4="Fixture.Skeleton"}{print}'
clone "$GOOD" "$TMP/kind"; rewrite "$TMP/kind/registry/bindings.tsv" 'NR==3{$5="abbrev"}{print}'
clone "$GOOD" "$TMP/oid"; rewrite "$TMP/oid/registry/bindings.tsv" 'NR==3{$7="0000000000000000000000000000000000000000"}{print}'

# A primary statement carries its proposition as a value, so a non-`Prop` value
# is the only way a `proof_proposition` shape can be false.
clone "$GOOD" "$TMP/shape"
rewrite "$TMP/shape/registry/bindings.tsv" 'NR==2{$6="proof_proposition"}{print}'
write_claims "$TMP/shape/Fixture/Claims.lean" \
  '/-- Reviewed setup datum. -/' 'def Setup : Type := Nat' '' "${STATEMENT[@]}" "${PROOF[@]}"

clone "$GOOD" "$TMP/extra"
write_claims "$TMP/extra/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Extra unregistered declaration. -/' 'def Extra : Nat := 0' ''

# `match`, `where`, and `let rec` elaborate to auxiliary declarations, so a
# primary statement must be a plain term.
clone "$GOOD" "$TMP/match"
write_claims "$TMP/match/Fixture/Claims.lean" "${SETUP[@]}" \
  '/-- Reviewed proposition written with a pattern match. -/' \
  'def Statement : Prop := Setup → match (0 : Nat) with | 0 => False | _ + 1 => False' '' \
  "${PROOF[@]}"
clone "$GOOD" "$TMP/multiple"
write_claims "$TMP/multiple/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'set_option warningAsError false in' '/-- Two registered-looking holes in one stub. -/' \
  'theorem StatementProof : Statement := by' '  have first : Statement := by sorry' \
  '  have second : Statement := by sorry' '  exact first' ''

# The hiding declaration must itself be a registered stub, otherwise the fixture
# stops at the earlier unregistered-declaration gate instead of this one.
clone "$GOOD" "$TMP/hidden"
append "$TMP/hidden/registry/claims.tsv" \
  $'CL-SRA-0003\tSRA\t000001.0003\tPG-SRA-0001\tfixture hidden assertion\tassertion\ttheorem\tOther.\t5555555555555555555555555555555555555555\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE'
append "$TMP/hidden/registry/item-claims.tsv" $'IT-SRA-0001\t3\tCL-SRA-0003'
append "$TMP/hidden/registry/bindings.tsv" \
  $'CL-SRA-0003\tFixture.Other\tFixture.OtherProof\tFixture.Claims\tdefinition\tproof_proposition\tPENDING\tPENDING\tproof_stub\ttheorem\tPENDING\tNONE\tNONE\tNONE\tfixture-review'
write_claims "$TMP/hidden/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  '/-- Independently reviewed proposition. -/' 'def Other : Prop := False → False' '' \
  'set_option warningAsError false in' '/-- Registered direct proof hole. -/' \
  'theorem OtherProof : Other := by sorry' '' \
  'set_option warningAsError false in' '/-- Bound proof hides its hole behind another stub. -/' \
  'theorem StatementProof : Statement := OtherProof' ''

clone "$GOOD" "$TMP/context"; rewrite "$TMP/context/registry/claim-context.tsv" 'NR==1{print}'
clone "$GOOD" "$TMP/backward"; awk 'NR==2{held=$0;next}NR==3{print;print held;next}{print}' "$GOOD/registry/claims.tsv" > "$TMP/backward/registry/claims.tsv"

# Dropping the umbrella import from both the source and the import registry keeps
# the registry/environment comparison green so this fixture reaches isolation.
clone "$GOOD" "$TMP/umbrella"
rewrite "$TMP/umbrella/registry/statement-imports.tsv" 'NR<=2{print}'
printf '%s\n' module '' '/-! Skeleton fixture umbrella without its leaf. -/' > "$TMP/umbrella/Fixture/Skeleton.lean"

clone "$GOOD" "$TMP/leak"
printf '%s\n' module '' 'public import Fixture.Claims' '' '/-! Leaking production fixture. -/' > "$TMP/leak/Fixture/Production.lean"
rewrite "$TMP/leak/registry/imports.tsv" 'NR==2{$3="Fixture.Claims"}{print}'
clone "$GOOD" "$TMP/axiom"
append "$TMP/axiom/registry/axioms.tsv" $'AX-FIXTURE-0001\tFixture.allowed\tFixture.Claims\tstate\tfixture\tfixture\tremove\tPENDING'
write_claims "$TMP/axiom/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Approved but unused axiom. -/' 'axiom allowed : False' ''
clone "$GOOD" "$TMP/warning"
write_claims "$TMP/warning/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'set_option warningAsError false' '/-- Module-wide suppression around the hole. -/' \
  'theorem StatementProof : Statement := by sorry' ''

expect_pass frozen-oids "$ROOT/scripts/check-skeleton.sh" --fixture "$FROZEN"
expect_pass checker-copy env "LATTICE_SKELETON_CHECKER_DIR=$CHECKER_COPY" "$ROOT/scripts/check-skeleton.sh" --fixture "$FROZEN"
expect_pass axiom-frozen-type "$ROOT/scripts/check-skeleton.sh" --fixture "$AXIOM_FROZEN"
expect_pass required-by "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/required-by"
expect_pass type-context "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/type-context"
expect_pass registered-vocabulary "$ROOT/scripts/check-skeleton.sh" --fixture "$VOCABULARY"

expect_fail nonstandard-primary-axiom "unregistered nonstandard axiom Lean.trustCompiler" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonstandard-primary-axiom"
expect_fail nonstandard-nonvacuity-axiom "unregistered nonstandard axiom Lean.trustCompiler" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonstandard-nonvacuity-axiom"
expect_fail contract "skeleton capability requires a registered skeleton" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/contract"
expect_fail missing "skeleton source lacks a binding" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/missing"
expect_fail duplicate "duplicate binding" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/duplicate"
expect_fail count "binding count does not match formalization targets" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/count"
expect_fail name "missing or wrong-module declaration" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/name"
expect_fail module "missing or wrong-module declaration" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/module"
expect_fail kind "wrong declaration kind" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/kind"
expect_fail oid "wrong type OID" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/oid"
expect_fail shape "proof proposition is not Prop-valued" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/shape"
expect_fail extra "extra declaration Fixture.Extra" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/extra"
expect_fail match "extra declaration Fixture.Statement.match_1" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/match"
expect_fail multiple "exactly one direct sorryAx" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/multiple"
expect_fail hidden "hidden or transitive-only sorryAx" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/hidden"
expect_fail nonvacuity-true "nonvacuity declaration concludes True" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-true"
expect_fail nonvacuity-self "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-self"
expect_fail nonvacuity-conjunct "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-conjunct"
expect_fail nonvacuity-wrapped "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-wrapped"
expect_fail nonvacuity-unrelated "nonvacuity declaration does not reference its bound statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-unrelated"
expect_fail frozen-statement-type "wrong type OID Fixture.Statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/frozen-statement-type"
expect_fail frozen-statement-value "wrong value OID Fixture.Statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/frozen-statement-value"
expect_fail frozen-proof-type "wrong type OID Fixture.StatementProof" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/frozen-proof-type"
expect_fail frozen-nonvacuity "wrong type OID Fixture.StatementNonvacuity" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/frozen-nonvacuity"
expect_fail value-encoding-mutant "wrong value OID Fixture.Statement" \
  env "LATTICE_SKELETON_CHECKER_DIR=$CHECKER_MUTANT" "$ROOT/scripts/check-skeleton.sh" --fixture "$FROZEN"
expect_fail axiom-restated "wrong type OID Fixture.interfaceAxiom" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/axiom-restated"
expect_fail proof-disjunction "proof type is not exactly the bound primary statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/proof-disjunction"
expect_fail proof-implication "proof type is not exactly the bound primary statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/proof-implication"
expect_fail proof-true "proof type is not exactly the bound primary statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/proof-true"
expect_fail required-by-backward "required_by reference does not pull a later claim forward" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/required-by-backward"
expect_fail type-context-unadmitted "actual setup reference lacks claim-context or dependency CL-SRA-0003" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/type-context-unadmitted"
expect_fail let-guard "assumption context is not a binder or antecedent" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/let-guard"
expect_fail vocabulary-unregistered "primary statement uses an unregistered project constant Fixture.Ground" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/vocabulary-unregistered"
expect_fail context "actual setup reference lacks claim-context" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/context"
expect_fail backward "statement references a claim that is not earlier" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/backward"
expect_fail umbrella "umbrella misses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/umbrella"
expect_fail leak "production root reaches" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/leak"
expect_fail axiom "registered axiom is unused" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/axiom"
expect_fail warning "warningAsError suppression" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/warning"

echo "test-skeleton-semantic: diagnostic reached by each negative fixture"
LC_ALL=C sort "$REACHED" | awk -F '\t' '{printf "  %-20s %s\n", $1, $2}'
echo "test-skeleton-semantic: ok ($PASSES positive, $FAILURES negative)"
