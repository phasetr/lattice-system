#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
ROOT=$(cd "$ROOT" && pwd)
# Fixtures use narrow imports; the scoped-notation case adds only its actual
# matrix API. Avoid the complete Mathlib umbrella in full-proof inspection.
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.skeleton.XXXXXX")
TMP=$(cd -P "$TMP" && pwd)
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
  if [[ $label == production-*-gates ]]; then
    printf '%s\n' "$output"
  fi
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
printf '%s\n' $'claim_id\tvocabulary_id' > "$GOOD/registry/claim-vocabulary.tsv"
printf '%s\n' $'claim_id\tbasis\treview_ref' \
  $'CL-SRA-0001\tmathlib_only\tfixture-review' \
  $'CL-SRA-0002\tmathlib_only\tfixture-review' \
  $'CL-SRB-0001\tmathlib_only\tfixture-review' > "$GOOD/registry/claim-vocabulary-review.tsv"
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
NONVACUITY=('/-- Explicit inhabitation witness for the fixture statement. -/' 'theorem StatementNonvacuity : Nonempty Statement := ⟨fun h => h⟩' '')
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
clone "$TMP/nonvacuity" "$TMP/nonvacuity-id-conclusion"
write_claims "$TMP/nonvacuity-id-conclusion/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Self-fulfilling obligation behind a reducible conclusion wrapper. -/' \
  'theorem StatementNonvacuity (h : Statement) : id Statement := h' ''
clone "$TMP/nonvacuity" "$TMP/nonvacuity-id-hypothesis"
write_claims "$TMP/nonvacuity-id-hypothesis/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Self-fulfilling obligation behind a reducible hypothesis wrapper. -/' \
  'theorem StatementNonvacuity (h : id Statement) : Statement := h' ''
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

# Reducibility attributes cannot conceal an otherwise identical obligation.
clone "$TMP/nonvacuity-wrapped" "$TMP/nonvacuity-irreducible"
write_claims "$TMP/nonvacuity-irreducible/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Reviewed irreducible wrapper around a self-implication. -/' \
  '@[irreducible] def SelfFulfilling : Prop := Statement → Statement' '' \
  '/-- Self-implication hidden behind an irreducible definition. -/' \
  'theorem StatementNonvacuity (h : Statement) : SelfFulfilling := by' \
  '  delta SelfFulfilling' '  exact fun _ => h' ''

# An irreducible identity can also conceal a literal True primary value.
clone "$GOOD" "$TMP/primary-irreducible-true"
rewrite "$TMP/primary-irreducible-true/registry/claim-context.tsv" 'NR==1{print}'
append "$TMP/primary-irreducible-true/registry/dependencies.tsv" $'CL-SRA-0002\trequires\tCL-SRA-0001\tNONE'
write_claims "$TMP/primary-irreducible-true/Fixture/Claims.lean" \
  '/-- Reviewed irreducible proposition identity. -/' \
  '@[irreducible] def Setup (p : Prop) : Prop := p' '' \
  '/-- Literal True hidden behind the reviewed identity. -/' \
  'def Statement : Prop := Setup True' '' "${PROOF[@]}"

# Exact obligations quantify the primary's universes in the proof's own order.
# The two declarations may spell their corresponding parameters differently.
POLYMORPHIC=('/-- Reviewed universe-polymorphic proposition. -/'
  'def Statement.{u} : Prop := ∀ (V : Type u), Setup → V = V' '')
POLYMORPHIC_TWO=('/-- Reviewed proposition with two ordered universes. -/'
  'def Statement.{u, v} : Prop := ∀ (V : Type u) (W : Type v), Setup → V = V ∧ W = W' '')
for variant in one alpha-two specialized reordered duplicated; do
  clone "$GOOD" "$TMP/proof-universe-$variant"
done
write_claims "$TMP/proof-universe-one/Fixture/Claims.lean" "${SETUP[@]}" "${POLYMORPHIC[@]}" \
  'set_option warningAsError false in' '/-- Exact universally quantified proof hole. -/' \
  'theorem StatementProof.{u} : Statement.{u} := by sorry' ''
write_claims "$TMP/proof-universe-alpha-two/Fixture/Claims.lean" "${SETUP[@]}" "${POLYMORPHIC_TWO[@]}" \
  'set_option warningAsError false in' '/-- Exact proof with alpha-renamed universe parameters. -/' \
  'theorem StatementProof.{x, y} : Statement.{x, y} := by sorry' ''
write_claims "$TMP/proof-universe-specialized/Fixture/Claims.lean" "${SETUP[@]}" "${POLYMORPHIC[@]}" \
  'set_option warningAsError false in' '/-- Specialized universe is not the universal obligation. -/' \
  'theorem StatementProof : Statement.{0} := by sorry' ''
write_claims "$TMP/proof-universe-reordered/Fixture/Claims.lean" "${SETUP[@]}" "${POLYMORPHIC_TWO[@]}" \
  'set_option warningAsError false in' '/-- Reordered universes are not the bound order. -/' \
  'theorem StatementProof.{x, y} : Statement.{y, x} := by sorry' ''
write_claims "$TMP/proof-universe-duplicated/Fixture/Claims.lean" "${SETUP[@]}" "${POLYMORPHIC_TWO[@]}" \
  'set_option warningAsError false in' '/-- Reusing one universe specializes the obligation. -/' \
  'theorem StatementProof.{x} : Statement.{x, x} := by sorry' ''
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
append "$VOCABULARY/registry/claim-vocabulary.tsv" $'CL-SRA-0002\tVO-FX-0001'
rewrite "$VOCABULARY/registry/claim-vocabulary-review.tsv" '$1=="CL-SRA-0002"{$2="project_vocabulary"}{print}'
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
  'theorem StatementNonvacuity : Nonempty Statement := ⟨fun h => (fun (_ : True) => h) Lean.trustCompiler⟩' ''

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

# Diagnostic consumers and explicit linter exemptions are separate from the
# registered stub's one declaration-owned warningAsError exception.
DIAGNOSTIC_SETUP=('/-- Setup whose unused argument normally emits a warning. -/'
  'def Setup (unused : Nat) : Prop := False' '')
DIAGNOSTIC_STATEMENT=('/-- Proposition referring to that setup. -/'
  'def Statement : Prop := Setup 0 → False' '')
for variant in guard-msgs linter-command linter-file linter-term linter-tactic nolint-inline nolint-command warn-option harmless-options; do
  clone "$GOOD" "$TMP/diagnostic-$variant"
done
write_claims "$TMP/diagnostic-guard-msgs/Fixture/Claims.lean" \
  '#guard_msgs (drop all) in' "${DIAGNOSTIC_SETUP[@]}" "${DIAGNOSTIC_STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-linter-command/Fixture/Claims.lean" \
  'set_option linter.unusedVariables false in' "${DIAGNOSTIC_SETUP[@]}" "${DIAGNOSTIC_STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-linter-file/Fixture/Claims.lean" \
  'set_option linter.unusedVariables false' "${DIAGNOSTIC_SETUP[@]}" "${DIAGNOSTIC_STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-linter-term/Fixture/Claims.lean" \
  '/-- A term-local linter exemption. -/' \
  'def Setup : Prop := set_option linter.unusedVariables false in False' '' \
  "${STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-linter-tactic/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'set_option warningAsError false in' '/-- A stub cannot disable an additional linter. -/' \
  'theorem StatementProof : Statement := by' \
  '  set_option linter.unusedVariables false in' '    sorry' ''
write_claims "$TMP/diagnostic-nolint-inline/Fixture/Claims.lean" \
  '/-- A declaration-local environment linter exemption. -/' \
  '@[nolint unusedArguments]' 'def Setup : Prop := False' '' "${STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-nolint-command/Fixture/Claims.lean" "${SETUP[@]}" \
  'attribute [nolint unusedArguments] Setup' "${STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-warn-option/Fixture/Claims.lean" \
  'set_option warn.classDefReducibility false in' "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}"
write_claims "$TMP/diagnostic-harmless-options/Fixture/Claims.lean" \
  'set_option maxRecDepth 4096' 'set_option pp.universes false in' \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}"
clone "$GOOD" "$TMP/diagnostic-linter-grind"
write_claims "$TMP/diagnostic-linter-grind/Fixture/Claims.lean" \
  '/-- Satisfiable setup for an unresolved grind fixture. -/' 'def Setup : Prop := (0 : Nat) = 0' '' \
  "${STATEMENT[@]}" 'set_option warningAsError false in' \
  '/-- Registered direct hole using the distinct grind option syntax. -/' \
  'theorem StatementProof : Statement := by' '  grind (abstractProof := false) =>' \
  '    set_option warningAsError false in' \
  '      set_option linter.unusedVariables false in' '        sorry' ''
clone "$GOOD" "$TMP/diagnostic-guard-panic"
write_claims "$TMP/diagnostic-guard-panic/Fixture/Claims.lean" \
  '#guard_panic in' '#check R4MissingPANIC' "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}"
# Warning exceptions belong to the actual registered declaration, independently
# of comments, line breaks, namespace spelling, or unrelated local options.
clone "$GOOD" "$TMP/warning-local-layout"
write_claims "$TMP/warning-local-layout/Fixture/Claims.lean" "${SETUP[@]}" "${STATEMENT[@]}" \
  'section Reviewed' 'set_option /- option -/ warningAsError /- value -/ false in -- local' \
  '/-- Registered proof under a parsed local exception. -/' \
  'theorem _root_.Fixture.StatementProof : Statement := by' \
  '  set_option warningAsError false in' '    sorry' 'end Reviewed' ''
for scope in file section namespace split; do
  clone "$GOOD" "$TMP/warning-$scope"
  prefix=('set_option warningAsError false -- trailing comment')
  suffix=()
  if [[ $scope == section ]]; then prefix=('section Quiet' "${prefix[@]}"); suffix=('end Quiet'); fi
  if [[ $scope == namespace ]]; then prefix=('namespace Quiet' "${prefix[@]}" 'end Quiet'); fi
  if [[ $scope == split ]]; then prefix=('set_option /- split -/ warningAsError' '  false -- trailing comment'); fi
  write_claims "$TMP/warning-$scope/Fixture/Claims.lean" "${prefix[@]}" \
    "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" "${suffix[@]}"
done
clone "$GOOD" "$TMP/warning-missing-exception"
write_claims "$TMP/warning-missing-exception/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" 'set_option warn.sorry false in' \
  '/-- A quiet hole still requires its registered warning exception. -/' \
  'theorem StatementProof : Statement := by sorry' ''
clone "$GOOD" "$TMP/warning-scoped-notation"
write_module "$TMP/warning-scoped-notation/Fixture/Claims.lean" \
  'Mathlib.Init Mathlib.LinearAlgebra.Matrix.Defs' "${SETUP[@]}" \
  'open scoped Matrix' '/-- A source proposition using imported scoped notation. -/' \
  'def Statement : Prop := Setup → ∀ M : Matrix Unit Unit Nat, Mᵀ = M' '' "${PROOF[@]}"
append "$TMP/warning-scoped-notation/registry/statement-imports.tsv" \
  $'Fixture.Claims\t2\tMathlib.LinearAlgebra.Matrix.Defs\ttrue\tfalse\tfalse'
clone "$GOOD" "$TMP/warning-borrowed-local"
write_claims "$TMP/warning-borrowed-local/Fixture/Claims.lean" \
  'set_option warningAsError false -- file-wide exception' \
  'set_option warningAsError false in' "${SETUP[@]}" "${STATEMENT[@]}" \
  '/-- Bound stub borrowing the setup declaration exception. -/' \
  'theorem StatementProof : Statement := by sorry' ''
clone "$GOOD" "$TMP/warning-unrelated-local"
write_claims "$TMP/warning-unrelated-local/Fixture/Claims.lean" \
  'set_option warningAsError false in' "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}"
clone "$GOOD" "$TMP/warning-term"
write_claims "$TMP/warning-term/Fixture/Claims.lean" \
  '/-- A setup value cannot disable warnings. -/' \
  'def Setup : Prop := set_option warningAsError false in False' '' \
  "${STATEMENT[@]}" "${PROOF[@]}"
clone "$TMP/nonvacuity" "$TMP/warning-completed"
write_claims "$TMP/warning-completed/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  'set_option warningAsError false in' "${NONVACUITY[@]}"
clone "$TMP/nonvacuity" "$TMP/warning-tactic"
write_claims "$TMP/warning-tactic/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- A completed witness cannot disable warnings in its tactic. -/' \
  'theorem StatementNonvacuity : Nonempty Statement := by' \
  '  set_option warningAsError false in' '    exact ⟨fun h => h⟩' ''
clone "$GOOD" "$TMP/warning-umbrella"
printf '%s\n' 'set_option warningAsError false -- umbrella exception' \
  >> "$TMP/warning-umbrella/Fixture/Skeleton.lean"

# These values actually reference imported theorem/opaque constants. Merely
# importing their modules would not exercise transitive kernel axiom traversal.
clone "$TMP/nonvacuity" "$TMP/imported-ordinary-theorem"
write_claims "$TMP/imported-ordinary-theorem/Fixture/Claims.lean" \
  "${SETUP[@]}" "${STATEMENT[@]}" "${PROOF[@]}" \
  '/-- Witness whose proof value actually refers to an imported ordinary theorem. -/' \
  'theorem StatementNonvacuity : Nonempty Statement := ⟨fun h => (fun (_ : 0 + 0 = 0) => h) (Nat.zero_add 0)⟩' ''
clone "$GOOD" "$TMP/imported-opaque-axiom"
write_claims "$TMP/imported-opaque-axiom/Fixture/Claims.lean" \
  'set_option linter.deprecated false in' \
  '/-- Imported opaque wrapper concealing an unsupported kernel axiom. -/' \
  'def Setup : Prop := Lean.reduceBool false = false' '' \
  "${STATEMENT[@]}" "${PROOF[@]}"

expect_pass frozen-oids "$ROOT/scripts/check-skeleton.sh" --fixture "$FROZEN"
expect_pass checker-copy env "LATTICE_SKELETON_CHECKER_DIR=$CHECKER_COPY" "$ROOT/scripts/check-skeleton.sh" --fixture "$FROZEN"
expect_pass axiom-frozen-type "$ROOT/scripts/check-skeleton.sh" --fixture "$AXIOM_FROZEN"
expect_pass required-by "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/required-by"
expect_pass type-context "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/type-context"
expect_pass registered-vocabulary "$ROOT/scripts/check-skeleton.sh" --fixture "$VOCABULARY"
expect_pass warning-local-layout "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/warning-local-layout"
expect_pass imported-ordinary-theorem env "LATTICE_SKELETON_ACTUAL_OUT=$TMP/imported-theorem-dump.tsv" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/imported-ordinary-theorem"
awk -F '\t' '$2=="Fixture.StatementNonvacuity"&&index(","$10",",",Nat.zero_add,")&&!index(","$11",",",Nat.zero_add,"){found=1}END{exit !found}' \
  "$TMP/imported-theorem-dump.tsv" || abort "imported ordinary theorem was not actually referenced"
expect_pass diagnostic-harmless-options "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-harmless-options"
expect_fail diagnostic-guard-msgs "forbidden diagnostic suppression #guard_msgs" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-guard-msgs"
for variant in command file term tactic; do
  expect_fail "diagnostic-linter-$variant" "forbidden diagnostic suppression linter.unusedVariables" \
    "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-linter-$variant"
done
for variant in inline command; do
  expect_fail "diagnostic-nolint-$variant" "forbidden diagnostic suppression nolint" \
    "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-nolint-$variant"
done
expect_fail diagnostic-guard-panic "forbidden diagnostic suppression #guard_panic" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-guard-panic"
expect_fail diagnostic-linter-grind "forbidden diagnostic suppression linter.unusedVariables" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-linter-grind"
expect_fail diagnostic-warn-option "forbidden diagnostic suppression warn.classDefReducibility" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/diagnostic-warn-option"
expect_pass warning-scoped-notation "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/warning-scoped-notation"
expect_fail warning-missing-exception "unresolved proof needs exactly one declaration-local warningAsError exception" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/warning-missing-exception"
for variant in file section namespace split borrowed-local unrelated-local term tactic umbrella; do
  expect_fail "warning-$variant" "unscoped warningAsError suppression" \
    "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/warning-$variant"
done
expect_fail warning-completed "warningAsError exception is not a registered unresolved proof" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/warning-completed"
expect_fail imported-opaque-axiom "unregistered nonstandard axiom Lean.trustCompiler" \
  env "LATTICE_SKELETON_ACTUAL_OUT=$TMP/imported-opaque-dump.tsv" \
  "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/imported-opaque-axiom"
awk -F '\t' '$2=="Fixture.Setup"&&index(","$10",",",Lean.reduceBool,")&&index(","$11",",",Lean.trustCompiler,"){found=1}END{exit !found}' \
  "$TMP/imported-opaque-dump.tsv" || abort "imported opaque wrapper and its kernel axiom were not both visited"

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
expect_fail nonvacuity-id-conclusion "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-id-conclusion"
expect_fail nonvacuity-id-hypothesis "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-id-hypothesis"
expect_fail nonvacuity-conjunct "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-conjunct"
expect_fail nonvacuity-wrapped "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-wrapped"
expect_fail nonvacuity-irreducible "nonvacuity declaration follows from its own hypotheses" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/nonvacuity-irreducible"
expect_fail primary-irreducible-true "literal True primary statement Fixture.Statement" "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/primary-irreducible-true"
expect_pass proof-universe-one "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/proof-universe-one"
expect_pass proof-universe-alpha-two "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/proof-universe-alpha-two"
for variant in specialized reordered duplicated; do
  expect_fail "proof-universe-$variant" "proof type is not exactly the bound primary statement" \
    "$ROOT/scripts/check-skeleton.sh" --fixture "$TMP/proof-universe-$variant"
done
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

# A counterfactual, minimal canonical project also runs the production branches.
# It owns its Git index and build outputs; only existing dependency artifacts
# are shared. No self-test is replaced or called recursively in this pipeline.
PRODUCTION=$TMP/production-composed
git clone --shared --no-checkout -q "$ROOT" "$PRODUCTION"
git -C "$PRODUCTION" checkout -q --detach HEAD
python3 - "$ROOT" "$GOOD" "$PRODUCTION" <<'PY'
from pathlib import Path
import csv
import importlib.util
import shutil
import subprocess
import sys
project, good, target = map(Path, sys.argv[1:])
for path in subprocess.check_output(['git', 'ls-files'], cwd=project).decode().splitlines():
    destination = target / path
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(project / path, destination)
    destination.chmod((project / path).stat().st_mode)
shutil.rmtree(target / 'LatticeSystem')
(target / 'LatticeSystem/Claims').mkdir(parents=True)
for path in (target / 'registry').glob('*.tsv'):
    path.write_text(path.read_text().splitlines()[0] + '\n')
for path in (good / 'registry').glob('*.tsv'):
    (target / 'registry' / path.name).write_bytes(path.read_bytes())
def write(name, rows):
    path = target / 'registry' / name
    header = path.read_text().splitlines()[0]
    path.write_text(header + '\n' + ''.join('\t'.join(row) + '\n' for row in rows))
write('tracks.tsv', [['TR-A', '1', 'Fixture A', 'a'], ['TR-B', '2', 'Fixture B', 'b']])
write('pages.tsv', [
    ['PG-SRA-0001', 'SRA', '000001', '1', '1', '1', 'content', 'complete', 'complete', 'a' * 40],
    ['PG-SRB-0001', 'SRB', '000001', '1', '1', '1', 'content', 'complete', 'complete', 'b' * 40]])
claim_rows = list(csv.reader((target / 'registry/claims.tsv').read_text().splitlines(), delimiter='\t'))
for row in claim_rows[1:]:
    row[4] = 'PDF p. 1; paragraph 1'
write('claims.tsv', claim_rows[1:])
# Use the canonical inventory derivation as well as its later strict validator.
spec = importlib.util.spec_from_file_location('r4_fixture_generator', project / 'scripts/generate-public-docs.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
def records(name):
    with (target / 'registry' / name).open(newline='') as stream:
        return list(csv.DictReader(stream, delimiter='\t', quoting=csv.QUOTE_NONE))
items, relations = generator.derive_source_items(
    records('claims.tsv'), records('pages.tsv'), records('sources.tsv'), records('tracks.tsv'))
write('source-items.tsv', [[row[field] for field in generator.HEADERS['source_items']] for row in items])
write('item-claims.tsv', [[row[field] for field in generator.HEADERS['item_claims']] for row in relations])
write('claim-vocabulary-review.tsv', [[claim, 'mathlib_only', 'FIXTURE-REVIEW'] for claim in
    ['CL-SRA-0001', 'CL-SRA-0002', 'CL-SRB-0001']])
write('modules.tsv', [['LatticeSystem', 'LatticeSystem.lean', 'root'],
                      ['LatticeSystem.Vocabulary', 'LatticeSystem/Vocabulary.lean', 'umbrella']])
write('imports.tsv', [['LatticeSystem', '1', 'LatticeSystem.Vocabulary', 'true', 'false', 'false'],
                      ['LatticeSystem.Vocabulary', '1', 'Mathlib.Init', 'true', 'false', 'false']])
write('statement-modules.tsv', [
    ['LatticeSystem.Claims.Front', 'LatticeSystem/Claims/Front.lean', 'leaf'],
    ['LatticeSystem.Skeleton', 'LatticeSystem/Skeleton.lean', 'umbrella']])
write('statement-imports.tsv', [
    ['LatticeSystem.Claims.Front', '1', 'Mathlib.Init', 'true', 'false', 'false'],
    ['LatticeSystem.Skeleton', '1', 'LatticeSystem.Claims.Front', 'true', 'false', 'false']])
bindings = (target / 'registry/bindings.tsv').read_text().replace('Fixture.Claims', 'LatticeSystem.Claims.Front')
bindings = bindings.replace('Fixture.', 'LatticeSystem.Claims.Front.')
(target / 'registry/bindings.tsv').write_text(bindings)
source = (good / 'Fixture/Claims.lean').read_text().replace('namespace Fixture', 'namespace LatticeSystem.Claims.Front').replace('end Fixture', 'end LatticeSystem.Claims.Front')
(target / 'LatticeSystem/Claims/Front.lean').write_text(source)
(target / 'LatticeSystem/Vocabulary.lean').write_text('module\n\npublic import Mathlib.Init\n\n/-! Counterfactual declaration-free vocabulary umbrella. -/\n')
(target / 'LatticeSystem/Skeleton.lean').write_text('module\n\npublic import LatticeSystem.Claims.Front\n\n/-! Counterfactual skeleton umbrella. -/\n')
(target / '.lake').mkdir(exist_ok=True)
(target / '.lake/packages').symlink_to((project / '.lake/packages').resolve(), target_is_directory=True)
PY
refresh_production() {
  python3 - "$1" <<'PY'
from pathlib import Path
import csv
import subprocess
import sys
root = Path(sys.argv[1])
def rows(name):
    with (root / 'registry' / name).open(newline='') as stream:
        return list(csv.reader(stream, delimiter='\t', quoting=csv.QUOTE_NONE))
def write(name, records):
    (root / 'registry' / name).write_text(''.join('\t'.join(row) + '\n' for row in records))
def blob(value):
    return subprocess.check_output(['git', 'hash-object', '--stdin'], input=value.encode(), cwd=root).decode().strip()
claims, pages = rows('claims.tsv'), rows('pages.tsv')
for row in claims[1:]:
    row[8] = blob(row[7])
write('claims.tsv', claims)
invariants = rows('source-invariants.tsv')[:1]
for source in ['SRA', 'SRB']:
    active = [row for row in claims[1:] if row[1] == source and row[11] == 'false']
    source_pages = [row for row in pages[1:] if row[1] == source]
    used = {row[3] for row in active}
    content = ''.join('\t'.join(row) + '\n' for row in pages[1:] + claims[1:] if row[1] == source)
    invariants.append([source, str(len(source_pages)), str(len(active)),
        str(sum(row[5] != 'out_of_scope' for row in active)),
        str(sum(row[6] == 'equation' for row in active)),
        str(sum(row[0] not in used for row in source_pages)), blob(content), 'FIXTURE-REVIEW'])
write('source-invariants.tsv', invariants)
PY
}
refresh_production "$PRODUCTION"
harvest "$PRODUCTION" "$TMP/production-dump.tsv"
freeze_bindings "$PRODUCTION/registry/bindings.tsv" "$TMP/production-dump.tsv"
python3 "$ROOT/scripts/generate-public-docs.py" --write --root "$PRODUCTION" >/dev/null
git -C "$PRODUCTION" add -- LatticeSystem.lean LatticeSystem registry docs scripts Checker
production_gates() {
  local dir=$1 gate
  for gate in tree schema sources order lifecycle registry census source-items policy vocabulary; do
    "$dir/scripts/check-$gate.sh" "$dir" || return
  done
  python3 "$dir/scripts/generate-public-docs.py" --check --root "$dir" || return
  (cd "$dir" && lake build) || return
  "$dir/scripts/check-skeleton.sh" "$dir"
}
expect_pass production-composed-gates production_gates "$PRODUCTION"
for variant in package-warning package-linter library-warning library-linter unknown-weak; do
  clone "$PRODUCTION" "$TMP/production-diagnostic-$variant"
done
python3 - "$TMP" <<'PYOPTIONS'
from pathlib import Path
import sys
root=Path(sys.argv[1])
for variant in ['package-warning','package-linter','library-warning','library-linter','unknown-weak']:
    path=root/('production-diagnostic-'+variant)/'lakefile.toml'
    text=path.read_text()
    if variant=='package-warning':
        text=text.replace('warningAsError = true','warningAsError = false')
    elif variant in ['package-linter','unknown-weak']:
        name='unusedVariables' if variant=='package-linter' else 'fixtureMissing'
        extra='weak.linter.'+name+' = false\n'
        if variant=='unknown-weak':
            extra+='pp.universes = false\nmaxRecDepth = 4096\n'
        text=text.replace('[[require]]',extra+'\n[[require]]')
    elif variant=='library-warning':
        text+='leanOptions = [["warningAsError", false]]\n'
    else:
        text+='leanOptions = [["weak.linter.unusedVariables", false]]\n'
    path.write_text(text)
PYOPTIONS
expect_pass production-diagnostic-unknown-weak-gates production_gates "$TMP/production-diagnostic-unknown-weak"
for owner in package library; do
  expect_fail "production-diagnostic-$owner-warning" "Lake diagnostic option disables warningAsError" \
    "$TMP/production-diagnostic-$owner-warning/scripts/check-skeleton.sh" "$TMP/production-diagnostic-$owner-warning"
  expect_fail "production-diagnostic-$owner-linter" "Lake diagnostic option disables linter.unusedVariables" \
    "$TMP/production-diagnostic-$owner-linter/scripts/check-skeleton.sh" "$TMP/production-diagnostic-$owner-linter"
done
for owner in package library; do
  for field in moreLeanArgs weakLeanArgs; do
    dir="$TMP/production-diagnostic-$owner-$field"
    clone "$PRODUCTION" "$dir"
    python3 - "$dir/lakefile.toml" "$owner" "$field" <<'PYRAW'
from pathlib import Path
import sys
path,owner,field=Path(sys.argv[1]),sys.argv[2],sys.argv[3]
extra=field+' = ["-DwarningAsError=false"]'
text=path.read_text()
if owner=='package':
    text=text.replace('defaultTargets = ["LatticeSystem"]','defaultTargets = ["LatticeSystem"]\n'+extra)
else:
    text+=extra+'\n'
path.write_text(text)
PYRAW
    expect_fail "production-diagnostic-$owner-$field" "Lake raw Lean arguments are unsupported in $owner" \
      "$dir/scripts/check-skeleton.sh" "$dir"
  done
done
for variant in safe-roots safe-globs skeleton-roots skeleton-globs package-deps library-deps library-needs facets source-path; do
  clone "$PRODUCTION" "$TMP/production-lake-$variant"
done
python3 - "$TMP" <<'PYLAKE'
from pathlib import Path
import sys
root = Path(sys.argv[1])
changes = {
    'safe-roots': 'roots = ["LatticeSystem", "LatticeSystem.Vocabulary"]',
    'safe-globs': 'roots = ["LatticeSystem", "LatticeSystem.Skeleton"]\nglobs = ["LatticeSystem", "LatticeSystem.Vocabulary"]',
    'skeleton-roots': 'roots = ["LatticeSystem", "LatticeSystem.Skeleton"]',
    'skeleton-globs': 'globs = ["LatticeSystem.*"]',
    'library-deps': 'extraDepTargets = ["LatticeSystem.Skeleton"]',
    'library-needs': 'needs = ["+LatticeSystem.Skeleton"]',
    'facets': 'defaultFacets = ["static"]',
    'source-path': 'srcDir = "alternate"',
}
for variant, extra in changes.items():
    path = root / ('production-lake-' + variant) / 'lakefile.toml'
    path.write_text(path.read_text() + extra + '\n')
path = root / 'production-lake-package-deps' / 'lakefile.toml'
path.write_text(path.read_text().replace('defaultTargets = ["LatticeSystem"]',
    'defaultTargets = ["LatticeSystem"]\nextraDepTargets = ["LatticeSystem.Skeleton"]'))
# This untracked alternative is deliberately selected by Lake's srcDir. The
# registry's physical source remains the production file, so path equality fails.
target = root / 'production-lake-source-path'
(target / 'alternate').mkdir()
(target / 'alternate/LatticeSystem.lean').write_bytes((target / 'LatticeSystem.lean').read_bytes())
PYLAKE
expect_pass production-lake-safe-roots-gates production_gates "$TMP/production-lake-safe-roots"
expect_pass production-lake-safe-globs-gates production_gates "$TMP/production-lake-safe-globs"
for variant in skeleton-roots skeleton-globs; do
  expect_fail "production-lake-$variant" "default library selects a statement or unregistered module" \
    "$TMP/production-lake-$variant/scripts/check-skeleton.sh" "$TMP/production-lake-$variant"
done
expect_fail production-lake-package-deps "package extraDepTargets is unsupported" \
  "$TMP/production-lake-package-deps/scripts/check-skeleton.sh" "$TMP/production-lake-package-deps"
for variant in library-deps library-needs; do
  expect_fail "production-lake-$variant" "library needs/extraDepTargets is unsupported" \
    "$TMP/production-lake-$variant/scripts/check-skeleton.sh" "$TMP/production-lake-$variant"
done
expect_fail production-lake-facets "default library facets must be leanArts" \
  "$TMP/production-lake-facets/scripts/check-skeleton.sh" "$TMP/production-lake-facets"
expect_fail production-lake-source-path "default module source differs from registry" \
  "$TMP/production-lake-source-path/scripts/check-skeleton.sh" "$TMP/production-lake-source-path"
# Even leanArts fetches configured plugin/dynamic-library targets while setting
# up a module. Reject these unsupported dependencies before executing any target.
for owner in package library; do
  for field in dynlibs plugins; do
    dir="$TMP/production-lake-$owner-$field"
    clone "$PRODUCTION" "$dir"
    python3 - "$dir/lakefile.toml" "$owner" "$field" <<'PYLAKE'
from pathlib import Path
import sys
path, owner, field = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
extra = field + ' = ["+LatticeSystem.Skeleton:dynlib"]'
text = path.read_text()
if owner == 'package':
    text = text.replace('defaultTargets = ["LatticeSystem"]',
        'defaultTargets = ["LatticeSystem"]\n' + extra)
else:
    text += extra + '\n'
path.write_text(text)
PYLAKE
    expect_fail "production-lake-$owner-$field" "$owner $field is unsupported" \
      "$dir/scripts/check-skeleton.sh" "$dir"
  done
done
# Matching only a seed's real path is insufficient: an ignored alternate srcDir
# can symlink that root while replacing the vocabulary module imported by it.
clone "$PRODUCTION" "$TMP/production-lake-shadow-vocabulary"
python3 - "$TMP/production-lake-shadow-vocabulary" <<'PYLAKE'
from pathlib import Path
import sys
root = Path(sys.argv[1])
shadow = root / '.lake/shadow-source'
(shadow / 'LatticeSystem').mkdir(parents=True)
(shadow / 'LatticeSystem.lean').symlink_to(root / 'LatticeSystem.lean')
(shadow / 'LatticeSystem/Vocabulary.lean').write_text(
    'module\n\npublic import Mathlib.Init\n\n'
    'set_option warningAsError false in\n'
    '/-- Unregistered theorem hidden behind a different physical provider. -/\n'
    'theorem UnregisteredShadow : True := by sorry\n')
config = root / 'lakefile.toml'
config.write_text(config.read_text() + 'srcDir = ".lake/shadow-source"\n')
PYLAKE
expect_fail production-lake-shadow-vocabulary "Lake vocabulary provider source differs from registry" \
  "$TMP/production-lake-shadow-vocabulary/scripts/check-skeleton.sh" "$TMP/production-lake-shadow-vocabulary"
# An alternate srcDir is harmless when every actual provider is a physical
# alias of the registered source, including the nondefault statement modules.
clone "$PRODUCTION" "$TMP/production-lake-alias-source"
python3 - "$TMP/production-lake-alias-source" <<'PYLAKE'
from pathlib import Path
import sys
root = Path(sys.argv[1])
alias = root / '.lake/alias-source'
for table in ['modules.tsv', 'statement-modules.tsv']:
    for row in (root / 'registry' / table).read_text().splitlines()[1:]:
        path = row.split('\t')[1]
        destination = alias / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.symlink_to(root / path)
config = root / 'lakefile.toml'
config.write_text(config.read_text() + 'srcDir = ".lake/alias-source"\n')
PYLAKE
expect_pass production-lake-alias-source-gates production_gates "$TMP/production-lake-alias-source"
clone "$TMP/production-lake-alias-source" "$TMP/production-lake-shadow-statement"
python3 - "$TMP/production-lake-shadow-statement" <<'PYLAKE'
from pathlib import Path
import sys
root = Path(sys.argv[1])
alias = root / '.lake/alias-source'
# Rebind copied absolute aliases to this independently owned clone.
for table in ['modules.tsv', 'statement-modules.tsv']:
    for row in (root / 'registry' / table).read_text().splitlines()[1:]:
        path = row.split('\t')[1]
        link = alias / path
        link.unlink()
        link.symlink_to(root / path)
leaf = 'LatticeSystem/Claims/Front.lean'
shadow = alias / leaf
shadow.unlink()
shadow.write_text((root / leaf).read_text() +
    '\nset_option warningAsError false in\n'
    '/-- Unregistered theorem in an alternate statement provider. -/\n'
    'theorem UnregisteredShadowStatement : True := by sorry\n')
PYLAKE
expect_fail production-lake-shadow-statement "Lake statement provider source differs from registry" \
  "$TMP/production-lake-shadow-statement/scripts/check-skeleton.sh" "$TMP/production-lake-shadow-statement"
for variant in pending frozen-oid any imports warning inactive-owner inactive-target proof-policy; do
  clone "$PRODUCTION" "$TMP/production-$variant"
done
rewrite "$TMP/production-pending/registry/bindings.tsv" 'NR==2{$7="PENDING"}{print}'
rewrite "$TMP/production-frozen-oid/registry/bindings.tsv" 'NR==2{$7="0000000000000000000000000000000000000000"}{print}'
rewrite "$TMP/production-any/registry/bindings.tsv" 'NR==2{$7="ANY"}{print}'
rewrite "$TMP/production-imports/registry/statement-imports.tsv" 'NR==2{$4="false"}{print}'
printf '%s\n' 'set_option warningAsError false -- file-wide exception' \
  >> "$TMP/production-warning/LatticeSystem/Claims/Front.lean"
printf '%s\n' phase proof > "$TMP/production-proof-policy/registry/phase.tsv"
for variant in owner target; do
  dir="$TMP/production-inactive-$variant"
  inactive=CL-SRB-0001
  [[ $variant != target ]] || inactive=CL-SRA-0001
  rewrite "$dir/registry/claims.tsv" \
    '$1=="'"$inactive"'"{$12="true";$13="CL-SRA-0002";$14="fixture-duplicate";$15="FIXTURE-REVIEW"}{print}'
  rewrite "$dir/registry/bindings.tsv" '$1!="'"$inactive"'"{print}'
  rewrite "$dir/registry/claim-vocabulary-review.tsv" '$1!="'"$inactive"'"{print}'
  if [[ $variant == owner ]]; then
    rewrite "$dir/registry/claim-context.tsv" 'NR==2{$1="CL-SRB-0001";$5="inherited"}{print}'
  fi
  refresh_production "$dir"
done
expect_fail production-pending "skeleton capability forbids pending binding OIDs" \
  production_gates "$TMP/production-pending"
expect_fail production-frozen-oid "wrong type OID" production_gates "$TMP/production-frozen-oid"
expect_fail production-any "bad statement type OID" production_gates "$TMP/production-any"
expect_fail production-imports "statement import registry/environment mismatch" production_gates "$TMP/production-imports"
expect_fail production-warning "unscoped warningAsError suppression" production_gates "$TMP/production-warning"
expect_fail production-inactive-owner "inactive claim-context owner or target" production_gates "$TMP/production-inactive-owner"
expect_fail production-inactive-target "inactive claim-context owner or target" production_gates "$TMP/production-inactive-target"
expect_fail production-proof-policy "production policy is not implemented for proof" production_gates "$TMP/production-proof-policy"

# Global registration is distinct from this claim's reviewed vocabulary use.
# The two counterexamples keep the R3 basis/use tables internally consistent.
PRODUCTION_VOCABULARY=$TMP/production-vocabulary
clone "$PRODUCTION" "$PRODUCTION_VOCABULARY"
printf '%s\n' module '' 'public import Mathlib.Init' '' '@[expose] public section' '' \
  'namespace LatticeSystem' '/-- First counterfactual vocabulary carrier. -/' \
  'def Ground : Type := Nat' '' '/-- Second counterfactual vocabulary carrier. -/' \
  'def AlternateGround : Type := Nat' '' 'end LatticeSystem' \
  > "$PRODUCTION_VOCABULARY/LatticeSystem/VocabularyData.lean"
printf '%s\n' module '' 'public import LatticeSystem.VocabularyData' '' \
  '/-! Counterfactual vocabulary umbrella. -/' \
  > "$PRODUCTION_VOCABULARY/LatticeSystem/Vocabulary.lean"
append "$PRODUCTION_VOCABULARY/registry/modules.tsv" \
  $'LatticeSystem.VocabularyData\tLatticeSystem/VocabularyData.lean\tleaf'
rewrite "$PRODUCTION_VOCABULARY/registry/imports.tsv" '$1=="LatticeSystem.Vocabulary"{$3="LatticeSystem.VocabularyData"}{print}'
append "$PRODUCTION_VOCABULARY/registry/imports.tsv" \
  $'LatticeSystem.VocabularyData\t1\tMathlib.Init\ttrue\tfalse\tfalse'
append "$PRODUCTION_VOCABULARY/registry/statement-imports.tsv" \
  $'LatticeSystem.Claims.Front\t2\tLatticeSystem.VocabularyData\ttrue\tfalse\tfalse'
append "$PRODUCTION_VOCABULARY/registry/vocabulary.tsv" \
  $'VO-LS-9001\tLatticeSystem.Ground\tLatticeSystem.VocabularyData\tdefinition\tprimary\tNONE\tPENDING\tPENDING\tstat_mech\tnone' \
  $'VO-LS-9002\tLatticeSystem.AlternateGround\tLatticeSystem.VocabularyData\tdefinition\tprimary\tNONE\tPENDING\tPENDING\tstat_mech\tnone'
append "$PRODUCTION_VOCABULARY/registry/claim-vocabulary.tsv" \
  $'CL-SRA-0001\tVO-LS-9001' $'CL-SRA-0002\tVO-LS-9001' $'CL-SRA-0002\tVO-LS-9002'
rewrite "$PRODUCTION_VOCABULARY/registry/claim-vocabulary-review.tsv" '$1~/^CL-SRA-/{$2="project_vocabulary"}{print}'
rewrite "$PRODUCTION_VOCABULARY/registry/claim-context.tsv" 'NR==2{$4="term_reference"}{print}'
rewrite "$PRODUCTION_VOCABULARY/registry/bindings.tsv" '$1=="CL-SRA-0001"{$6="definition_value"}{print}'
printf '%s\n' module '' 'public import Mathlib.Init' 'public import LatticeSystem.VocabularyData' '' \
  '@[expose] public section' '' 'namespace LatticeSystem.Claims.Front' \
  '/-- Primary type directly uses reviewed vocabulary. -/' \
  'def Setup (x : LatticeSystem.Ground) : Nat := x' '' \
  '/-- Primary value directly uses reviewed vocabulary and an earlier setup. -/' \
  'def Statement : Prop :=' \
  '  ∀ (x : LatticeSystem.Ground) (y : LatticeSystem.AlternateGround), Setup x = y' '' \
  'set_option warningAsError false in' '/-- Registered counterfactual direct proof hole. -/' \
  'theorem StatementProof : Statement := by sorry' '' 'end LatticeSystem.Claims.Front' \
  > "$PRODUCTION_VOCABULARY/LatticeSystem/Claims/Front.lean"
"$ROOT/scripts/check-vocabulary.sh" --dump --fixture "$PRODUCTION_VOCABULARY" > "$TMP/production-vocabulary-dump.tsv"
awk -F '\t' -v OFS='\t' '
  NR==FNR{if(FNR>1){type[$2]=$5;value[$2]=$6}next}
  FNR>1{$7=type[$2];$8=value[$2]}{print}
' "$TMP/production-vocabulary-dump.tsv" "$PRODUCTION_VOCABULARY/registry/vocabulary.tsv" > "$TMP/frozen-vocabulary.tsv"
cp "$TMP/frozen-vocabulary.tsv" "$PRODUCTION_VOCABULARY/registry/vocabulary.tsv"
harvest "$PRODUCTION_VOCABULARY" "$TMP/production-vocabulary-binding-dump.tsv"
awk -F '\t' '$2=="LatticeSystem.Claims.Front.Setup"&&index(","$9",",",LatticeSystem.Ground,"){found=1}END{exit !found}' \
  "$TMP/production-vocabulary-binding-dump.tsv" || abort "primary type vocabulary use was not observed"
awk -F '\t' '$2=="LatticeSystem.Claims.Front.Statement"&&index(","$10",",",LatticeSystem.Ground,")&&index(","$10",",",LatticeSystem.AlternateGround,"){found=1}END{exit !found}' \
  "$TMP/production-vocabulary-binding-dump.tsv" || abort "primary value vocabulary uses were not observed"
freeze_bindings "$PRODUCTION_VOCABULARY/registry/bindings.tsv" "$TMP/production-vocabulary-binding-dump.tsv"
python3 "$ROOT/scripts/generate-public-docs.py" --write --root "$PRODUCTION_VOCABULARY" >/dev/null
git -C "$PRODUCTION_VOCABULARY" add -- LatticeSystem registry docs
clone "$PRODUCTION_VOCABULARY" "$TMP/production-vocabulary-mathlib-basis"
rewrite "$TMP/production-vocabulary-mathlib-basis/registry/claim-vocabulary-review.tsv" '$1=="CL-SRA-0001"{$2="mathlib_only"}{print}'
rewrite "$TMP/production-vocabulary-mathlib-basis/registry/claim-vocabulary.tsv" '$1!="CL-SRA-0001"{print}'
clone "$PRODUCTION_VOCABULARY" "$TMP/production-vocabulary-unadmitted"
rewrite "$TMP/production-vocabulary-unadmitted/registry/claim-vocabulary.tsv" '!($1=="CL-SRA-0002"&&$2=="VO-LS-9002"){print}'
append "$TMP/production-vocabulary-unadmitted/registry/claim-vocabulary.tsv" $'CL-SRB-0001\tVO-LS-9002'
rewrite "$TMP/production-vocabulary-unadmitted/registry/claim-vocabulary-review.tsv" '$1=="CL-SRB-0001"{$2="project_vocabulary"}{print}'
for dir in "$TMP/production-vocabulary-mathlib-basis" "$TMP/production-vocabulary-unadmitted"; do
  python3 "$ROOT/scripts/generate-public-docs.py" --write --root "$dir" >/dev/null
done
expect_pass production-vocabulary-gates production_gates "$PRODUCTION_VOCABULARY"
expect_fail production-vocabulary-mathlib-basis "primary project vocabulary contradicts claim review basis" \
  production_gates "$TMP/production-vocabulary-mathlib-basis"
expect_fail production-vocabulary-unadmitted "primary vocabulary use lacks claim-vocabulary admission" \
  production_gates "$TMP/production-vocabulary-unadmitted"

echo "test-skeleton-semantic: diagnostic reached by each negative fixture"
LC_ALL=C sort "$REACHED" | awk -F '\t' '{printf "  %-20s %s\n", $1, $2}'
echo "test-skeleton-semantic: ok ($PASSES positive, $FAILURES negative)"
