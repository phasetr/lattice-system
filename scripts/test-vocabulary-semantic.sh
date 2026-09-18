#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.vocabulary-semantic.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP

expect_pass() { local label=$1; shift; "$@" >/dev/null 2>&1 || { echo "test-vocabulary-semantic: expected pass: $label" >&2; exit 1; }; }
expect_fail() {
  local label=$1 diagnostic=${2:-}; shift 2
  local output
  if output=$("$@" 2>&1); then echo "test-vocabulary-semantic: expected failure: $label" >&2; exit 1; fi
  [[ -z "$diagnostic" || "$output" == *"$diagnostic"* ]] || { echo "test-vocabulary-semantic: wrong diagnostic: $label" >&2; echo "$output" >&2; exit 1; }
}
prepare() {
  local name=$1 target="$TMP/$1"
  mkdir -p "$target/registry" "$target/Fixture"
  printf '%s\n' $'module\tsource_path\trole' $'Fixture.Subject\tFixture/Subject.lean\tumbrella' > "$target/registry/modules.tsv"
  printf '%s\n' $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' > "$target/registry/imports.tsv"
  printf '%s\n' \
    $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' \
    $'VO-FIXTURE-0001\tFixture.Item\tFixture.Subject\tabbrev\tprimary\tNONE\teda6899694a1d94c33f3b10aa4e8e71fe7970cd3\teedad8e975235d5b3d0801932bc9e971a4c2a5a3\tfixture\tnone' > "$target/registry/vocabulary.tsv"
  case "$name" in
    axiom) body=$'/-- Forbidden axiom fixture. -/\naxiom Item : Nat' ;;
    body) body=$'/-- Body drift fixture. -/\nabbrev Item := Int' ;;
    extra) body=$'/-- Registered fixture. -/\nabbrev Item := Nat\n/-- Unregistered fixture. -/\nabbrev Extra := Nat' ;;
    sorry) body=$'/-- Sorry fixture. -/\ndef Item : Nat := by sorry' ;;
    theorem) body=$'/-- Theorem fixture. -/\ntheorem Item : True := trivial' ;;
    structure) body=$'/-- Structure fixture. -/\nstructure Pair where\n  left : Nat\n  right : Nat' ;;
    transitive)
      mkdir -p "$target/Mathlib"
      printf '%s\n' 'module' '' '@[expose] public section' '' 'namespace Mathlib' '' '/-- Hidden unresolved dependency. -/' 'def hidden : Nat := by sorry' '' 'end Mathlib' > "$target/Mathlib/FixtureDependency.lean"
      body=$'/-- Transitive dependency fixture. -/\ndef Item : Nat := Mathlib.hidden'
      ;;
    *) body=$'/-- Harmless semantic-checker fixture. -/\nabbrev Item := Nat' ;;
  esac
  if [[ "$name" == import ]]; then
    imported='Mathlib.Data.Nat.Basic'
  elif [[ "$name" == transitive ]]; then
    imported='Mathlib.FixtureDependency'
  else
    imported='Init'
  fi
  printf '%s\n' 'module' '' "public import $imported" '' '@[expose] public section' '' 'namespace Fixture' '' "$body" '' 'end Fixture' > "$target/Fixture/Subject.lean"
}
mutate_vocab() {
  local name=$1 program=$2 file="$TMP/$1/registry/vocabulary.tsv"
  awk -F '\t' -v OFS='\t' "$program" "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
}

for name in good structure axiom extra import sorry theorem type body missing module graph finiteness transitive; do prepare "$name"; done

mutate_vocab axiom 'NR==2 {$4="definition";$7="471dd3a050827d736f2fc6858b2dc396f864af71";$8="PENDING"} {print}'
for name in extra import; do mutate_vocab "$name" 'NR==2 {$8="PENDING"} {print}'; done
mutate_vocab sorry 'NR==2 {$4="definition";$7="471dd3a050827d736f2fc6858b2dc396f864af71";$8="PENDING"} {print}'
mutate_vocab theorem 'NR==2 {$4="definition";$7="e05a1983e371947c14bd3b353ce23e5230136ffe";$8="PENDING"} {print}'
mutate_vocab type 'NR==2 {$7="0000000000000000000000000000000000000000";$8="PENDING"} {print}'
mutate_vocab missing 'NR==2 {$2="Fixture.Missing"} {print}'
mutate_vocab module 'NR==2 {$3="Fixture.Other"} {print}'
mutate_vocab graph 'NR==2 {$9="graph_core"} {print}'
mutate_vocab finiteness 'NR==2 {$10="local_operation"} {print}'
printf '%s\n' \
  $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' \
  $'VO-FIXTURE-0001\tFixture.Pair\tFixture.Subject\tstructure\tprimary\tNONE\teda6899694a1d94c33f3b10aa4e8e71fe7970cd3\t0586bd493d684bcfdfadaa8ff4947f51eec7c48e\tfixture\tnone' \
  $'VO-FIXTURE-0002\tFixture.Pair.left\tFixture.Subject\tprojection\tgenerated\tVO-FIXTURE-0001\t09117ddb3ec4f41df783154859883a9de3d050e2\tdd7d0075df1dd47237fddb4cca34b753916ce4bb\tgenerated\tinherited' \
  $'VO-FIXTURE-0003\tFixture.Pair.mk\tFixture.Subject\tconstructor\tgenerated\tVO-FIXTURE-0001\t70175a16711a85717984d042c516015d987420a8\t9fff138066c2a8c1f2806a98d48afaa072024658\tgenerated\tinherited' \
  $'VO-FIXTURE-0004\tFixture.Pair.rec\tFixture.Subject\trecursor\tgenerated\tVO-FIXTURE-0001\ta0e3a5ba971ba56e66b0a2cf7a38ee6dab0137ef\t83977b98a8d306caafe0acc5c6e163b7969eaeca\tgenerated\tinherited' \
  $'VO-FIXTURE-0005\tFixture.Pair.right\tFixture.Subject\tprojection\tgenerated\tVO-FIXTURE-0001\t09117ddb3ec4f41df783154859883a9de3d050e2\tf379ffda38c34d4b3959edf8c48281993ce88661\tgenerated\tinherited' > "$TMP/structure/registry/vocabulary.tsv"
mutate_vocab transitive 'NR==2 {$4="definition";$7="PENDING";$8="PENDING"} {print}'
printf '%s\n' $'module\tsource_path\trole' $'Mathlib.FixtureDependency\tMathlib/FixtureDependency.lean\tleaf' $'Fixture.Subject\tFixture/Subject.lean\tumbrella' > "$TMP/transitive/registry/modules.tsv"
printf '%s\n' $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' $'Fixture.Subject\t1\tMathlib.FixtureDependency\ttrue\tfalse\tfalse' > "$TMP/transitive/registry/imports.tsv"

expect_pass good "$ROOT/scripts/check-vocabulary.sh" --fixture "$TMP/good"
expect_pass structure "$ROOT/scripts/check-vocabulary.sh" --fixture "$TMP/structure"
for name in axiom extra import sorry theorem type body missing module graph finiteness; do expect_fail "$name" "" "$ROOT/scripts/check-vocabulary.sh" --fixture "$TMP/$name"; done
expect_fail transitive "transitive sorryAx dependency: Fixture.Item" "$ROOT/scripts/check-vocabulary.sh" --fixture "$TMP/transitive"

echo "test-vocabulary-semantic: ok"
