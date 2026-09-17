#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
fail() { echo "check-vocabulary: $*" >&2; exit 1; }

MODE=check
FIXTURE=0
ROOT=
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dump) MODE=dump; shift ;;
    --fixture) FIXTURE=1; shift; [[ $# -gt 0 ]] || fail "--fixture requires ROOT"; ROOT=$1; shift ;;
    --*) fail "unknown option: $1" ;;
    *) [[ -z "$ROOT" ]] || fail "multiple roots supplied"; ROOT=$1; shift ;;
  esac
done
ROOT=${ROOT:-$PROJECT_ROOT}
ROOT=$(cd "$ROOT" && pwd) || fail "invalid root"
if [[ "$FIXTURE" -eq 1 ]]; then
  case "$ROOT/" in "$PROJECT_ROOT/fixtures/"*) ;; *) fail "fixture root must be below fixtures/" ;; esac
else
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] ||
    fail "ROOT must be the repository top (use --fixture for a fixture)"
fi

REG=$ROOT/registry
MODULES=$REG/modules.tsv
VOCAB=$REG/vocabulary.tsv
IMPORTS=$REG/imports.tsv
[[ -f "$MODULES" && -f "$VOCAB" && -f "$IMPORTS" ]] ||
  fail "modules.tsv, vocabulary.tsv, and imports.tsv are required"

[[ $(head -n 1 "$MODULES") == $'module\tsource_path\trole' ]] || fail "bad modules.tsv header"
[[ $(head -n 1 "$VOCAB") == $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' ]] || fail "bad vocabulary.tsv header"
[[ $(head -n 1 "$IMPORTS") == $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' ]] || fail "bad imports.tsv header"

TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-r3-vocabulary.XXXXXX")
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT HUP INT TERM

LEAN=$(elan which lean)
BASE_LEAN_PATH=$(cd "$PROJECT_ROOT" && lake env printenv LEAN_PATH)
export LEAN_PATH="$TMP:$BASE_LEAN_PATH"

mkdir -p "$TMP/Checker"
"$LEAN" --root="$PROJECT_ROOT" "$PROJECT_ROOT/Checker/R3Vocabulary.lean" \
  -o "$TMP/Checker/R3Vocabulary.olean" >/dev/null || fail "failed to compile semantic checker"

awk -F '\t' 'NR > 1 { print $1 }' "$MODULES" > "$TMP/modules.list"
: > "$TMP/compiled.list"
remaining=$(awk 'END { print NR - 1 }' "$MODULES")
while [[ "$remaining" -gt 0 ]]; do
  progressed=0
  while IFS=$'\t' read -r module source_path role extra; do
    [[ "$module" != module ]] || continue
    grep -Fqx "$module" "$TMP/compiled.list" && continue
    [[ -z "${extra:-}" && -n "$source_path" && -n "$role" ]] || fail "malformed modules.tsv row for $module"
    [[ "$module" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]] || fail "unsafe module name: $module"
    [[ "$source_path" != /* && "$source_path" != *..* && "$source_path" == *.lean ]] || fail "unsafe source_path for $module"
    [[ -f "$ROOT/$source_path" ]] || fail "missing source_path for $module: $source_path"
    blocked=0
    while IFS= read -r dep; do
      [[ -n "$dep" ]] || continue
      if grep -Fqx "$dep" "$TMP/modules.list" && ! grep -Fqx "$dep" "$TMP/compiled.list"; then
        blocked=1
        break
      fi
    done < <(awk -F '\t' -v m="$module" 'NR > 1 && $1 == m { print $3 }' "$IMPORTS")
    [[ "$blocked" -eq 0 ]] || continue
    out="$TMP/${module//./\/}.olean"
    mkdir -p "${out%/*}"
    "$LEAN" --root="$ROOT" "$ROOT/$source_path" -o "$out" >/dev/null ||
      fail "failed to elaborate registered module $module"
    printf '%s\n' "$module" >> "$TMP/compiled.list"
    remaining=$((remaining - 1))
    progressed=1
  done < "$MODULES"
  [[ "$progressed" -eq 1 ]] || fail "registered module import graph is cyclic or incomplete"
done

{
  echo module
  while IFS= read -r module; do
    printf 'public import %s\n' "$module"
  done < "$TMP/modules.list"
  echo 'public meta import Checker.R3Vocabulary'
  echo
  printf '#r3_vocabulary_dump "%s" "%s"\n' "$TMP/modules.list" "$TMP/environment.tsv"
} > "$TMP/R3VocabularyRun.lean"
"$LEAN" --root="$TMP" "$TMP/R3VocabularyRun.lean" -o "$TMP/R3VocabularyRun.olean" >/dev/null ||
  fail "semantic environment inspection failed"

: > "$TMP/actual-vocabulary.tsv"
mkdir -p "$TMP/types"
mkdir -p "$TMP/declarations"
awk -F '\t' -v dir="$TMP/types" -v declDir="$TMP/declarations" '$1 == "D" {
  n++
  print n "\t" $2 "\t" $3 "\t" $4 "\t" $5 "\t" $6 "\t" $7 "\t" $8 "\t" $9 "\t" $10 "\t" $11
  printf "%s", $12 > (dir "/" n)
  printf "%s", $13 > (declDir "/" n)
}' "$TMP/environment.tsv" > "$TMP/declaration-index.tsv"
while IFS=$'\t' read -r index module declaration kind parent is_prop direct_sorry transitive_sorry uses_graph uses_fintype uses_finset; do
  type_oid=$(git -C "$PROJECT_ROOT" hash-object "$TMP/types/$index")
  declaration_oid=$(git -C "$PROJECT_ROOT" hash-object "$TMP/declarations/$index")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$module" "$declaration" "$kind" "$parent" "$is_prop" "$direct_sorry" \
    "$transitive_sorry" "$uses_graph" "$uses_fintype" "$uses_finset" \
    "$type_oid" "$declaration_oid" >> "$TMP/actual-vocabulary.tsv"
done < "$TMP/declaration-index.tsv"

if [[ "$MODE" == dump ]]; then
  printf '%s\n' $'module\tdeclaration\tdeclaration_kind\tparent_declaration\ttype_oid\tdeclaration_oid\tis_prop\tdirect_sorry\ttransitive_sorry\tuses_simple_graph\tuses_fintype\tuses_finset'
  LC_ALL=C sort -t $'\t' -k1,1 -k2,2 "$TMP/actual-vocabulary.tsv" |
    awk -F '\t' 'BEGIN { OFS="\t" } { print $1, $2, $3, $4, $11, $12, $5, $6, $7, $8, $9, $10 }'
  exit 0
fi

awk -F '\t' '
  NR == FNR {
    if (FNR > 1) { idByDecl[$2]=$1; origin[$2]=$5; parentId[$2]=$6; role[$2]=$9; finite[$2]=$10 }
    next
  }
  {
    decl=$2; actualParent=$4
    if (!(decl in idByDecl)) { print "unregistered declaration: " decl > "/dev/stderr"; bad=1; next }
    if ($3 == "theorem" || $3 == "axiom" || $3 == "opaque" || $3 == "quotient") {
      print "forbidden primary declaration kind: " decl " (" $3 ")" > "/dev/stderr"; bad=1
    }
    if ($5 == "true") { print "Prop-valued vocabulary declaration: " decl > "/dev/stderr"; bad=1 }
    if ($6 == "true") { print "direct sorryAx dependency: " decl > "/dev/stderr"; bad=1 }
    if ($7 == "true") { print "transitive sorryAx dependency: " decl > "/dev/stderr"; bad=1 }
    if (role[decl] == "graph_core" && $8 != "true") { print "graph_core declaration does not mention SimpleGraph: " decl > "/dev/stderr"; bad=1 }
    if (finite[decl] == "none" && $9 == "true") { print "global vocabulary declaration requires Fintype: " decl > "/dev/stderr"; bad=1 }
    if (finite[decl] == "local_operation" && $9 != "true") { print "local_operation declaration lacks Fintype: " decl > "/dev/stderr"; bad=1 }
    if (finite[decl] == "explicit_finite_volume" && ($9 == "true" || $10 != "true")) { print "explicit_finite_volume declaration is not explicit Finset data: " decl > "/dev/stderr"; bad=1 }
    if (actualParent == "NONE") {
      if (origin[decl] != "primary" || parentId[decl] != "NONE") {
        print "unsubstantiated generated origin/parent: " decl > "/dev/stderr"; bad=1
      }
    } else {
      expectedParent=idByDecl[actualParent]
      if (expectedParent == "" || origin[decl] != "generated" || parentId[decl] != expectedParent || role[decl] != "generated" || finite[decl] != "inherited") {
        print "generated declaration parent metadata mismatch: " decl > "/dev/stderr"; bad=1
      }
    }
  }
  END { exit bad }
' "$VOCAB" "$TMP/actual-vocabulary.tsv" || fail "semantic declaration policy failed"

awk -F '\t' 'NR > 1 {
  if ($4 == "notation") { print "notation has no ConstantInfo and cannot be a vocabulary declaration: " $2 > "/dev/stderr"; bad=1 }
  print $2 "\t" $3 "\t" $4 "\t" $7 "\t" $8
} END { exit bad }' "$VOCAB" | LC_ALL=C sort > "$TMP/expected-declarations.tsv" ||
  fail "registry contains a semantically unverifiable declaration kind"
awk -F '\t' 'BEGIN { OFS="\t" } { print $2, $1, $3, $11, $12 }' "$TMP/actual-vocabulary.tsv" |
  LC_ALL=C sort > "$TMP/actual-declarations.tsv"
if ! cmp -s "$TMP/expected-declarations.tsv" "$TMP/actual-declarations.tsv"; then
  diff -u "$TMP/expected-declarations.tsv" "$TMP/actual-declarations.tsv" >&2 || true
  fail "declaration/module/kind/type_oid/declaration_oid registry does not exactly match the environment"
fi

awk -F '\t' 'NR > 1 && index($3, "LatticeSystem.") != 1 && $3 != "LatticeSystem" && $3 !~ /^Mathlib(\.|$)/ { print "unauthorized production import: " $3 > "/dev/stderr"; bad=1 } END { exit bad }' "$IMPORTS" ||
  fail "production imports must target registered project modules or Mathlib"

awk -F '\t' 'NR > 1 { print $1 "\t" $2 "\t" $3 "\t" $4 "\t" $5 "\t" $6 }' "$IMPORTS" |
  LC_ALL=C sort > "$TMP/expected-imports.tsv"
awk -F '\t' '$1 == "I" && $4 != "Init" { pos[$2]++; print $2 "\t" pos[$2] "\t" $4 "\t" $5 "\t" $6 "\t" $7 }' "$TMP/environment.tsv" |
  LC_ALL=C sort > "$TMP/actual-imports.tsv"
if ! cmp -s "$TMP/expected-imports.tsv" "$TMP/actual-imports.tsv"; then
  diff -u "$TMP/expected-imports.tsv" "$TMP/actual-imports.tsv" >&2 || true
  fail "direct imports are missing, reordered, drifted, or unauthorized"
fi

awk -F '\t' '
  NR == FNR { if (FNR > 1) { modules[$1]=1; roles[$1]=$3 } next }
  FNR > 1 && ($1 in modules) && ($3 in modules) { reach[$1 SUBSEP $3]=1 }
  END {
    for (m in modules) reach[m SUBSEP m]=1
    for (k in modules) for (i in modules) for (j in modules)
      if (reach[i SUBSEP k] && reach[k SUBSEP j]) reach[i SUBSEP j]=1
    umbrellas=0; roots=0
    for (u in modules) if (roles[u] == "umbrella") {
      umbrellas++
      for (m in modules) if (roles[m] == "leaf" && !reach[u SUBSEP m]) {
        print "umbrella cannot reach leaf: " u " -> " m > "/dev/stderr"; bad=1
      }
    }
    for (r in modules) if (roles[r] == "root") {
      roots++
      for (m in modules) if (!reach[r SUBSEP m]) {
        print "root cannot reach registered module: " r " -> " m > "/dev/stderr"; bad=1
      }
    }
    if (umbrellas == 0) { print "no umbrella module registered" > "/dev/stderr"; bad=1 }
    exit bad
  }
' "$MODULES" "$IMPORTS" || fail "registered umbrella reachability failed"

echo "check-vocabulary: ok"
