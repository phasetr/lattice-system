#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
fail() { echo "check-policy: $*" >&2; exit 1; }

source_root="$ROOT/LatticeSystem.lean"
[[ -f "$source_root" ]] || fail "missing LatticeSystem.lean"

CANONICAL_ROOT_OID=f94581f054ad1f1a0b343257b72d1e81c2d786c9
VOCABULARY_ROOT_OID=3936875b61b943e3a28c70410b049d6be2d431c5
{ IFS= read -r _; IFS= read -r phase; } < "$ROOT/registry/phase.tsv"
VOCABULARY_STAGING=0
case "$phase" in
  bootstrap)
    [[ $(git hash-object "$source_root") == "$CANONICAL_ROOT_OID" ]] || fail "declaration-free production root differs from canonical doc-only content"
    [[ ! -d "$ROOT/LatticeSystem" ]] || fail "$phase phase must not contain a production source directory"
    ;;
  census)
    if [[ -f "$ROOT/registry/modules.tsv" && $(awk 'END { print NR }' "$ROOT/registry/modules.tsv") -gt 1 ]]; then
      VOCABULARY_STAGING=1
      [[ $(git hash-object "$source_root") == "$VOCABULARY_ROOT_OID" ]] || fail "staged vocabulary root differs from canonical registered umbrella import"
    else
      [[ $(git hash-object "$source_root") == "$CANONICAL_ROOT_OID" ]] || fail "declaration-free production root differs from canonical doc-only content"
      [[ ! -d "$ROOT/LatticeSystem" ]] || fail "declaration-free census must not contain a production source directory"
    fi
    ;;
  vocabulary)
    [[ $(git hash-object "$source_root") == "$VOCABULARY_ROOT_OID" ]] || fail "vocabulary root differs from canonical registered umbrella import"
    ;;
  skeleton)
    [[ $(git hash-object "$source_root") == "$VOCABULARY_ROOT_OID" ]] || fail "skeleton root differs from canonical registered umbrella import"
    [[ -f "$ROOT/registry/statement-modules.tsv" ]] || fail "missing registry/statement-modules.tsv"
    [[ $(awk 'END { print NR }' "$ROOT/registry/statement-modules.tsv") -gt 1 ]] ||
      fail "skeleton phase requires registered statement modules"
    ;;
  proof) fail "production policy is not implemented for $phase" ;;
  *) fail "unknown phase: $phase" ;;
esac

# Registered statement modules carry registered axioms, claim theorems, and
# proof stubs by construction, so only those tokens are exempt there; `admit`
# and `native_decide` stay forbidden everywhere. Every other tracked production
# source stays under the full token ban, and a path claimed by both registries
# gets no exemption at all.
if [[ "$phase" == vocabulary || "$phase" == skeleton || "$VOCABULARY_STAGING" -eq 1 ]]; then
  statement_paths=$ROOT/registry/statement-modules.tsv
  [[ -f "$statement_paths" ]] || statement_paths=/dev/null
  vocabulary_paths=$ROOT/registry/modules.tsv
  [[ -f "$vocabulary_paths" ]] || vocabulary_paths=/dev/null
  while IFS= read -r lean_file; do
    [[ -z "$lean_file" ]] && continue
    statement=0 vocabulary=0
    awk -F '\t' -v path="$lean_file" 'FNR > 1 && $2 == path { found=1 } END { exit !found }' "$statement_paths" && statement=1
    awk -F '\t' -v path="$lean_file" 'FNR > 1 && $2 == path { found=1 } END { exit !found }' "$vocabulary_paths" && vocabulary=1
    [[ $statement -eq 1 && $vocabulary -eq 1 ]] &&
      fail "source path is registered as both a vocabulary and a statement module: $lean_file"
    if [[ $statement -eq 1 ]]; then
      tokens='admit|native_decide'
    else
      tokens='axiom|theorem|lemma|sorry|admit|native_decide'
    fi
    if LC_ALL=C awk -v tokens="$tokens" \
      '$0 ~ "(^|[[:space:]])(" tokens ")([[:space:]]|$)" { found=1 } END { exit !found }' "$ROOT/$lean_file"; then
      fail "vocabulary lexical hygiene found a forbidden token (nonsemantic check): $lean_file"
    fi
  done < <(git -C "$ROOT" ls-files 'LatticeSystem.lean' 'LatticeSystem/*.lean' 'LatticeSystem/**/*.lean')
fi

for file in README.md DESIGN.md .github/pull_request_template.md; do
  [[ -f "$ROOT/$file" ]] || fail "missing $file"
  awk 'index($0, "exact PR") { found=1 } END { exit !found }' "$ROOT/$file" || fail "$file omits exact PR merge gate"
  awk 'index($0, "exact head SHA") { found=1 } END { exit !found }' "$ROOT/$file" || fail "$file omits exact head SHA merge gate"
done

if awk 'index($0, "- [x] USER ONLY") || index($0, "- [X] USER ONLY") { found=1 } END { exit !found }' "$ROOT/.github/pull_request_template.md"; then
  fail "USER ONLY gate is checked"
fi
awk 'index($0, "- [ ] USER ONLY") { found=1 } END { exit !found }' "$ROOT/.github/pull_request_template.md" || fail "template lacks unchecked USER ONLY gate"

echo "check-policy: ok"
