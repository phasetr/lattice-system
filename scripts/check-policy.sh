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
  skeleton|proof) fail "production policy is not implemented for $phase" ;;
  *) fail "unknown phase: $phase" ;;
esac

if [[ "$phase" == vocabulary || "$VOCABULARY_STAGING" -eq 1 ]]; then
  while IFS= read -r lean_file; do
    [[ -z "$lean_file" ]] && continue
    if LC_ALL=C awk '/(^|[[:space:]])(axiom|theorem|lemma|sorry|admit|native_decide)([[:space:]]|$)/ { found=1 } END { exit !found }' "$ROOT/$lean_file"; then
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
