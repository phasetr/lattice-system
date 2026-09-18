#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd)
CHECK_BASE_DIFF=${CHECK_BASE_DIFF:-"$PROJECT_ROOT/scripts/check-base-diff.sh"}
fail() { echo "check-base-diff-ci: $*" >&2; exit 1; }

[[ $# -eq 1 || $# -eq 2 ]] || fail "usage: check-base-diff-ci.sh ROOT [BASE_REF]"
ROOT=$(cd -P "$1" && pwd -P) || fail "invalid repository root"
GIT_ROOT=$(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) ||
  fail "ROOT must be the repository top"
GIT_ROOT=$(cd -P "$GIT_ROOT" && pwd -P) || fail "invalid Git root"
[[ "$GIT_ROOT" == "$ROOT" ]] ||
  fail "ROOT must be the repository top"
BASE_REF=${2:-HEAD^}
BASE_TIP=$(git -C "$ROOT" rev-parse --verify "$BASE_REF^{commit}" 2>/dev/null) ||
  fail "invalid or unfetched base ref: $BASE_REF"
MERGE_BASE=$(git -C "$ROOT" merge-base HEAD "$BASE_TIP" 2>/dev/null) ||
  fail "base ref has no merge base"

EVENTS=$ROOT/registry/correction-events.tsv
if [[ ! -f "$EVENTS" ]]; then
  "$CHECK_BASE_DIFF" "$ROOT" "$BASE_REF"
  exit 0
fi
[[ $(head -n 1 "$EVENTS") == $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' ]] ||
  fail "bad correction-events.tsv header"

TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-base-diff-ci.XXXXXX")
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
BASE_EVENTS=$TMP/base-events.tsv
if git -C "$ROOT" cat-file -e "$MERGE_BASE:registry/correction-events.tsv" 2>/dev/null; then
  git -C "$ROOT" show "$MERGE_BASE:registry/correction-events.tsv" > "$BASE_EVENTS"
else
  printf '%s\n' $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' > "$BASE_EVENTS"
fi

NEW_EVENTS=$TMP/new-events.tsv
awk -F '\t' '
  NR==FNR { if (FNR>1) old[$1]=1; next }
  FNR>1 && !($1 in old) { print $1 "\t" $4 }
' "$BASE_EVENTS" "$EVENTS" > "$NEW_EVENTS"
NEW_COUNT=$(awk 'END {print NR+0}' "$NEW_EVENTS")
if [[ "$NEW_COUNT" -eq 0 ]]; then
  "$CHECK_BASE_DIFF" "$ROOT" "$BASE_REF"
  exit 0
fi
[[ "$NEW_COUNT" -eq 1 ]] || fail "multiple new correction events require an explicit CI policy change"

IFS=$'\t' read -r EVENT_ID RECORDED_BASE < "$NEW_EVENTS"
[[ -n "$EVENT_ID" && "$RECORDED_BASE" == "$MERGE_BASE" ]] ||
  fail "new correction event base commit does not match the actual merge base"
"$CHECK_BASE_DIFF" --correction-event "$EVENT_ID" "$ROOT" "$BASE_REF"

echo "check-base-diff-ci: ok"
