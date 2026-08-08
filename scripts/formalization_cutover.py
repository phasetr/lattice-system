#!/usr/bin/env python3
"""Shared, dependency-free formalization-status cutover baseline checks."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any, Iterable


BASELINE_COMMIT = "6519099024bf156b87ac0c807c6633c513792581"
BASELINE_PATH = "docs/index.md"
BASELINE_FIRST_LINE = 217
BASELINE_LAST_LINE = 2731
BASELINE_ROW_COUNT = 2052
CUTOVER_BASELINE_KEYS = {
    "baseline_commit",
    "baseline_path",
    "cutover_record_ids",
    "legacy_rows",
    "non_legacy_record_ids",
    "schema_version",
}
LEGACY_ROW_KEYS = {
    "disposition",
    "legacy_declaration_refs",
    "legacy_first_cell",
    "legacy_grouping_syntax",
    "legacy_plain_text",
    "legacy_source_line",
    "mapped_record_ids",
    "ordinal",
    "outcome",
    "row_sha256",
}
OUTCOMES = {"mapped", "not_a_declaration", "retired"}
DISPOSITIONS = {"non_declaration", "retired_declarations"}
CUTOVER_CERTIFICATE_KEYS = {
    "baseline_sha256",
    "cutover_record_ids_sha256",
    "exceptional_mappings",
    "legacy_mapping_sha256",
    "non_record_ordinals",
    "retired_declarations",
    "schema_version",
}
CUTOVER_EXCEPTIONAL_MAPPING_KEYS = {
    "expected_lean_names",
    "ordinal",
    "row_sha256",
}
CUTOVER_RETIRED_DECLARATION_REQUIRED_KEYS = {
    "deletion_commit",
    "former_lean_name",
    "former_path",
    "legacy_leaf",
    "ordinal",
    "reason",
    "row_sha256",
}
CUTOVER_RETIRED_DECLARATION_KEYS = (
    CUTOVER_RETIRED_DECLARATION_REQUIRED_KEYS | {"replacement_record_ids"}
)
# PR E must replace this with the SHA-256 of the independently audited canonical
# certificate in the same atomic change that flips the catalogue authority.
ACCEPTED_CUTOVER_CERTIFICATE_SHA256: str | None = None
PROTOTYPE_RECORD_IDS = {
    "shastry-1992-staggered-susceptibility-bound",
    "tasaki-2020-section-2-1-pauli-x-involutive",
    "tasaki-2020-theorem-3-1-finite-dimensional-core",
    "tasaki-2020-theorem-4-2-shastry-no-ssb",
}
PINNED_EXCEPTIONAL_EXPECTED_NAMES = {
    # One cyclic triple, not a 3 × 3 Cartesian product.
    20: (
        "LatticeSystem.Quantum.spinHalfRot1_pi_anticomm_spinHalfRot2_pi",
        "LatticeSystem.Quantum.spinHalfRot2_pi_anticomm_spinHalfRot3_pi",
        "LatticeSystem.Quantum.spinHalfRot3_pi_anticomm_spinHalfRot1_pi",
    ),
    # Two paired ladder/base-state declarations, not a 2 × 2 product.
    432: (
        "LatticeSystem.Quantum.totalSpinHalfOpMinus_pow_basisVec_all_up_mem_magnetizationSubspace",
        "LatticeSystem.Quantum.totalSpinHalfOpPlus_pow_basisVec_all_down_mem_magnetizationSubspace",
    ),
    # This row is explicitly audited as the four-member Cartesian product.
    471: (
        "LatticeSystem.Quantum.neelSquareState_inner_szsz_horizontal_adjacent_eq_neg_one_quarter",
        "LatticeSystem.Quantum.neelSquareState_inner_szsz_horizontal_wrap_eq_neg_one_quarter",
        "LatticeSystem.Quantum.neelSquareState_inner_szsz_vertical_adjacent_eq_neg_one_quarter",
        "LatticeSystem.Quantum.neelSquareState_inner_szsz_vertical_wrap_eq_neg_one_quarter",
    ),
    1237: (
        "LatticeSystem.Quantum.onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_mulVec_mem_magSubspaceS",
        "LatticeSystem.Quantum.onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_mulVec_mem_magSubspaceS",
        "LatticeSystem.Quantum.onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_mulVec_mem_magSubspaceS",
        "LatticeSystem.Quantum.onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_mulVec_mem_magSubspaceS",
        "LatticeSystem.Quantum.totalSpinSOp3_mul_onSiteS_spinSOpMinus",
        "LatticeSystem.Quantum.totalSpinSOp3_mul_onSiteS_spinSOpPlus",
    ),
    1239: (
        "LatticeSystem.Quantum.onSiteS_mul_onSiteS_apply_im_zero_of_real",
        "LatticeSystem.Quantum.onSiteS_mul_onSiteS_apply_re_nonneg_of_real_nonneg",
        "LatticeSystem.Quantum.onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg",
        "LatticeSystem.Quantum.onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg",
        "LatticeSystem.Quantum.onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_im_zero_re_nonneg",
        "LatticeSystem.Quantum.onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_apply_im_zero_re_nonneg",
    ),
    1269: (
        "LatticeSystem.Quantum.dressedAxisSwapped_bond_re_neg_bipartite_x_of_raiseLower_witness",
        "LatticeSystem.Quantum.dressedAxisSwapped_bond_re_neg_bipartite_y_of_raiseLower_witness",
    ),
    # Five zipped spin-S/spin-half declarations, not a 5 × 5 product.
    1592: (
        "LatticeSystem.Quantum.spinSOp1_one_eq_spinHalfOp1",
        "LatticeSystem.Quantum.spinSOp2_one_eq_spinHalfOp2",
        "LatticeSystem.Quantum.spinSOp3_one_eq_spinHalfOp3",
        "LatticeSystem.Quantum.spinSOpMinus_one_eq_spinHalfOpMinus",
        "LatticeSystem.Quantum.spinSOpPlus_one_eq_spinHalfOpPlus",
    ),
    1905: (
        "LatticeSystem.Fermion.hubbardOnSiteInteractionSiteReflectionCoeffAction",
        "LatticeSystem.Fermion.hubbardOnSiteInteractionSiteReflectionCoeffWeight",
        "LatticeSystem.Fermion.spinReflectionCoeff_attractiveHubbardInteraction",
        "LatticeSystem.Fermion.spinReflectionCoeff_hubbardOnSiteInteractionSite",
    ),
    1907: (
        "LatticeSystem.Fermion.hubbardBlock_betweenSum_down",
        "LatticeSystem.Fermion.hubbardBlock_betweenSum_up",
        "LatticeSystem.Fermion.hubbardBlock_downHop_jwSign_backward",
        "LatticeSystem.Fermion.hubbardBlock_downHop_jwSign_forward",
        "LatticeSystem.Fermion.hubbardBlock_upHop_jwSign_backward",
        "LatticeSystem.Fermion.hubbardBlock_upHop_jwSign_forward",
    ),
}
SHA256_RE = re.compile(r"[0-9a-f]{64}")
GIT_COMMIT_RE = re.compile(r"[0-9a-f]{40}")
STABLE_ID_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
LEAN_NAME_RE = re.compile(
    r"LatticeSystem(?:\.[A-Za-z_\u0080-\uFFFF][A-Za-z0-9_'\u0080-\uFFFF]*)+"
)
LEAN_DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:abbrev|axiom|class|def|inductive|instance|lemma|opaque|structure|theorem)\s+"
    r"([A-Za-z_\u0080-\uFFFF][A-Za-z0-9_'\u0080-\uFFFF]*)"
)
RETIRED_FIXTURES = {
    656: {
        "deletion_commit": "7b65d59ec539b195d449bd97f94b08dbf99bf66e",
        "former_lean_name": (
            "LatticeSystem.Quantum."
            "sublatticeSpinHalfOpComplementMinus_complement_plus_mulVec_neelStateOf"
        ),
        "former_path": (
            "LatticeSystem/Quantum/MarshallLiebMattis/"
            "SublatticeCasimirNeelExpectations.lean"
        ),
        "legacy_leaf": (
            "sublatticeSpinHalfOpComplementMinus_complement_plus_mulVec_neelStateOf"
        ),
        "reason": "Deleted with the bulk orphan-module removal in PR #3919.",
    },
    676: {
        "deletion_commit": "7b65d59ec539b195d449bd97f94b08dbf99bf66e",
        "former_lean_name": "LatticeSystem.Quantum.neelStateOf_allUp_orthogonal",
        "former_path": (
            "LatticeSystem/Quantum/MarshallLiebMattis/"
            "SublatticeCasimirNeelBasisOrthogonality.lean"
        ),
        "legacy_leaf": "neelStateOf_allUp_orthogonal",
        "reason": "Deleted with the bulk orphan-module removal in PR #3919.",
    },
}
_CURRENT_DECLARATION_LEAVES_CACHE: dict[Path, set[str]] = {}
_RETIREMENT_HISTORY_CACHE: dict[tuple[Path, str, str, str, str], str | None] = {}


def _is_separator(line: str) -> bool:
    return line.startswith("|") and set(line.strip()) <= set("|-: ")


def reconstruct_legacy_rows(repo_root: Path) -> list[dict[str, Any]]:
    """Reconstruct the exact 2,052 legacy rows from the pinned source commit."""
    text = subprocess.run(
        ["git", "show", f"{BASELINE_COMMIT}:{BASELINE_PATH}"],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    lines = text.splitlines()
    rows: list[dict[str, Any]] = []
    for source_line in range(BASELINE_FIRST_LINE, BASELINE_LAST_LINE + 1):
        line = lines[source_line - 1]
        if not line.startswith("|") or _is_separator(line):
            continue
        if source_line < len(lines) and _is_separator(lines[source_line]):
            continue
        first_cell = line.removeprefix("| ").split(" | ", 1)[0]
        references = re.findall(r"`([^`]+)`", first_cell)
        plain_text = re.sub(r"`[^`]*`", "", first_cell).strip()
        grouping_syntax: list[str] = []
        if any("{" in ref or "}" in ref for ref in references):
            grouping_syntax.append("brace")
        if any("/" in ref for ref in references):
            grouping_syntax.append("slash")
        if any("*" in ref for ref in references):
            grouping_syntax.append("wildcard")
        if re.search(r"\betc\.", plain_text, flags=re.IGNORECASE):
            grouping_syntax.append("plain_etc")
        if len(references) > 1 or "," in plain_text:
            grouping_syntax.append("multiple")
        if any(ref.startswith("_") or "..." in ref or "…" in ref for ref in references):
            grouping_syntax.append("abbreviated")
        if any(any(character.isspace() for character in ref) for ref in references):
            grouping_syntax.append("signature")
        rows.append(
            {
                "legacy_declaration_refs": references,
                "legacy_first_cell": first_cell,
                "legacy_grouping_syntax": sorted(grouping_syntax),
                "legacy_plain_text": plain_text,
                "legacy_source_line": source_line,
                "ordinal": len(rows) + 1,
                "row_sha256": hashlib.sha256(line.encode("utf-8")).hexdigest(),
            }
        )
    if len(rows) != BASELINE_ROW_COUNT:
        raise ValueError(
            f"pinned legacy reconstruction produced {len(rows)} rows, "
            f"expected {BASELINE_ROW_COUNT}"
        )
    return rows


def canonical_bytes(value: Any) -> bytes:
    """Serialize certificate inputs with the canonical JSON byte contract."""
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    """Return the lowercase SHA-256 of exact bytes."""
    return hashlib.sha256(raw).hexdigest()


def _legacy_ref_matches_leaf(reference: str, leaf: str) -> bool:
    """Match an exact leaf or the audited slash shorthand used by legacy rows."""
    reference_leaf = reference.rsplit(".", 1)[-1]
    if reference_leaf == leaf:
        return True
    if "/" not in reference_leaf:
        return False
    alternatives = reference_leaf.split("/")
    first = re.fullmatch(r"(.*)([A-Z0-9])", alternatives[0])
    last = re.fullmatch(r"([A-Z0-9])(.*)", alternatives[-1])
    if first is None or last is None:
        return False
    prefix, first_choice = first.groups()
    last_choice, suffix = last.groups()
    choices = [first_choice, *alternatives[1:-1], last_choice]
    return leaf in {prefix + choice + suffix for choice in choices}


def _expand_braces(value: str) -> list[str] | None:
    """Expand deterministic comma-separated brace products in one legacy name."""
    match = re.search(r"\{([^{}]+)\}", value)
    if match is None:
        return [value]
    choices = match.group(1).split(",")
    if not choices or any(not re.fullmatch(r"[A-Za-z0-9_']+", item) for item in choices):
        return None
    expanded: list[str] = []
    for choice in choices:
        children = _expand_braces(value[: match.start()] + choice + value[match.end() :])
        if children is None:
            return None
        expanded.extend(children)
    return expanded


def _expand_slash(value: str) -> list[str] | None:
    """Expand deterministic camel-case or numeric slash products."""
    if "/" not in value:
        return [value]
    match = re.fullmatch(
        r"([^/]*)([A-Z][a-z0-9']*|[0-9]+)"
        r"((?:/(?:[A-Z][a-z0-9']*|[0-9]+))+)(.*)",
        value,
    )
    if match is None:
        return None
    prefix, first_choice, alternatives, suffix = match.groups()
    choices = [first_choice, *alternatives.removeprefix("/").split("/")]
    result: list[str] = []
    for choice in choices:
        children = _expand_slash(prefix + choice + suffix)
        if children is None:
            return None
        result.extend(children)
    return result


def _slash_group_count(value: str) -> int | None:
    """Count deterministic slash groups without choosing cross-group semantics."""
    count = 0
    remaining = value
    while "/" in remaining:
        match = re.fullmatch(
            r"([^/]*)([A-Z][a-z0-9']*|[0-9]+)"
            r"((?:/(?:[A-Z][a-z0-9']*|[0-9]+))+)(.*)",
            remaining,
        )
        if match is None:
            return None
        count += 1
        remaining = match.group(4)
    return count


def _is_lean_identifier_leaf(value: str) -> bool:
    """Recognize one nonempty Lean-like identifier, excluding prose notation."""
    return bool(value) and value.replace("'", "").isidentifier()


def expand_legacy_leaves(row: dict[str, Any]) -> set[str] | None:
    """Expand mechanically complete legacy references, or require a certificate."""
    syntax = set(row.get("legacy_grouping_syntax", []))
    if syntax & {"abbreviated", "plain_etc", "wildcard"}:
        return None
    result: set[str] = set()
    for raw_reference in row.get("legacy_declaration_refs", []):
        if not raw_reference or any(character.isspace() for character in raw_reference):
            return None
        reference_token = raw_reference
        if reference_token.endswith(".lean") or re.match(r"[0-9]", reference_token):
            return None
        reference = reference_token.rsplit(".", 1)[-1]
        slash_groups = _slash_group_count(reference)
        if (
            reference.count("{") != reference.count("}")
            or slash_groups is None
            or reference.count("{") + slash_groups > 1
        ):
            return None
        brace_expanded = _expand_braces(reference)
        if brace_expanded is None:
            return None
        for expanded in brace_expanded:
            slash_expanded = _expand_slash(expanded)
            if slash_expanded is None:
                return None
            if any(not _is_lean_identifier_leaf(leaf) for leaf in slash_expanded):
                return None
            result.update(slash_expanded)
    return result if result else None


def certificate_projection(baseline: dict[str, Any]) -> tuple[list[str], list[dict[str, Any]]]:
    """Return the immutable ID and row-mapping projections covered by a certificate."""
    cutover_ids = baseline.get("cutover_record_ids", [])
    mappings = [
        {
            "disposition": row.get("disposition"),
            "mapped_record_ids": row.get("mapped_record_ids"),
            "ordinal": row.get("ordinal"),
            "outcome": row.get("outcome"),
            "row_sha256": row.get("row_sha256"),
        }
        for row in baseline.get("legacy_rows", [])
        if isinstance(row, dict)
    ]
    return cutover_ids, mappings


def _sorted_unique_strings(value: Any) -> bool:
    return (
        isinstance(value, list)
        and all(isinstance(item, str) for item in value)
        and value == sorted(set(value))
    )


def validate_cutover_baseline(
    baseline: Any,
    records: Iterable[dict[str, Any]],
    expected_rows: list[dict[str, Any]],
    allowed_non_record_ordinals: set[int] | None = None,
    exceptional_mappings: dict[int, dict[str, Any]] | None = None,
    retired_declarations: dict[int, list[dict[str, Any]]] | None = None,
) -> list[str]:
    """Validate exhaustive historical coverage and irreversible cutover IDs."""
    errors: list[str] = []
    allowed_non_record_ordinals = allowed_non_record_ordinals or set()
    exceptional_mappings = exceptional_mappings or {}
    retired_declarations = retired_declarations or {}
    record_map = {
        record.get("id"): record
        for record in records
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    }
    current_record_names = {
        record.get("lean_name")
        for record in record_map.values()
        if isinstance(record.get("lean_name"), str)
    }
    current_record_leaves = {
        name.rsplit(".", 1)[-1] for name in current_record_names
    }
    if not isinstance(baseline, dict):
        return ["cutover baseline: expected object"]
    if set(baseline) != CUTOVER_BASELINE_KEYS:
        errors.append("cutover baseline: field contract differs")
    if baseline.get("schema_version") != 1:
        errors.append("cutover baseline: bad schema version")
    if baseline.get("baseline_commit") != BASELINE_COMMIT:
        errors.append("cutover baseline: baseline commit is not pinned")
    if baseline.get("baseline_path") != BASELINE_PATH:
        errors.append("cutover baseline: baseline path differs")
    cutover_ids = baseline.get("cutover_record_ids")
    non_legacy_ids = baseline.get("non_legacy_record_ids")
    if not _sorted_unique_strings(cutover_ids):
        errors.append("cutover baseline: cutover_record_ids must be sorted and unique")
        cutover_ids = []
    if not _sorted_unique_strings(non_legacy_ids):
        errors.append("cutover baseline: non_legacy_record_ids must be sorted and unique")
        non_legacy_ids = []
    for name, values in (
        ("cutover_record_ids", cutover_ids),
        ("non_legacy_record_ids", non_legacy_ids),
    ):
        if any(STABLE_ID_RE.fullmatch(item) is None for item in values):
            errors.append(f"cutover baseline: {name} contains an invalid record ID")
    rows = baseline.get("legacy_rows")
    if not isinstance(rows, list) or len(rows) != len(expected_rows):
        errors.append(
            f"cutover baseline: expected {len(expected_rows)} legacy rows, "
            f"found {len(rows) if isinstance(rows, list) else 'non-array'}"
        )
        rows = []
    mapped_ids: list[str] = []
    actual_non_record_ordinals: set[int] = set()
    needed_exceptional_ordinals: set[int] = set()
    for index, (row, expected) in enumerate(zip(rows, expected_rows), 1):
        location = f"cutover baseline row {index}"
        if not isinstance(row, dict):
            errors.append(f"{location}: expected object")
            continue
        if set(row) != LEGACY_ROW_KEYS:
            errors.append(f"{location}: field contract differs")
        for field in (
            "legacy_declaration_refs",
            "legacy_first_cell",
            "legacy_grouping_syntax",
            "legacy_plain_text",
            "ordinal",
            "legacy_source_line",
            "row_sha256",
        ):
            if row.get(field) != expected[field]:
                errors.append(f"{location}: {field} differs from pinned legacy row")
        outcome = row.get("outcome")
        mapped = row.get("mapped_record_ids")
        disposition = row.get("disposition")
        retired_entries = retired_declarations.get(index, [])
        retired_leaves = {entry.get("legacy_leaf") for entry in retired_entries}
        retired_names = {entry.get("former_lean_name") for entry in retired_entries}
        if retired_names & current_record_names or retired_leaves & current_record_leaves:
            errors.append(f"{location}: retired declaration still has a current record")
        if any(entry.get("row_sha256") != row.get("row_sha256") for entry in retired_entries):
            errors.append(f"{location}: retired declaration evidence has the wrong row hash")
        if retired_entries and not row.get("legacy_declaration_refs"):
            errors.append(f"{location}: retirement evidence lacks a legacy declaration reference")
        if any(
            record_id not in record_map
            for entry in retired_entries
            for record_id in entry.get("replacement_record_ids", [])
        ):
            errors.append(f"{location}: retired declaration replacement record is missing")
        if outcome not in OUTCOMES:
            errors.append(f"{location}: invalid outcome")
        if not _sorted_unique_strings(mapped):
            errors.append(f"{location}: mapped_record_ids must be sorted and unique")
            mapped = []
        if any(STABLE_ID_RE.fullmatch(item) is None for item in mapped):
            errors.append(f"{location}: invalid mapped record ID")
        if outcome == "mapped":
            if not mapped:
                errors.append(f"{location}: mapped outcome requires at least one record ID")
            if disposition is not None:
                errors.append(f"{location}: mapped outcome requires a null disposition")
            mapped_names = {
                record_map.get(record_id, {}).get("lean_name") for record_id in mapped
            }
            mapped_names.discard(None)
            mapped_leaves = {
                name.rsplit(".", 1)[-1] for name in mapped_names if isinstance(name, str)
            }
            if mapped_leaves & retired_leaves or mapped_names & retired_names:
                errors.append(f"{location}: mapped and retired declarations overlap")
            mechanically_expected = expand_legacy_leaves(row)
            if mechanically_expected is not None:
                if mapped_leaves | retired_leaves != mechanically_expected:
                    errors.append(
                        f"{location}: mapped/retired leaves differ from the complete expanded legacy references"
                    )
            else:
                entry = exceptional_mappings.get(index)
                if not row.get("legacy_grouping_syntax") or entry is None:
                    errors.append(
                        f"{location}: non-expandable grouped mapping lacks exact certificate evidence"
                    )
                elif (
                    entry.get("row_sha256") != row.get("row_sha256")
                    or set(entry.get("expected_lean_names", []))
                    != mapped_names | retired_names
                ):
                    errors.append(
                        f"{location}: exceptional certificate names/hash differ from mapped records"
                    )
                else:
                    needed_exceptional_ordinals.add(index)
        elif outcome == "retired":
            if mapped:
                errors.append(f"{location}: retired outcome cannot map current records")
            if disposition != "retired_declarations":
                errors.append(f"{location}: retired outcome requires its closed disposition")
            mechanically_expected = expand_legacy_leaves(row)
            if mechanically_expected is not None:
                if retired_leaves != mechanically_expected:
                    errors.append(
                        f"{location}: pure-retired leaves differ from expanded legacy references"
                    )
            else:
                entry = exceptional_mappings.get(index)
                if entry is None or set(entry.get("expected_lean_names", [])) != retired_names:
                    errors.append(
                        f"{location}: pure-retired non-mechanical row lacks exact expected names"
                    )
                else:
                    needed_exceptional_ordinals.add(index)
        elif outcome == "not_a_declaration":
            if mapped:
                errors.append(f"{location}: not_a_declaration outcome cannot map records")
            if disposition not in DISPOSITIONS:
                errors.append(f"{location}: invalid closed non-record disposition")
            if index not in allowed_non_record_ordinals:
                errors.append(f"{location}: non-record outcome is absent from the certificate")
            if row.get("legacy_declaration_refs"):
                errors.append(f"{location}: a declaration-bearing row cannot be a non-record")
            actual_non_record_ordinals.add(index)
        if outcome == "not_a_declaration" and retired_entries:
            errors.append(f"{location}: non-record row cannot retire declarations")
        mapped_ids.extend(mapped)
    if actual_non_record_ordinals != allowed_non_record_ordinals:
        errors.append(
            "cutover baseline: certificate non-record ordinals differ from row outcomes"
        )
    if needed_exceptional_ordinals != set(exceptional_mappings):
        errors.append(
            "cutover baseline: certificate exceptional-mapping ordinals differ from required bindings"
        )
    used_retired_ordinals = {
        row.get("ordinal")
        for row in rows
        if isinstance(row, dict) and row.get("outcome") in {"mapped", "retired"}
    }
    if set(retired_declarations) - used_retired_ordinals:
        errors.append("cutover baseline: retired declaration evidence is unused")
    mapped_set = set(mapped_ids)
    non_legacy_set = set(non_legacy_ids)
    cutover_set = set(cutover_ids)
    if mapped_set & non_legacy_set:
        errors.append("cutover baseline: mapped and non-legacy record IDs overlap")
    missing_prototype_mappings = sorted(PROTOTYPE_RECORD_IDS - mapped_set)
    if missing_prototype_mappings:
        errors.append(
            "cutover baseline: original prototype records must map to legacy rows: "
            f"{missing_prototype_mappings}"
        )
    if mapped_set | non_legacy_set != cutover_set:
        errors.append("cutover baseline: mapped/non-legacy union differs from cutover_record_ids")
    current_ids = set(record_map)
    missing = sorted(cutover_set - current_ids)
    if missing:
        errors.append(f"cutover baseline: cutover records were deleted or are missing: {missing}")
    return errors


def _sorted_unique_ordinals(value: Any) -> bool:
    return (
        isinstance(value, list)
        and all(isinstance(item, int) and 1 <= item <= BASELINE_ROW_COUNT for item in value)
        and value == sorted(set(value))
    )


def exceptional_mapping_map(value: Any) -> tuple[dict[int, dict[str, Any]], list[str]]:
    """Validate and index exact certificate evidence for non-expandable groups."""
    errors: list[str] = []
    result: dict[int, dict[str, Any]] = {}
    if not isinstance(value, list):
        return {}, ["cutover certificate: exceptional_mappings must be an array"]
    ordinals: list[int] = []
    for index, entry in enumerate(value, 1):
        location = f"cutover certificate exceptional mapping {index}"
        if not isinstance(entry, dict) or set(entry) != CUTOVER_EXCEPTIONAL_MAPPING_KEYS:
            errors.append(f"{location}: field contract differs")
            continue
        ordinal = entry.get("ordinal")
        names = entry.get("expected_lean_names")
        if not isinstance(ordinal, int) or not 1 <= ordinal <= BASELINE_ROW_COUNT:
            errors.append(f"{location}: invalid ordinal")
            continue
        ordinals.append(ordinal)
        if (
            not _sorted_unique_strings(names)
            or not names
            or any(not name.startswith("LatticeSystem.") for name in names)
        ):
            errors.append(f"{location}: expected Lean names must be nonempty sorted exact names")
        if not isinstance(entry.get("row_sha256"), str) or SHA256_RE.fullmatch(
            entry["row_sha256"]
        ) is None:
            errors.append(f"{location}: invalid row SHA-256")
        result[ordinal] = entry
    if ordinals != sorted(set(ordinals)):
        errors.append("cutover certificate: exceptional mappings must be sorted unique ordinals")
    return result, errors


def _git_text(repo_root: Path, revision_path: str) -> str | None:
    """Return one historical Git blob as text, or none when it does not exist."""
    process = subprocess.run(
        ["git", "show", revision_path],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    return process.stdout if process.returncode == 0 else None


def _retirement_history_error(entry: dict[str, Any], repo_root: Path) -> str | None:
    """Prove that one exact former declaration disappeared in the named commit."""
    commit = entry["deletion_commit"]
    path = entry["former_path"]
    leaf = entry["legacy_leaf"]
    former_name = entry["former_lean_name"]
    cache_key = (repo_root.resolve(), commit, path, leaf, former_name)
    if cache_key in _RETIREMENT_HISTORY_CACHE:
        return _RETIREMENT_HISTORY_CACHE[cache_key]

    def finish(error: str | None) -> str | None:
        _RETIREMENT_HISTORY_CACHE[cache_key] = error
        return error

    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    if ancestor.returncode != 0:
        return finish("deletion commit is not an ancestor of HEAD")
    changed = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit, "--", path],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    if changed.returncode != 0 or path not in changed.stdout.splitlines():
        return finish("deletion commit does not change the former path")
    before = _git_text(repo_root, f"{commit}^:{path}")
    after = _git_text(repo_root, f"{commit}:{path}")
    if before is None or leaf not in set(LEAN_DECLARATION_RE.findall(before)):
        return finish("former path does not declare the legacy leaf before deletion")
    if former_name != leaf:
        namespaces = set(
            re.findall(
                r"(?m)^namespace\s+(LatticeSystem(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$",
                before,
            )
        )
        if not any(former_name == f"{namespace}.{leaf}" for namespace in namespaces):
            return finish("former fully qualified name disagrees with the historical namespace")
    if after is not None and leaf in set(LEAN_DECLARATION_RE.findall(after)):
        return finish("legacy leaf remains declared at the deletion commit")
    resolved_root = repo_root.resolve()
    current_leaves = _CURRENT_DECLARATION_LEAVES_CACHE.get(resolved_root)
    if current_leaves is None:
        current_leaves = set()
        for current_path in (repo_root / "LatticeSystem").rglob("*.lean"):
            current_leaves.update(
                LEAN_DECLARATION_RE.findall(current_path.read_text(encoding="utf-8"))
            )
        _CURRENT_DECLARATION_LEAVES_CACHE[resolved_root] = current_leaves
    if leaf in current_leaves:
        return finish("legacy leaf is still declared in the current Lean tree")
    return finish(None)


def retired_declaration_map(
    value: Any,
    repo_root: Path | None = None,
) -> tuple[dict[int, list[dict[str, Any]]], list[str]]:
    """Validate and index exact, history-proven retired declaration evidence."""
    errors: list[str] = []
    result: dict[int, list[dict[str, Any]]] = {}
    if not isinstance(value, list):
        return {}, ["cutover certificate: retired_declarations must be an array"]
    ordering: list[tuple[int, str]] = []
    for index, entry in enumerate(value, 1):
        location = f"cutover certificate retired declaration {index}"
        if (
            not isinstance(entry, dict)
            or not CUTOVER_RETIRED_DECLARATION_REQUIRED_KEYS <= set(entry)
            or not set(entry) <= CUTOVER_RETIRED_DECLARATION_KEYS
        ):
            errors.append(f"{location}: field contract differs")
            continue
        ordinal = entry.get("ordinal")
        leaf = entry.get("legacy_leaf")
        former_name = entry.get("former_lean_name")
        if not isinstance(ordinal, int) or not 1 <= ordinal <= BASELINE_ROW_COUNT:
            errors.append(f"{location}: invalid ordinal")
            continue
        if not isinstance(leaf, str) or not _is_lean_identifier_leaf(leaf):
            errors.append(f"{location}: invalid exact legacy leaf")
            continue
        ordering.append((ordinal, leaf))
        if (
            not isinstance(former_name, str)
            or not (
                former_name == leaf
                or (
                    LEAN_NAME_RE.fullmatch(former_name) is not None
                    and former_name.rsplit(".", 1)[-1] == leaf
                )
            )
        ):
            errors.append(f"{location}: former Lean name does not bind the legacy leaf")
        if not isinstance(entry.get("deletion_commit"), str) or GIT_COMMIT_RE.fullmatch(
            entry["deletion_commit"]
        ) is None:
            errors.append(f"{location}: invalid deletion commit")
        path = entry.get("former_path")
        if (
            not isinstance(path, str)
            or re.fullmatch(r"LatticeSystem/[A-Za-z0-9_./-]+\.lean", path) is None
            or ".." in Path(path).parts
        ):
            errors.append(f"{location}: invalid former Lean path")
        reason = entry.get("reason")
        if (
            not isinstance(reason, str)
            or not reason.strip()
            or any(ord(character) < 32 or 127 <= ord(character) <= 159 for character in reason)
        ):
            errors.append(f"{location}: retirement reason must be nonempty inline text")
        if not isinstance(entry.get("row_sha256"), str) or SHA256_RE.fullmatch(
            entry["row_sha256"]
        ) is None:
            errors.append(f"{location}: invalid row SHA-256")
        replacements = entry.get("replacement_record_ids", [])
        if not _sorted_unique_strings(replacements) or any(
            STABLE_ID_RE.fullmatch(record_id) is None for record_id in replacements
        ):
            errors.append(f"{location}: replacement record IDs must be sorted valid IDs")
        if repo_root is not None and not any(
            message.startswith(location) for message in errors
        ):
            history_error = _retirement_history_error(entry, repo_root)
            if history_error is not None:
                errors.append(f"{location}: {history_error}")
        result.setdefault(ordinal, []).append(entry)
    if ordering != sorted(set(ordering)):
        errors.append(
            "cutover certificate: retired declarations must be sorted unique ordinal/leaf pairs"
        )
    return result, errors


def validate_cutover_certificate(
    certificate: Any,
    certificate_raw: bytes,
    baseline: Any,
    baseline_raw: bytes,
    catalog_state: Any,
    records: Iterable[dict[str, Any]],
    repo_root: Path | None = None,
    accepted_certificate_sha256: str | None = ACCEPTED_CUTOVER_CERTIFICATE_SHA256,
) -> list[str]:
    """Bind one baseline and its immutable cutover projections to a certificate."""
    errors: list[str] = []
    if not isinstance(certificate, dict):
        return ["cutover certificate: expected object"]
    if set(certificate) != CUTOVER_CERTIFICATE_KEYS:
        errors.append("cutover certificate: field contract differs")
    if certificate.get("schema_version") != 1:
        errors.append("cutover certificate: bad schema version")
    if canonical_bytes(certificate) != certificate_raw:
        errors.append("cutover certificate: bytes are not canonical JSON")
    if not isinstance(baseline, dict) or canonical_bytes(baseline) != baseline_raw:
        errors.append("cutover certificate: baseline bytes are not canonical JSON")
        baseline = {}
    cutover_ids, mappings = certificate_projection(baseline)
    expected_hashes = {
        "baseline_sha256": sha256_bytes(baseline_raw),
        "cutover_record_ids_sha256": sha256_bytes(canonical_bytes(cutover_ids)),
        "legacy_mapping_sha256": sha256_bytes(canonical_bytes(mappings)),
    }
    for field, expected in expected_hashes.items():
        if certificate.get(field) != expected:
            errors.append(f"cutover certificate: {field} does not bind the baseline")
    exceptional_map, exceptional_errors = exceptional_mapping_map(
        certificate.get("exceptional_mappings")
    )
    errors.extend(exceptional_errors)
    _retired_map, retired_errors = retired_declaration_map(
        certificate.get("retired_declarations"), repo_root
    )
    errors.extend(retired_errors)
    if not _sorted_unique_ordinals(certificate.get("non_record_ordinals")):
        errors.append("cutover certificate: non_record_ordinals must be sorted unique ordinals")
    if set(exceptional_map) & set(certificate.get("non_record_ordinals", [])):
        errors.append("cutover certificate: exceptional mappings and non-record rows overlap")
    if set(_retired_map) & set(certificate.get("non_record_ordinals", [])):
        errors.append("cutover certificate: retired declarations and non-record rows overlap")
    current_ids = {
        record.get("id")
        for record in records
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    }
    cutover_set = set(cutover_ids) if isinstance(cutover_ids, list) else set()
    if catalog_state == "prototype" and current_ids != cutover_set:
        errors.append(
            "prototype cutover freeze requires current record IDs to equal cutover_record_ids"
        )
    if catalog_state == "authoritative" and not cutover_set <= current_ids:
        errors.append("authoritative catalogue deleted a certified cutover record")
    certificate_digest = sha256_bytes(certificate_raw)
    if catalog_state == "authoritative":
        if accepted_certificate_sha256 is None:
            errors.append("authoritative catalogue lacks a pinned accepted certificate digest")
        elif certificate_digest != accepted_certificate_sha256:
            errors.append("authoritative cutover certificate differs from the accepted fingerprint")
    return errors


def validate_cutover_requirement(
    catalog_state: Any, baseline_name: Any, certificate_name: Any = None
) -> list[str]:
    """Require paired fixed cutover evidence only when authority has been cut over."""
    errors: list[str] = []
    if baseline_name is not None and baseline_name != "cutover-baseline.json":
        errors.append("manifest cutover baseline path is not fixed")
    if certificate_name is not None and certificate_name != "cutover-certificate.json":
        errors.append("manifest cutover certificate path is not fixed")
    if (baseline_name is None) != (certificate_name is None):
        errors.append("manifest cutover baseline and certificate must be owned together")
    if catalog_state == "authoritative" and baseline_name is None:
        errors.append("authoritative catalogue requires cutover baseline and certificate")
    return errors


def self_test(repo_root: Path) -> list[str]:
    """Exercise positive and mutation fixtures without requiring a live baseline file."""
    import copy

    failures: list[str] = []
    rows = reconstruct_legacy_rows(repo_root)
    fixture_rows: list[dict[str, Any]] = []
    records: list[dict[str, Any]] = []
    record_by_name: dict[str, str] = {}
    non_record_ordinals: list[int] = []
    exceptional_entries: list[dict[str, Any]] = []
    for row in rows:
        expected_leaves = expand_legacy_leaves(row)
        expected_names: list[str]
        if expected_leaves is not None:
            expected_names = sorted(
                f"LatticeSystem.Fixture.{leaf}" for leaf in expected_leaves
            )
        elif row["legacy_grouping_syntax"]:
            pinned_names = PINNED_EXCEPTIONAL_EXPECTED_NAMES.get(row["ordinal"])
            if pinned_names is None:
                base = f"LatticeSystem.Fixture.exceptional_{row['ordinal']:04d}"
                expected_names = [base + "_a", base + "_b"]
            else:
                expected_names = list(pinned_names)
            exceptional_entries.append(
                {
                    "expected_lean_names": expected_names,
                    "ordinal": row["ordinal"],
                    "row_sha256": row["row_sha256"],
                }
            )
        else:
            expected_names = []
        if expected_names:
            mapped_ids: list[str] = []
            for lean_name in expected_names:
                record_id = record_by_name.get(lean_name)
                if record_id is None:
                    record_id = f"fixture-record-{len(records) + 1:04d}"
                    record_by_name[lean_name] = record_id
                    records.append({"id": record_id, "lean_name": lean_name})
                mapped_ids.append(record_id)
            fixture_rows.append(
                {
                    **row,
                    "disposition": None,
                    "mapped_record_ids": sorted(set(mapped_ids)),
                    "outcome": "mapped",
                }
            )
        else:
            fixture_rows.append(
                {
                    **row,
                    "disposition": "non_declaration",
                    "mapped_record_ids": [],
                    "outcome": "not_a_declaration",
                }
            )
            non_record_ordinals.append(row["ordinal"])
    prototype_names = {
        "shastry-1992-staggered-susceptibility-bound": "shastry_staggered_susceptibility_bound",
        "tasaki-2020-section-2-1-pauli-x-involutive": "pauliX_mul_self",
        "tasaki-2020-theorem-3-1-finite-dimensional-core": "horsch_vonderLinden_lowLying",
        "tasaki-2020-theorem-4-2-shastry-no-ssb": "shastry_no_symmetry_breaking_1d",
    }
    for record_id, leaf in prototype_names.items():
        target = next(
            row
            for row in fixture_rows
            if any(_legacy_ref_matches_leaf(ref, leaf) for ref in row["legacy_declaration_refs"])
        )
        target["mapped_record_ids"].append(record_id)
        target["mapped_record_ids"].sort()
        records.append({"id": record_id, "lean_name": f"LatticeSystem.Fixture.{leaf}"})
    retired_entries: list[dict[str, Any]] = []
    retired_record_ids: set[str] = set()
    for ordinal, fixture in RETIRED_FIXTURES.items():
        row = fixture_rows[ordinal - 1]
        fixture_name = f"LatticeSystem.Fixture.{fixture['legacy_leaf']}"
        retired_record_id = record_by_name[fixture_name]
        row["mapped_record_ids"].remove(retired_record_id)
        retired_record_ids.add(retired_record_id)
        if not row["mapped_record_ids"]:
            row["outcome"] = "retired"
            row["disposition"] = "retired_declarations"
        retired_entries.append(
            {
                **fixture,
                "ordinal": ordinal,
                "replacement_record_ids": [],
                "row_sha256": row["row_sha256"],
            }
        )
    records = [record for record in records if record["id"] not in retired_record_ids]
    retired_by_ordinal = {
        ordinal: [entry for entry in retired_entries if entry["ordinal"] == ordinal]
        for ordinal in sorted(RETIRED_FIXTURES)
    }
    cutover_ids = sorted(record["id"] for record in records)
    baseline = {
        "schema_version": 1,
        "baseline_commit": BASELINE_COMMIT,
        "baseline_path": BASELINE_PATH,
        "cutover_record_ids": cutover_ids,
        "legacy_rows": fixture_rows,
        "non_legacy_record_ids": [],
    }
    baseline_raw = canonical_bytes(baseline)
    ids, mappings = certificate_projection(baseline)
    certificate = {
        "baseline_sha256": sha256_bytes(baseline_raw),
        "cutover_record_ids_sha256": sha256_bytes(canonical_bytes(ids)),
        "exceptional_mappings": exceptional_entries,
        "legacy_mapping_sha256": sha256_bytes(canonical_bytes(mappings)),
        "non_record_ordinals": non_record_ordinals,
        "retired_declarations": retired_entries,
        "schema_version": 1,
    }
    certificate_raw = canonical_bytes(certificate)
    baseline_errors = validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        {entry["ordinal"]: entry for entry in exceptional_entries},
        retired_by_ordinal,
    )
    certificate_errors = validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "prototype",
        records,
        repo_root,
    )
    if baseline_errors or certificate_errors:
        failures.append(
            "valid exhaustive fixture was rejected: "
            f"baseline={baseline_errors}, certificate={certificate_errors}"
        )

    mapped_row_index = next(
        index for index, row in enumerate(baseline["legacy_rows"])
        if row["outcome"] == "mapped"
    )
    non_record_row_index = next(
        index for index, row in enumerate(baseline["legacy_rows"])
        if row["outcome"] == "not_a_declaration"
    )
    retired_row_index = next(
        index for index, row in enumerate(baseline["legacy_rows"])
        if row["outcome"] == "retired"
    )
    runtime_row_mutations = (
        (
            "mapped row without IDs",
            mapped_row_index,
            {"mapped_record_ids": []},
        ),
        (
            "mapped row with non-record disposition",
            mapped_row_index,
            {"disposition": "non_declaration"},
        ),
        (
            "non-record row with mapped IDs",
            non_record_row_index,
            {"mapped_record_ids": [records[0]["id"]]},
        ),
        (
            "non-record row without disposition",
            non_record_row_index,
            {"disposition": None},
        ),
        (
            "non-record row with waived disposition",
            non_record_row_index,
            {"disposition": "waived"},
        ),
        (
            "retired row with a mapped ID",
            retired_row_index,
            {"mapped_record_ids": [records[0]["id"]]},
        ),
        (
            "retired row without its closed disposition",
            retired_row_index,
            {"disposition": None},
        ),
    )
    for label, row_index, mutation in runtime_row_mutations:
        mutated = copy.deepcopy(baseline)
        mutated["legacy_rows"][row_index].update(mutation)
        if not validate_cutover_baseline(
            mutated,
            records,
            rows,
            set(non_record_ordinals),
            {entry["ordinal"]: entry for entry in exceptional_entries},
            retired_by_ordinal,
        ):
            failures.append(f"runtime row conditional accepted {label}")

    etc_row = next(
        row for row in fixture_rows if "plain_etc" in row["legacy_grouping_syntax"]
    )
    etc_entry = next(
        entry for entry in exceptional_entries if entry["ordinal"] == etc_row["ordinal"]
    )
    if len(set(etc_entry["expected_lean_names"])) < 2:
        failures.append("plain etc. grouped-row fixture did not bind multiple exact names")

    missing_group_member = copy.deepcopy(baseline)
    hermitian_row = next(
        row
        for row in missing_group_member["legacy_rows"]
        if row["legacy_first_cell"] == "`pauliX/Y/Z_isHermitian`"
    )
    hermitian_row["mapped_record_ids"] = hermitian_row["mapped_record_ids"][:1]
    if not validate_cutover_baseline(
        missing_group_member,
        records,
        rows,
        set(non_record_ordinals),
        {entry["ordinal"]: entry for entry in exceptional_entries},
        retired_by_ordinal,
    ):
        failures.append("slash expansion accepted missing Y/Z group members")

    expected_group_expansions = {
        "`spinHalfOp{1,2,3}`": {
            "spinHalfOp1",
            "spinHalfOp2",
            "spinHalfOp3",
        },
        "`spinHalfOpPlus/Minus_conjTranspose`": {
            "spinHalfOpMinus_conjTranspose",
            "spinHalfOpPlus_conjTranspose",
        },
        (
            "`spinHalfRot1_half_pi_conj_spinHalfOp{2,3}` / "
            "`spinHalfRot2_half_pi_conj_spinHalfOp{3,1}` / "
            "`spinHalfRot3_half_pi_conj_spinHalfOp{1,2}`"
        ): {
            "spinHalfRot1_half_pi_conj_spinHalfOp2",
            "spinHalfRot1_half_pi_conj_spinHalfOp3",
            "spinHalfRot2_half_pi_conj_spinHalfOp1",
            "spinHalfRot2_half_pi_conj_spinHalfOp3",
            "spinHalfRot3_half_pi_conj_spinHalfOp1",
            "spinHalfRot3_half_pi_conj_spinHalfOp2",
        },
    }
    for first_cell, expected_expansion in expected_group_expansions.items():
        source_row = next(row for row in rows if row["legacy_first_cell"] == first_cell)
        if expand_legacy_leaves(source_row) != expected_expansion:
            failures.append(f"deterministic slash expansion drifted for {first_cell}")

    invalid_reference_fixtures = (
        ("empty", ""),
        ("unbalanced brace", "fixture{A,B"),
        ("whitespace-truncated signature", "fixtureName argument"),
        ("Unicode ellipsis", "…fixtureName"),
        ("prose symbolic notation", "Ŝ⁺Ŝ⁻"),
    )
    for label, reference in invalid_reference_fixtures:
        invalid_row = {
            **rows[4],
            "legacy_declaration_refs": [reference],
            "legacy_grouping_syntax": [],
        }
        if expand_legacy_leaves(invalid_row) is not None:
            failures.append(f"invalid {label} reference expanded mechanically")

    exceptional_by_ordinal = {
        entry["ordinal"]: entry for entry in exceptional_entries
    }
    for ordinal, expected_names in PINNED_EXCEPTIONAL_EXPECTED_NAMES.items():
        if expand_legacy_leaves(rows[ordinal - 1]) is not None:
            failures.append(f"pinned ambiguous/prose row {ordinal} expanded mechanically")
        entry = exceptional_by_ordinal.get(ordinal)
        if entry is None or entry["expected_lean_names"] != list(expected_names):
            failures.append(f"pinned exceptional mapping drifted for row {ordinal}")
            continue
        for label, names in (
            ("missing", list(expected_names[:-1])),
            (
                "extra",
                sorted([*expected_names, f"LatticeSystem.Fixture.extra_{ordinal}"]),
            ),
        ):
            mutated_evidence = copy.deepcopy(exceptional_by_ordinal)
            mutated_evidence[ordinal]["expected_lean_names"] = names
            if not validate_cutover_baseline(
                baseline,
                records,
                rows,
                set(non_record_ordinals),
                mutated_evidence,
                retired_by_ordinal,
            ):
                failures.append(
                    f"pinned exceptional row {ordinal} accepted {label} certificate names"
                )

    uncertified_group = {
        entry["ordinal"]: entry
        for entry in exceptional_entries
        if entry["ordinal"] != etc_row["ordinal"]
    }
    if not validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        uncertified_group,
        retired_by_ordinal,
    ):
        failures.append("non-expandable etc. group was accepted without certificate evidence")

    nongrouped = copy.deepcopy(baseline)
    exact_row = next(
        row
        for row in nongrouped["legacy_rows"]
        if not row["legacy_grouping_syntax"] and row["outcome"] == "mapped"
    )
    wrong_record = records[-1]
    exact_row["mapped_record_ids"] = [wrong_record["id"]]
    forged_exception = {
        **{entry["ordinal"]: entry for entry in exceptional_entries},
        exact_row["ordinal"]: {
            "expected_lean_names": [wrong_record["lean_name"]],
            "ordinal": exact_row["ordinal"],
            "row_sha256": exact_row["row_sha256"],
        },
    }
    if not validate_cutover_baseline(
        nongrouped,
        records,
        rows,
        set(non_record_ordinals),
        forged_exception,
        retired_by_ordinal,
    ):
        failures.append("nongrouped mismatched row was accepted through certificate evidence")

    all_non_record = copy.deepcopy(baseline)
    for row in all_non_record["legacy_rows"]:
        if not any(record_id in PROTOTYPE_RECORD_IDS for record_id in row["mapped_record_ids"]):
            row.update(
                disposition="non_declaration",
                mapped_record_ids=[],
                outcome="not_a_declaration",
            )
    if not validate_cutover_baseline(
        all_non_record,
        records,
        rows,
        set(range(1, BASELINE_ROW_COUNT + 1)),
        {entry["ordinal"]: entry for entry in exceptional_entries},
        retired_by_ordinal,
    ):
        failures.append("all-rows-non-record-except-prototype fixture was accepted")

    mixed_retired_row = baseline["legacy_rows"][655]
    pure_retired_row = baseline["legacy_rows"][675]
    if (
        mixed_retired_row["outcome"] != "mapped"
        or len(mixed_retired_row["mapped_record_ids"]) != 1
        or pure_retired_row["outcome"] != "retired"
        or pure_retired_row["mapped_record_ids"]
    ):
        failures.append("mixed/pure retired row fixtures drifted")
    missing_survivor = copy.deepcopy(baseline)
    missing_survivor["legacy_rows"][655]["mapped_record_ids"] = []
    if not validate_cutover_baseline(
        missing_survivor,
        records,
        rows,
        set(non_record_ordinals),
        exceptional_by_ordinal,
        retired_by_ordinal,
    ):
        failures.append("mixed retired row accepted deletion of its surviving declaration")
    uncertified_retirement = {
        ordinal: entries
        for ordinal, entries in retired_by_ordinal.items()
        if ordinal != 656
    }
    if not validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        exceptional_by_ordinal,
        uncertified_retirement,
    ):
        failures.append("mixed retired row accepted an uncertified missing legacy leaf")
    wrong_row_retirement = copy.deepcopy(retired_by_ordinal)
    wrong_row_entry = wrong_row_retirement.pop(656)[0]
    wrong_row_entry["ordinal"] = 657
    wrong_row_entry["row_sha256"] = baseline["legacy_rows"][656]["row_sha256"]
    wrong_row_retirement[657] = [wrong_row_entry]
    if not validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        exceptional_by_ordinal,
        wrong_row_retirement,
    ):
        failures.append("retirement evidence was accepted for the wrong legacy row")
    wrong_hash_retirement = copy.deepcopy(retired_by_ordinal)
    wrong_hash_retirement[656][0]["row_sha256"] = "0" * 64
    if not validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        exceptional_by_ordinal,
        wrong_hash_retirement,
    ):
        failures.append("retirement evidence was accepted with the wrong row hash")
    misnamed_retirement_entries = copy.deepcopy(retired_entries)
    misnamed_retirement_entries[0]["legacy_leaf"] = (
        "sublatticeSpinHalfOpMinus_mul_sublatticeSpinHalfOpPlus_eq"
    )
    _misnamed_map, misnamed_errors = retired_declaration_map(
        misnamed_retirement_entries, repo_root
    )
    if not misnamed_errors:
        failures.append("retirement evidence accepted a misnamed deleted declaration")
    nonexistent_retirement = copy.deepcopy(retired_entries)
    nonexistent_retirement[0]["legacy_leaf"] = "neverExistedLegacyDeclaration"
    nonexistent_retirement[0]["former_lean_name"] = (
        "LatticeSystem.Quantum.neverExistedLegacyDeclaration"
    )
    _nonexistent_map, nonexistent_errors = retired_declaration_map(
        nonexistent_retirement, repo_root
    )
    if not nonexistent_errors:
        failures.append("retirement evidence accepted a name absent from deletion history")
    fabricated_commit = copy.deepcopy(retired_entries)
    fabricated_commit[0]["deletion_commit"] = "0" * 40
    _fabricated_map, fabricated_errors = retired_declaration_map(
        fabricated_commit, repo_root
    )
    if not fabricated_errors:
        failures.append("retirement evidence accepted a fabricated deletion commit")
    missing_replacement = copy.deepcopy(retired_by_ordinal)
    missing_replacement[656][0]["replacement_record_ids"] = ["missing-replacement"]
    if not validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        exceptional_by_ordinal,
        missing_replacement,
    ):
        failures.append("retirement evidence accepted a missing replacement record")
    retired_current_record = [
        *records,
        {
            "id": "fixture-retired-still-current",
            "lean_name": retired_entries[0]["former_lean_name"],
        },
    ]
    if not validate_cutover_baseline(
        baseline,
        retired_current_record,
        rows,
        set(non_record_ordinals),
        exceptional_by_ordinal,
        retired_by_ordinal,
    ):
        failures.append("retired declaration accepted a current catalogue record")

    remapped = copy.deepcopy(baseline)
    remapped["legacy_rows"][0]["mapped_record_ids"] = remapped["legacy_rows"][1][
        "mapped_record_ids"
    ]
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        remapped,
        canonical_bytes(remapped),
        "prototype",
        records,
        repo_root,
    ):
        failures.append("row remapping without a new certificate was accepted")
    shrunk = copy.deepcopy(baseline)
    shrunk["cutover_record_ids"].pop()
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        shrunk,
        canonical_bytes(shrunk),
        "prototype",
        records,
        repo_root,
    ):
        failures.append("cutover ID shrink without a new certificate was accepted")
    omitted_current = [*records, {"id": "unfrozen", "lean_name": "LatticeSystem.Fixture.unfrozen"}]
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "prototype",
        omitted_current,
        repo_root,
    ):
        failures.append("prototype freeze omitted a current record")
    accepted_digest = sha256_bytes(certificate_raw)
    if validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "authoritative",
        omitted_current,
        repo_root,
        accepted_certificate_sha256=accepted_digest,
    ):
        failures.append("authoritative post-cutover record superset was rejected")
    deleted = records[1:]
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "authoritative",
        deleted,
        repo_root,
        accepted_certificate_sha256=accepted_digest,
    ):
        failures.append("authoritative deletion of a certified record was accepted")

    if validate_cutover_requirement("prototype", None, None):
        failures.append("prototype incorrectly required cutover evidence")
    if not validate_cutover_requirement("authoritative", None, None):
        failures.append("authoritative catalogue without cutover evidence was accepted")
    if not validate_cutover_requirement("prototype", "other.json", "other.json"):
        failures.append("non-fixed optional baseline path was accepted")
    return failures
