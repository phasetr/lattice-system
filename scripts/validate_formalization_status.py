#!/usr/bin/env python3
"""Validate and deterministically aggregate formalization-status version 1."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Iterable

from formalization_cutover import (
    CUTOVER_BASELINE_KEYS,
    CUTOVER_CERTIFICATE_KEYS,
    LEGACY_ROW_KEYS,
    reconstruct_legacy_rows,
    self_test as cutover_self_test,
    validate_cutover_baseline,
    validate_cutover_certificate,
    validate_cutover_requirement,
)


SCHEMA_VERSION = 1
GENERATOR_VERSION = 2
MANIFEST_KEYS = {
    "catalog_state",
    "cutover_baseline",
    "cutover_certificate",
    "human_publication_root",
    "machine_publication_root",
    "record_shards",
    "registries",
    "schema",
    "schema_version",
}
MANIFEST_REQUIRED_KEYS = MANIFEST_KEYS - {"cutover_baseline", "cutover_certificate"}
REGISTRY_KEYS = {"source_items", "sources", "topics"}
SHARD_KEYS = {"records", "schema_version", "source_id", "source_unit"}
RELATION_RANK = {
    "formalizes": 0,
    "presents": 0,
    "attributes": 1,
    "supports": 2,
    "cross_checks": 3,
}
INLINE_TEXT_PATTERN = r"^(?![\s\S]*[\u0000-\u001F\u007F-\u009F])[\s\S]+$"
HTTPS_URL_PATTERN = (
    r"^(?![\s\S]*[\u0000-\u001F\u007F-\u009F])https://[\s\S]+$"
)
INLINE_TEXT_RE = re.compile(INLINE_TEXT_PATTERN)


class Validation:
    """Collect validation errors so one run reports every actionable defect."""

    def __init__(self) -> None:
        self.errors: list[str] = []

    def require(self, condition: bool, message: str) -> None:
        """Record an error when a contract condition is false."""
        if not condition:
            self.errors.append(message)

    def keys(
        self,
        value: Any,
        properties: set[str],
        required: set[str],
        location: str,
    ) -> None:
        """Reject missing and unknown object fields at a contract location."""
        if not isinstance(value, dict):
            self.errors.append(f"{location}: expected object")
            return
        missing = sorted(required - set(value))
        unknown = sorted(set(value) - properties)
        if missing:
            self.errors.append(f"{location}: missing fields: {', '.join(missing)}")
        if unknown:
            self.errors.append(f"{location}: unknown fields: {', '.join(unknown)}")


class Contract:
    """Schema-derived constants shared by structural and semantic validation."""

    def __init__(self, schema: dict[str, Any], validation: Validation) -> None:
        self.schema = schema
        self.defs = schema.get("$defs", {})
        self.validation = validation
        self.declaration_kinds = self.enum("declaration_kind")
        self.implementation_states = self.enum("implementation_state")
        self.origins = self.enum("origin")
        self.source_coverages = self.enum("source_coverage")
        self.trust_states = self.enum("trust_state")
        self.relation_kinds = set(
            self.defs.get("source_relation", {})
            .get("properties", {})
            .get("relation", {})
            .get("enum", [])
        )
        self.stable_id = self.pattern("stable_id")
        self.lean_name = self.pattern("lean_name")
        self.module_name = self.pattern("module_name")
        self.source_path = self.pattern("source_path")
        self.inline_text = self.pattern("inline_text")

    def enum(self, name: str) -> set[str]:
        """Read a closed vocabulary from the JSON Schema."""
        values = self.defs.get(name, {}).get("enum")
        self.validation.require(
            isinstance(values, list) and all(isinstance(value, str) for value in values),
            f"schema parity: $defs.{name}.enum is missing or invalid",
        )
        return set(values or [])

    def pattern(self, name: str) -> re.Pattern[str]:
        """Compile a pattern directly from the JSON Schema."""
        pattern = self.defs.get(name, {}).get("pattern")
        self.validation.require(
            isinstance(pattern, str),
            f"schema parity: $defs.{name}.pattern is missing",
        )
        return re.compile(pattern or r"(?!)")

    def object_keys(self, name: str) -> tuple[set[str], set[str]]:
        """Return allowed and required keys from one strict schema object."""
        definition = self.defs.get(name, {})
        properties = set(definition.get("properties", {}))
        required = set(definition.get("required", []))
        self.validation.require(
            definition.get("additionalProperties") is False,
            f"schema parity: $defs.{name} must reject additional properties",
        )
        self.validation.require(
            required <= properties,
            f"schema parity: $defs.{name}.required is not a property subset",
        )
        return properties, required

    def check_parity(self) -> None:
        """Fail startup if schema fields, enums, or patterns drift from semantics."""
        def walk(value: Any) -> Iterable[dict[str, Any]]:
            if isinstance(value, dict):
                yield value
                for child in value.values():
                    yield from walk(child)
            elif isinstance(value, list):
                for child in value:
                    yield from walk(child)

        for node in walk(self.schema):
            reference = node.get("$ref")
            if isinstance(reference, str) and reference.startswith("#/$defs/"):
                self.validation.require(
                    reference.removeprefix("#/$defs/") in self.defs,
                    f"schema parity: unresolved local reference {reference}",
                )
        expected_record = {
            "axiom_dependencies",
            "capstone",
            "declaration_kind",
            "id",
            "implementation_state",
            "lean_name",
            "module",
            "origin",
            "proof_guide_anchor",
            "source_coverage",
            "source_path",
            "source_relations",
            "summary",
            "topic_ids",
            "trust_state",
        }
        expected_source = {
            "authors",
            "edition",
            "id",
            "publication",
            "title",
            "url",
            "year",
        }
        expected_source_required = {"authors", "id", "year"}
        expected_item = {
            "equations",
            "id",
            "item_kind",
            "item_number",
            "pages",
            "section",
            "source_id",
            "title",
        }
        expected_topic = {"description", "id", "label"}
        expected_relation = {"relation", "source_item_id"}
        expected_aggregate = {
            "catalog_state",
            "generated_by",
            "generator_version",
            "input_sha256",
            "records",
            "schema_version",
            "source_items",
            "sources",
            "topics",
        }
        checks = (
            ("aggregate", expected_aggregate, expected_aggregate),
            ("declaration_record", expected_record, expected_record),
            ("cutover_baseline", CUTOVER_BASELINE_KEYS, CUTOVER_BASELINE_KEYS),
            ("cutover_certificate", CUTOVER_CERTIFICATE_KEYS, CUTOVER_CERTIFICATE_KEYS),
            ("cutover_legacy_row", LEGACY_ROW_KEYS, LEGACY_ROW_KEYS),
            ("manifest", MANIFEST_KEYS, MANIFEST_REQUIRED_KEYS),
            ("record_shard", SHARD_KEYS, SHARD_KEYS),
            ("source", expected_source, expected_source_required),
            ("source_item", expected_item, expected_item),
            ("source_relation", expected_relation, expected_relation),
            ("topic", expected_topic, expected_topic),
        )
        for name, properties, required in checks:
            actual_properties, actual_required = self.object_keys(name)
            self.validation.require(
                actual_properties == properties and actual_required == required,
                f"schema parity: $defs.{name} field contract drifted",
            )
        registry_checks = {
            "source_item_registry": {"schema_version", "source_items"},
            "source_registry": {"schema_version", "sources"},
            "topic_registry": {"schema_version", "topics"},
        }
        for name, fields in registry_checks.items():
            actual_properties, actual_required = self.object_keys(name)
            self.validation.require(
                actual_properties == fields and actual_required == fields,
                f"schema parity: $defs.{name} field contract drifted",
            )
        manifest_registries = self.defs["manifest"]["properties"]["registries"]
        self.validation.require(
            set(manifest_registries.get("properties", {})) == REGISTRY_KEYS
            and set(manifest_registries.get("required", [])) == REGISTRY_KEYS
            and manifest_registries.get("additionalProperties") is False,
            "schema parity: manifest registry contract drifted",
        )
        aggregate_properties = self.defs["aggregate"]["properties"]
        self.validation.require(
            aggregate_properties.get("generator_version", {}).get("const")
            == GENERATOR_VERSION,
            "schema parity: generator version drifted",
        )
        self.validation.require(
            aggregate_properties.get("generated_by", {}).get("const")
            == "scripts/validate_formalization_status.py"
            and aggregate_properties.get("input_sha256", {}).get("pattern")
            == "^[0-9a-f]{64}$",
            "schema parity: aggregate generator/digest contract drifted",
        )
        for name in (
            "aggregate",
            "manifest",
            "record_shard",
            "source_item_registry",
            "source_registry",
            "topic_registry",
        ):
            self.validation.require(
                self.defs[name]["properties"].get("schema_version", {}).get("const")
                == SCHEMA_VERSION,
                f"schema parity: $defs.{name} schema version drifted",
            )
        record_properties = self.defs["declaration_record"]["properties"]
        for field, minimum in (
            ("axiom_dependencies", 0),
            ("source_relations", 0),
            ("topic_ids", 1),
        ):
            field_schema = record_properties[field]
            self.validation.require(
                field_schema.get("type") == "array"
                and field_schema.get("uniqueItems") is True
                and field_schema.get("minItems", 0) == minimum,
                f"schema parity: declaration array constraint drifted for {field}",
            )
        equations = self.defs["source_item"]["properties"]["equations"]
        self.validation.require(
            equations.get("type") == "array" and equations.get("uniqueItems") is True,
            "schema parity: source-item equation constraints drifted",
        )
        manifest_shards = self.defs["manifest"]["properties"]["record_shards"]
        self.validation.require(
            manifest_shards.get("type") == "array"
            and manifest_shards.get("uniqueItems") is True,
            "schema parity: manifest shard-array constraints drifted",
        )
        baseline_rows = self.defs["cutover_baseline"]["properties"]["legacy_rows"]
        self.validation.require(
            baseline_rows.get("minItems") == 2052
            and baseline_rows.get("maxItems") == 2052
            and self.defs["manifest"]["properties"].get("cutover_baseline", {}).get("const")
            == "cutover-baseline.json",
            "schema parity: cutover baseline cardinality/path drifted",
        )
        self.validation.require(
            self.defs["manifest"]["properties"].get("cutover_certificate", {}).get("const")
            == "cutover-certificate.json",
            "schema parity: cutover certificate path drifted",
        )
        self.validation.require(
            self.declaration_kinds
            == {
                "abbrev",
                "axiom",
                "class",
                "definition",
                "inductive",
                "instance",
                "lemma",
                "opaque",
                "structure",
                "theorem",
            },
            "schema parity: declaration_kind vocabulary drifted",
        )
        self.validation.require(
            self.implementation_states == {"implemented", "in_progress"},
            "schema parity: implementation_state vocabulary drifted",
        )
        self.validation.require(
            self.source_coverages
            == {"complete", "conditional_reduction", "not_applicable", "partial"},
            "schema parity: source_coverage vocabulary drifted",
        )
        self.validation.require(
            self.trust_states
            == {"axiom_free", "depends_on_documented_axioms", "documented_axiom"},
            "schema parity: trust_state vocabulary drifted",
        )
        self.validation.require(
            self.relation_kinds
            == {"attributes", "cross_checks", "formalizes", "presents", "supports"},
            "schema parity: source relation vocabulary drifted",
        )
        source_url = self.defs["source"]["properties"].get("url", {})
        self.validation.require(
            "url" not in self.defs["source"]["required"]
            and source_url.get("pattern")
            == HTTPS_URL_PATTERN,
            "schema parity: source URL must be optional and HTTPS when present",
        )
        year = self.defs["source"]["properties"].get("year", {})
        self.validation.require(
            year.get("minimum") == 1000 and year.get("maximum") == 9999,
            "schema parity: source year bounds drifted",
        )
        authors = self.defs["source"]["properties"].get("authors", {})
        self.validation.require(
            authors.get("minItems") == 1
            and authors.get("type") == "array"
            and authors.get("items", {}).get("$ref") == "#/$defs/inline_text",
            "schema parity: source authors constraints drifted",
        )
        self.validation.require(
            self.defs.get("inline_text")
            == {"pattern": INLINE_TEXT_PATTERN, "type": "string"},
            "schema parity: inline-render text contract drifted",
        )
        inline_refs = (
            record_properties.get("summary"),
            self.defs["source"]["properties"].get("edition"),
            self.defs["source"]["properties"].get("publication"),
            self.defs["source"]["properties"].get("title"),
            self.defs["source_item"]["properties"]["equations"].get("items"),
            self.defs["source_item"]["properties"].get("title"),
            self.defs["topic"]["properties"].get("description"),
            self.defs["topic"]["properties"].get("label"),
        )
        self.validation.require(
            all(node == {"$ref": "#/$defs/inline_text"} for node in inline_refs),
            "schema parity: an inline-rendered field bypasses inline_text",
        )
        for field in ("item_number", "pages", "section"):
            alternatives = self.defs["source_item"]["properties"][field].get("oneOf")
            self.validation.require(
                alternatives
                == [{"$ref": "#/$defs/inline_text"}, {"type": "null"}],
                f"schema parity: source-item {field} bypasses inline_text",
            )

        def implication(field: str, value: Any, then: dict[str, Any]) -> dict[str, Any]:
            return {
                "if": {
                    "properties": {field: {"const": value}},
                    "required": [field],
                },
                "then": then,
            }

        primary_relation = {
            "properties": {
                "relation": {
                    "enum": ["formalizes", "presents"],
                }
            },
            "required": ["relation"],
        }
        expected_implications = [
            implication(
                "trust_state",
                "axiom_free",
                {"properties": {"axiom_dependencies": {"maxItems": 0}}},
            ),
            implication(
                "trust_state",
                "depends_on_documented_axioms",
                {
                    "properties": {
                        "axiom_dependencies": {"minItems": 1},
                        "declaration_kind": {"not": {"const": "axiom"}},
                    }
                },
            ),
            implication(
                "trust_state",
                "documented_axiom",
                {
                    "properties": {
                        "axiom_dependencies": {"maxItems": 1, "minItems": 1},
                        "declaration_kind": {"const": "axiom"},
                        "implementation_state": {"const": "implemented"},
                    }
                },
            ),
            implication(
                "declaration_kind",
                "axiom",
                {"properties": {"trust_state": {"const": "documented_axiom"}}},
            ),
            implication(
                "implementation_state",
                "in_progress",
                {
                    "properties": {
                        "capstone": {"const": False},
                        "source_coverage": {"const": "partial"},
                    }
                },
            ),
            implication(
                "capstone",
                True,
                {
                    "properties": {
                        "implementation_state": {"const": "implemented"},
                        "source_coverage": {
                            "enum": ["complete", "conditional_reduction"]
                        },
                    }
                },
            ),
            implication(
                "origin",
                "literature",
                {
                    "properties": {
                        "source_coverage": {"not": {"const": "not_applicable"}},
                        "source_relations": {
                            "contains": primary_relation,
                            "maxContains": 1,
                            "minContains": 1,
                        },
                    }
                },
            ),
            implication(
                "origin",
                "project_original",
                {
                    "allOf": [
                        implication(
                            "implementation_state",
                            "implemented",
                            {
                                "properties": {
                                    "source_coverage": {"const": "not_applicable"}
                                }
                            },
                        )
                    ],
                    "properties": {
                        "source_relations": {
                            "not": {"contains": primary_relation}
                        }
                    },
                },
            ),
        ]
        actual_implications = self.defs["declaration_record"].get("allOf", [])
        self.validation.require(
            canonical_json(actual_implications) == canonical_json(expected_implications),
            "schema parity: full declaration conditional implications drifted",
        )


def canonical_json(value: Any) -> str:
    """Serialize canonical repository JSON."""
    return json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def _schema_type_matches(value: Any, expected: str) -> bool:
    """Return whether a Python JSON value has one JSON Schema primitive type."""
    return {
        "array": isinstance(value, list),
        "boolean": isinstance(value, bool),
        "integer": isinstance(value, int) and not isinstance(value, bool),
        "null": value is None,
        "object": isinstance(value, dict),
        "string": isinstance(value, str),
    }.get(expected, False)


def _resolve_local_ref(
    reference: Any,
    root_schema: dict[str, Any],
    location: str,
    validation: Validation,
) -> dict[str, Any] | None:
    """Resolve a dependency-free local JSON Pointer reference."""
    if not isinstance(reference, str) or not reference.startswith("#/"):
        validation.errors.append(f"{location}: unsupported schema reference {reference!r}")
        return None
    node: Any = root_schema
    for raw_part in reference[2:].split("/"):
        part = raw_part.replace("~1", "/").replace("~0", "~")
        if not isinstance(node, dict) or part not in node:
            validation.errors.append(f"{location}: unresolved schema reference {reference}")
            return None
        node = node[part]
    if not isinstance(node, dict):
        validation.errors.append(f"{location}: schema reference is not an object: {reference}")
        return None
    return node


def validate_schema_instance(
    value: Any,
    schema: Any,
    root_schema: dict[str, Any],
    location: str,
    validation: Validation,
) -> None:
    """Evaluate the JSON Schema subset used by the version-1 contract."""
    if not isinstance(schema, dict):
        validation.errors.append(f"{location}: malformed schema node")
        return
    if "$ref" in schema:
        target = _resolve_local_ref(schema.get("$ref"), root_schema, location, validation)
        if target is not None:
            validate_schema_instance(value, target, root_schema, location, validation)
        return

    expected_type = schema.get("type")
    if expected_type is not None:
        types = expected_type if isinstance(expected_type, list) else [expected_type]
        if not all(isinstance(item, str) for item in types) or not any(
            _schema_type_matches(value, item) for item in types
        ):
            validation.errors.append(f"{location}: schema type mismatch")
            return

    if "const" in schema and value != schema["const"]:
        validation.errors.append(f"{location}: expected constant {schema['const']!r}")
    enum = schema.get("enum")
    if isinstance(enum, list) and value not in enum:
        validation.errors.append(f"{location}: value is outside the closed enum")

    for index, subschema in enumerate(schema.get("allOf", [])) if isinstance(schema.get("allOf", []), list) else []:
        validate_schema_instance(value, subschema, root_schema, f"{location}.allOf[{index}]", validation)

    one_of = schema.get("oneOf")
    if isinstance(one_of, list):
        matches: list[int] = []
        for index, subschema in enumerate(one_of):
            trial = Validation()
            validate_schema_instance(value, subschema, root_schema, location, trial)
            if not trial.errors:
                matches.append(index)
        if len(matches) != 1:
            validation.errors.append(f"{location}: expected exactly one matching oneOf branch")
        else:
            validate_schema_instance(value, one_of[matches[0]], root_schema, location, validation)

    negated = schema.get("not")
    if isinstance(negated, dict):
        trial = Validation()
        validate_schema_instance(value, negated, root_schema, location, trial)
        if not trial.errors:
            validation.errors.append(f"{location}: value matched a forbidden schema")

    condition = schema.get("if")
    if isinstance(condition, dict):
        trial = Validation()
        validate_schema_instance(value, condition, root_schema, location, trial)
        if not trial.errors and isinstance(schema.get("then"), dict):
            validate_schema_instance(value, schema["then"], root_schema, location, validation)

    if isinstance(value, dict):
        required = schema.get("required", [])
        if isinstance(required, list):
            for field in required:
                if isinstance(field, str) and field not in value:
                    validation.errors.append(f"{location}: missing required field {field}")
        properties = schema.get("properties", {})
        if isinstance(properties, dict):
            for field, child in value.items():
                if field in properties:
                    validate_schema_instance(
                        child, properties[field], root_schema, f"{location}.{field}", validation
                    )
                elif schema.get("additionalProperties") is False:
                    validation.errors.append(f"{location}: unknown field {field}")

    if isinstance(value, list):
        minimum = schema.get("minItems")
        maximum = schema.get("maxItems")
        if isinstance(minimum, int) and len(value) < minimum:
            validation.errors.append(f"{location}: too few array items")
        if isinstance(maximum, int) and len(value) > maximum:
            validation.errors.append(f"{location}: too many array items")
        if schema.get("uniqueItems") is True:
            serialized = [json.dumps(item, ensure_ascii=False, sort_keys=True) for item in value]
            if len(serialized) != len(set(serialized)):
                validation.errors.append(f"{location}: duplicate array items")
        item_schema = schema.get("items")
        if isinstance(item_schema, dict):
            for index, item in enumerate(value):
                validate_schema_instance(
                    item, item_schema, root_schema, f"{location}[{index}]", validation
                )
        contains = schema.get("contains")
        if isinstance(contains, dict):
            count = 0
            for item in value:
                trial = Validation()
                validate_schema_instance(item, contains, root_schema, location, trial)
                count += not trial.errors
            min_contains = schema.get("minContains", 1)
            max_contains = schema.get("maxContains")
            if isinstance(min_contains, int) and count < min_contains:
                validation.errors.append(f"{location}: too few contains matches")
            if isinstance(max_contains, int) and count > max_contains:
                validation.errors.append(f"{location}: too many contains matches")

    if isinstance(value, str):
        minimum_length = schema.get("minLength")
        if isinstance(minimum_length, int) and len(value) < minimum_length:
            validation.errors.append(f"{location}: string is too short")
        pattern = schema.get("pattern")
        if isinstance(pattern, str):
            try:
                matched = re.search(pattern, value) is not None
            except re.error as error:
                validation.errors.append(f"{location}: invalid schema pattern: {error}")
            else:
                if not matched:
                    validation.errors.append(f"{location}: string does not match schema pattern")

    if isinstance(value, int) and not isinstance(value, bool):
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")
        if isinstance(minimum, (int, float)) and value < minimum:
            validation.errors.append(f"{location}: number is below minimum")
        if isinstance(maximum, (int, float)) and value > maximum:
            validation.errors.append(f"{location}: number is above maximum")


def safe_relative_path(
    base: Path,
    raw_path: Any,
    location: str,
    validation: Validation,
) -> Path | None:
    """Validate a relative POSIX path and containment before any dereference."""
    if not isinstance(raw_path, str) or not raw_path:
        validation.errors.append(f"{location}: expected non-empty relative POSIX path")
        return None
    segments = raw_path.split("/")
    if (
        raw_path.startswith("/")
        or "\\" in raw_path
        or any(segment in {"", ".", ".."} for segment in segments)
    ):
        validation.errors.append(f"{location}: unsafe relative POSIX path")
        return None
    base_resolved = base.resolve()
    candidate = (base / raw_path).resolve()
    try:
        candidate.relative_to(base_resolved)
    except ValueError:
        validation.errors.append(f"{location}: path escapes its allowed root")
        return None
    return candidate


def safe_expected_relative_path(
    base: Path,
    raw_path: Any,
    expected: str,
    location: str,
    validation: Validation,
) -> Path | None:
    """Gate a fixed manifest-owned path before reading it."""
    candidate = safe_relative_path(base, raw_path, location, validation)
    validation.require(raw_path == expected, f"{location}: expected {expected}")
    return candidate if raw_path == expected else None


def read_json(path: Path, validation: Validation) -> tuple[Any, bytes]:
    """Read UTF-8 JSON and enforce byte-for-byte canonical formatting."""
    try:
        raw = path.read_bytes()
    except OSError as error:
        validation.errors.append(f"{path}: cannot read: {error}")
        return None, b""
    validation.require(not raw.startswith(b"\xef\xbb\xbf"), f"{path}: UTF-8 BOM is forbidden")
    validation.require(b"\r" not in raw, f"{path}: CR line endings are forbidden")
    try:
        text = raw.decode("utf-8")
        value = json.loads(text)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        validation.errors.append(f"{path}: invalid UTF-8 JSON: {error}")
        return None, raw
    validation.require(text == canonical_json(value), f"{path}: JSON is not canonical")
    return value, raw


def require_string(value: Any, location: str, validation: Validation) -> bool:
    """Require a non-empty string."""
    passed = isinstance(value, str) and bool(value)
    validation.require(passed, f"{location}: expected non-empty string")
    return passed


def require_inline_text(value: Any, location: str, validation: Validation) -> bool:
    """Require non-empty single-line text without ASCII control characters."""
    passed = isinstance(value, str) and INLINE_TEXT_RE.fullmatch(value) is not None
    validation.require(passed, f"{location}: expected non-empty inline text without control characters")
    return passed


def require_sorted_unique_strings(
    values: Any,
    location: str,
    validation: Validation,
    *,
    nonempty: bool = False,
) -> bool:
    """Require a sorted, duplicate-free string array."""
    if not isinstance(values, list) or not all(isinstance(value, str) for value in values):
        validation.errors.append(f"{location}: expected array of strings")
        return False
    validation.require(values == sorted(set(values)), f"{location}: must be sorted and unique")
    validation.require(not nonempty or bool(values), f"{location}: must not be empty")
    return True


def require_unique_strings_preserve_order(
    values: Any,
    location: str,
    validation: Validation,
) -> bool:
    """Require unique strings while preserving source presentation order."""
    if not isinstance(values, list) or not all(isinstance(value, str) and value for value in values):
        validation.errors.append(f"{location}: expected array of non-empty strings")
        return False
    validation.require(len(values) == len(set(values)), f"{location}: duplicate values")
    return True


def index_by_id(
    items: Any,
    location: str,
    contract: Contract,
    validation: Validation,
) -> dict[str, dict[str, Any]]:
    """Index a sorted object array while checking stable IDs."""
    if not isinstance(items, list):
        validation.errors.append(f"{location}: expected array")
        return {}
    identifiers = [item.get("id") for item in items if isinstance(item, dict)]
    if all(isinstance(identifier, str) for identifier in identifiers):
        validation.require(identifiers == sorted(identifiers), f"{location}: sort records by id")
    result: dict[str, dict[str, Any]] = {}
    for index, item in enumerate(items):
        item_location = f"{location}[{index}]"
        if not isinstance(item, dict):
            validation.errors.append(f"{item_location}: expected object")
            continue
        identifier = item.get("id")
        valid_id = isinstance(identifier, str) and contract.stable_id.fullmatch(identifier)
        validation.require(bool(valid_id), f"{item_location}.id: invalid stable ID")
        if valid_id:
            validation.require(identifier not in result, f"{item_location}.id: duplicate {identifier}")
            result[identifier] = item
    return result


def validate_sources(
    data: Any,
    contract: Contract,
    validation: Validation,
) -> dict[str, dict[str, Any]]:
    """Validate bibliographic works, including incomplete older metadata."""
    if not isinstance(data, dict):
        validation.errors.append("sources.json: expected object")
        return {}
    validation.keys(data, {"schema_version", "sources"}, {"schema_version", "sources"}, "sources.json")
    validation.require(data.get("schema_version") == SCHEMA_VERSION, "sources.json: bad version")
    sources = index_by_id(data.get("sources"), "sources.json.sources", contract, validation)
    properties, required = contract.object_keys("source")
    for identifier, source in sources.items():
        location = f"sources.json.sources[{identifier}]"
        validation.keys(source, properties, required, location)
        authors = source.get("authors")
        validation.require(
            isinstance(authors, list)
            and bool(authors)
            and all(
                isinstance(author, str) and INLINE_TEXT_RE.fullmatch(author) is not None
                for author in authors
            ),
            f"{location}.authors: expected non-empty string array",
        )
        year = source.get("year")
        validation.require(
            isinstance(year, int) and 1000 <= year <= 9999,
            f"{location}.year: expected integer from 1000 through 9999",
        )
        for field in ("edition", "publication", "title"):
            if field in source:
                require_inline_text(source[field], f"{location}.{field}", validation)
        if "url" in source:
            validation.require(
                isinstance(source["url"], str)
                and source["url"].startswith("https://")
                and INLINE_TEXT_RE.fullmatch(source["url"]) is not None,
                f"{location}.url: expected HTTPS URL",
            )
    return sources


def validate_source_items(
    data: Any,
    contract: Contract,
    source_ids: set[str],
    validation: Validation,
) -> dict[str, dict[str, Any]]:
    """Validate locatable units while retaining semantic equation order."""
    if not isinstance(data, dict):
        validation.errors.append("source-items.json: expected object")
        return {}
    expected = {"schema_version", "source_items"}
    validation.keys(data, expected, expected, "source-items.json")
    validation.require(data.get("schema_version") == SCHEMA_VERSION, "source-items.json: bad version")
    items = index_by_id(data.get("source_items"), "source-items.json.source_items", contract, validation)
    properties, required = contract.object_keys("source_item")
    item_kinds = set(contract.defs["source_item"]["properties"]["item_kind"]["enum"])
    for identifier, item in items.items():
        location = f"source-items.json.source_items[{identifier}]"
        validation.keys(item, properties, required, location)
        item_source_id = item.get("source_id")
        item_kind = item.get("item_kind")
        validation.require(
            isinstance(item_source_id, str) and item_source_id in source_ids,
            f"{location}.source_id: unknown source",
        )
        validation.require(
            isinstance(item_kind, str) and item_kind in item_kinds,
            f"{location}.item_kind: invalid",
        )
        for field in ("item_number", "pages", "section"):
            validation.require(
                item.get(field) is None
                or isinstance(item.get(field), str)
                and INLINE_TEXT_RE.fullmatch(item[field]) is not None,
                f"{location}.{field}: expected inline text or null",
            )
        require_inline_text(item.get("title"), f"{location}.title", validation)
        require_unique_strings_preserve_order(item.get("equations"), f"{location}.equations", validation)
        for index, equation in enumerate(item.get("equations", [])) if isinstance(item.get("equations"), list) else []:
            require_inline_text(equation, f"{location}.equations[{index}]", validation)
    return items


def validate_topics(
    data: Any,
    contract: Contract,
    validation: Validation,
) -> dict[str, dict[str, Any]]:
    """Validate controlled topic navigation terms."""
    if not isinstance(data, dict):
        validation.errors.append("topics.json: expected object")
        return {}
    expected = {"schema_version", "topics"}
    validation.keys(data, expected, expected, "topics.json")
    validation.require(data.get("schema_version") == SCHEMA_VERSION, "topics.json: bad version")
    topics = index_by_id(data.get("topics"), "topics.json.topics", contract, validation)
    properties, required = contract.object_keys("topic")
    for identifier, topic in topics.items():
        location = f"topics.json.topics[{identifier}]"
        validation.keys(topic, properties, required, location)
        require_inline_text(topic.get("description"), f"{location}.description", validation)
        require_inline_text(topic.get("label"), f"{location}.label", validation)
    return topics


def expected_module(source_path: str) -> str:
    """Convert a repository Lean path to its module name."""
    return source_path.removesuffix(".lean").replace("/", ".")


def source_declares(path: Path, kind: str, lean_name: str) -> bool:
    """Check source syntax for the stated fully qualified declaration name."""
    keyword = "def" if kind == "definition" else kind
    try:
        source = path.read_text(encoding="utf-8")
    except OSError:
        return False
    # Remove nested block comments while retaining newlines for command boundaries.
    cleaned: list[str] = []
    index = 0
    comment_depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            comment_depth += 1
            cleaned.extend("  ")
            index += 2
        elif comment_depth and source.startswith("-/", index):
            comment_depth -= 1
            cleaned.extend("  ")
            index += 2
        else:
            character = source[index]
            cleaned.append("\n" if comment_depth and character == "\n" else character if not comment_depth else " ")
            index += 1
    lines = [line.split("--", 1)[0] for line in "".join(cleaned).splitlines()]
    attributes = r"(?:@\[[^\]\n]*\]\s*)*"
    modifiers = r"(?:(?:private|protected|noncomputable|unsafe|public)\s+)*"
    declaration = re.compile(
        rf"^\s*{attributes}{modifiers}{re.escape(keyword)}\s+([^\s(:{{\[]+)"
    )
    command = re.compile(r"^\s*(namespace|section|end)(?:\s+([^\s]+))?")
    frames: list[tuple[str, list[str]]] = []
    for line in lines:
        command_match = command.match(line)
        if command_match:
            command_kind, command_name = command_match.groups()
            if command_kind == "namespace" and command_name:
                frames.append(("namespace", command_name.split(".")))
            elif command_kind == "section":
                frames.append(("section", []))
            elif command_kind == "end" and frames:
                frames.pop()
            continue
        declaration_match = declaration.match(line)
        if declaration_match:
            declared = declaration_match.group(1)
            namespace = [part for frame_kind, parts in frames if frame_kind == "namespace" for part in parts]
            if declared.startswith("_root_."):
                full_name = declared.removeprefix("_root_.")
            else:
                full_name = ".".join([*namespace, *declared.split(".")])
            if full_name == lean_name:
                return True
    return False


def validate_state_dimensions(record: dict[str, Any], location: str, validation: Validation) -> None:
    """Enforce exclusive implementation, coverage, and trust dimensions."""
    kind = record.get("declaration_kind")
    implementation = record.get("implementation_state")
    coverage = record.get("source_coverage")
    trust = record.get("trust_state")
    dependencies = record.get("axiom_dependencies")
    if trust == "axiom_free":
        validation.require(dependencies == [], f"{location}: axiom_free requires no dependencies")
    elif trust == "depends_on_documented_axioms":
        validation.require(
            isinstance(dependencies, list) and bool(dependencies) and kind != "axiom",
            f"{location}: dependent trust requires dependencies and a non-axiom declaration",
        )
    elif trust == "documented_axiom":
        validation.require(
            kind == "axiom"
            and implementation == "implemented"
            and dependencies == [record.get("lean_name")],
            f"{location}: documented axiom must be implemented and list exactly itself",
        )
    validation.require(
        kind != "axiom" or trust == "documented_axiom",
        f"{location}: axiom declarations require documented_axiom trust",
    )
    if implementation == "in_progress":
        validation.require(
            record.get("capstone") is False and coverage == "partial",
            f"{location}: in-progress records must be non-capstone partial coverage",
        )
    if record.get("capstone") is True:
        validation.require(
            implementation == "implemented"
            and isinstance(coverage, str)
            and coverage in {"complete", "conditional_reduction"},
            f"{location}: capstone must be implemented with complete or reduction coverage",
        )


def validate_record(
    record: dict[str, Any],
    location: str,
    contract: Contract,
    repo_root: Path,
    source_items: dict[str, dict[str, Any]],
    topic_ids: set[str],
    validation: Validation,
) -> None:
    """Validate one declaration and its status/provenance semantics."""
    properties, required = contract.object_keys("declaration_record")
    validation.keys(record, properties, required, location)
    lean_name = record.get("lean_name")
    module = record.get("module")
    source_path = record.get("source_path")
    kind = record.get("declaration_kind")
    identifier = record.get("id")
    validation.require(
        isinstance(identifier, str) and contract.stable_id.fullmatch(identifier) is not None,
        f"{location}.id: invalid stable ID",
    )
    validation.require(
        isinstance(kind, str) and kind in contract.declaration_kinds,
        f"{location}.declaration_kind: invalid",
    )
    validation.require(
        isinstance(record.get("implementation_state"), str)
        and record.get("implementation_state") in contract.implementation_states,
        f"{location}.implementation_state: invalid",
    )
    validation.require(
        isinstance(record.get("origin"), str) and record.get("origin") in contract.origins,
        f"{location}.origin: invalid",
    )
    validation.require(
        isinstance(record.get("source_coverage"), str)
        and record.get("source_coverage") in contract.source_coverages,
        f"{location}.source_coverage: invalid",
    )
    validation.require(
        isinstance(record.get("trust_state"), str)
        and record.get("trust_state") in contract.trust_states,
        f"{location}.trust_state: invalid",
    )
    validation.require(isinstance(record.get("capstone"), bool), f"{location}.capstone: expected Boolean")
    validation.require(
        isinstance(lean_name, str) and contract.lean_name.fullmatch(lean_name) is not None,
        f"{location}.lean_name: invalid fully qualified Lean name",
    )
    validation.require(
        isinstance(module, str) and contract.module_name.fullmatch(module) is not None,
        f"{location}.module: invalid module name",
    )
    validation.require(
        isinstance(source_path, str)
        and contract.source_path.fullmatch(source_path) is not None
        and ".." not in source_path,
        f"{location}.source_path: invalid Lean source path",
    )
    if isinstance(module, str) and isinstance(source_path, str):
        validation.require(module == expected_module(source_path), f"{location}: module/path mismatch")
        path = safe_relative_path(repo_root, source_path, f"{location}.source_path", validation)
        if path is not None:
            validation.require(path.is_file(), f"{location}.source_path: file does not exist")
        if path is not None and path.is_file() and isinstance(kind, str) and isinstance(lean_name, str):
            validation.require(
                source_declares(path, kind, lean_name),
                f"{location}: source does not declare {kind} {lean_name}",
            )
    dependencies = record.get("axiom_dependencies")
    require_sorted_unique_strings(dependencies, f"{location}.axiom_dependencies", validation)
    for dependency in dependencies if isinstance(dependencies, list) else []:
        validation.require(
            isinstance(dependency, str)
            and contract.lean_name.fullmatch(dependency) is not None,
            f"{location}.axiom_dependencies: invalid Lean name {dependency}",
        )
    topic_values = record.get("topic_ids")
    require_sorted_unique_strings(topic_values, f"{location}.topic_ids", validation, nonempty=True)
    for topic_id in topic_values if isinstance(topic_values, list) else []:
        validation.require(
            isinstance(topic_id, str) and topic_id in topic_ids,
            f"{location}.topic_ids: unknown {topic_id}",
        )
    require_inline_text(record.get("summary"), f"{location}.summary", validation)
    anchor = record.get("proof_guide_anchor")
    validation.require(
        anchor is None or isinstance(anchor, str) and contract.stable_id.fullmatch(anchor) is not None,
        f"{location}.proof_guide_anchor: invalid",
    )
    relations = record.get("source_relations")
    if not isinstance(relations, list):
        validation.errors.append(f"{location}.source_relations: expected array")
        relations = []
    relation_properties, relation_required = contract.object_keys("source_relation")
    pairs: list[tuple[Any, Any]] = []
    primary_count = 0
    for index, relation in enumerate(relations):
        relation_location = f"{location}.source_relations[{index}]"
        validation.keys(relation, relation_properties, relation_required, relation_location)
        if not isinstance(relation, dict):
            continue
        kind_value = relation.get("relation")
        item_id = relation.get("source_item_id")
        validation.require(
            isinstance(kind_value, str) and kind_value in contract.relation_kinds,
            f"{relation_location}.relation: invalid",
        )
        validation.require(
            isinstance(item_id, str) and item_id in source_items,
            f"{relation_location}.source_item_id: unknown",
        )
        if isinstance(kind_value, str) and isinstance(item_id, str):
            pairs.append((kind_value, item_id))
            if kind_value in {"formalizes", "presents"}:
                primary_count += 1
    validation.require(len(pairs) == len(set(pairs)), f"{location}.source_relations: duplicate relation")
    relation_order = sorted(
        pairs,
        key=lambda pair: (RELATION_RANK.get(str(pair[0]), 99), str(pair[1])),
    )
    validation.require(
        pairs == relation_order,
        f"{location}.source_relations: expected primary-first canonical relation order",
    )
    if record.get("origin") == "literature":
        validation.require(primary_count == 1, f"{location}: literature origin requires exactly one formalizes/presents relation")
        validation.require(record.get("source_coverage") != "not_applicable", f"{location}: literature coverage cannot be not_applicable")
    elif record.get("origin") == "project_original":
        validation.require(primary_count == 0, f"{location}: project-original record cannot claim a primary source")
        if record.get("implementation_state") == "implemented":
            validation.require(
                record.get("source_coverage") == "not_applicable",
                f"{location}: implemented project-original record requires not_applicable coverage",
            )
    validate_state_dimensions(record, location, validation)


def validate_dependencies(records: list[dict[str, Any]], validation: Validation) -> None:
    """Resolve every project axiom dependency to a documented-axiom record."""
    by_name = {
        record["lean_name"]: record
        for record in records
        if isinstance(record.get("lean_name"), str)
    }
    for record in records:
        dependencies = record.get("axiom_dependencies")
        if not isinstance(dependencies, list):
            validation.errors.append(f"{record.get('id')}: axiom_dependencies must be an array")
            continue
        for dependency in dependencies:
            if not isinstance(dependency, str):
                validation.errors.append(
                    f"{record.get('id')}: axiom dependency must be a string"
                )
                continue
            target = by_name.get(dependency)
            validation.require(target is not None, f"{record.get('id')}: unresolved axiom dependency {dependency}")
            if target is not None:
                validation.require(
                    target.get("declaration_kind") == "axiom"
                    and target.get("trust_state") == "documented_axiom",
                    f"{record.get('id')}: dependency is not a documented-axiom record: {dependency}",
                )


def validate_shards(
    shard_data: list[tuple[str, Any]],
    contract: Contract,
    repo_root: Path,
    sources: dict[str, dict[str, Any]],
    source_items: dict[str, dict[str, Any]],
    topics: dict[str, dict[str, Any]],
    validation: Validation,
) -> list[dict[str, Any]]:
    """Validate explicit shards and return a deterministic record array."""
    records: list[dict[str, Any]] = []
    ids: set[str] = set()
    names: set[str] = set()
    for shard_path, data in shard_data:
        if not isinstance(data, dict):
            validation.errors.append(f"{shard_path}: expected object")
            continue
        validation.keys(data, SHARD_KEYS, SHARD_KEYS, shard_path)
        validation.require(data.get("schema_version") == SCHEMA_VERSION, f"{shard_path}: bad version")
        source_id = data.get("source_id")
        validation.require(
            source_id is None or isinstance(source_id, str) and source_id in sources,
            f"{shard_path}.source_id: unknown",
        )
        require_string(data.get("source_unit"), f"{shard_path}.source_unit", validation)
        shard_records = data.get("records")
        if not isinstance(shard_records, list):
            validation.errors.append(f"{shard_path}.records: expected array")
            continue
        record_ids = [record.get("id") for record in shard_records if isinstance(record, dict)]
        if all(isinstance(identifier, str) for identifier in record_ids):
            validation.require(record_ids == sorted(record_ids), f"{shard_path}.records: sort by id")
        for index, record in enumerate(shard_records):
            location = f"{shard_path}.records[{index}]"
            if not isinstance(record, dict):
                validation.errors.append(f"{location}: expected object")
                continue
            validate_record(record, location, contract, repo_root, source_items, set(topics), validation)
            identifier = record.get("id")
            lean_name = record.get("lean_name")
            validation.require(
                not isinstance(identifier, str) or identifier not in ids,
                f"{location}.id: duplicate across shards",
            )
            validation.require(
                not isinstance(lean_name, str) or lean_name not in names,
                f"{location}.lean_name: duplicate across shards",
            )
            if isinstance(identifier, str):
                ids.add(identifier)
            if isinstance(lean_name, str):
                names.add(lean_name)
            relations = record.get("source_relations")
            if not isinstance(relations, list):
                relations = []
            primary_items = [
                source_items.get(relation["source_item_id"], {})
                for relation in relations
                if isinstance(relation, dict)
                and relation.get("relation") in {"formalizes", "presents"}
                and isinstance(relation.get("source_item_id"), str)
            ]
            if record.get("origin") == "literature" and primary_items:
                validation.require(
                    primary_items[0].get("source_id") == source_id,
                    f"{location}: shard source must own the primary source relation",
                )
            if record.get("origin") == "project_original":
                validation.require(source_id is None, f"{location}: project-original shard source must be null")
            records.append(record)
    validate_dependencies(records, validation)
    return sorted(records, key=lambda record: str(record.get("id", "")))


def validate_prototype_coverage(
    catalog_state: Any,
    shard_data: list[tuple[str, Any]],
    records: list[dict[str, Any]],
    source_items: dict[str, dict[str, Any]],
    validation: Validation,
) -> None:
    """Require representative source, capstone, and trust behavior."""
    if catalog_state != "prototype":
        return
    tasaki_units = {
        data.get("source_unit")
        for _, data in shard_data
        if isinstance(data, dict) and data.get("source_id") == "tasaki-2020"
    }
    validation.require(len(tasaki_units) >= 2, "prototype: expected two Tasaki source units")
    non_tasaki_relation = False
    non_tasaki_primary_record = False
    for record in records:
        relations = record.get("source_relations")
        if not isinstance(relations, list):
            continue
        for relation in relations:
            if not isinstance(relation, dict):
                continue
            relation_item_id = relation.get("source_item_id")
            item = source_items.get(relation_item_id, {}) if isinstance(relation_item_id, str) else {}
            relation_source_id = item.get("source_id")
            if isinstance(relation_source_id, str) and relation_source_id != "tasaki-2020":
                non_tasaki_relation = True
            if (
                relation.get("relation") in {"formalizes", "presents"}
                and isinstance(relation_source_id, str)
                and relation_source_id != "tasaki-2020"
            ):
                non_tasaki_primary_record = True
    validation.require(non_tasaki_relation, "prototype: expected a typed non-Tasaki source relation")
    validation.require(
        non_tasaki_primary_record,
        "prototype: expected a non-Tasaki source-first record with a primary relation",
    )
    validation.require(
        any(
            record.get("capstone") is True
            and record.get("implementation_state") == "implemented"
            and record.get("declaration_kind") in {"lemma", "theorem"}
            and record.get("trust_state") == "axiom_free"
            for record in records
        ),
        "prototype: expected an axiom-free proved capstone",
    )
    validation.require(
        any(record.get("trust_state") == "documented_axiom" for record in records),
        "prototype: expected a documented axiom",
    )


def input_digest(inputs: list[tuple[str, bytes]]) -> str:
    """Hash manifest-listed canonical inputs with path framing."""
    digest = hashlib.sha256()
    for path, raw in inputs:
        digest.update(path.encode("utf-8"))
        digest.update(b"\0")
        digest.update(raw)
        digest.update(b"\0")
    return digest.hexdigest()


def aggregate(
    catalog_state: str,
    digest: str,
    records: Iterable[dict[str, Any]],
    source_items: Iterable[dict[str, Any]],
    sources: Iterable[dict[str, Any]],
    topics: Iterable[dict[str, Any]],
) -> dict[str, Any]:
    """Build the stable machine aggregate with arrays sorted by stable ID."""
    return {
        "catalog_state": catalog_state,
        "generated_by": "scripts/validate_formalization_status.py",
        "generator_version": GENERATOR_VERSION,
        "input_sha256": digest,
        "records": sorted(records, key=lambda item: item["id"]),
        "schema_version": SCHEMA_VERSION,
        "source_items": sorted(source_items, key=lambda item: item["id"]),
        "sources": sorted(sources, key=lambda item: item["id"]),
        "topics": sorted(topics, key=lambda item: item["id"]),
    }


def lean_check(records: Iterable[dict[str, Any]]) -> str:
    """Generate authoritative defining-module, name, and exact axiom checks."""
    modules = sorted({record["module"] for record in records})
    declarations = sorted(
        {
            (
                record["lean_name"],
                record["module"],
                tuple(record["axiom_dependencies"]),
            )
            for record in records
        }
    )
    lines = ["import Lean", *(f"import {module}" for module in modules), ""]
    lines.extend(
        (
            "open Lean Meta Elab Command",
            "",
            "elab \"#assert_decl_module \" decl:ident \" in \" expected:ident : command => do",
            "  let env ← getEnv",
            "  let declName := decl.getId",
            "  let expectedModule := expected.getId",
            "  let some moduleIdx := env.getModuleIdxFor? declName",
            "    | throwError \"declaration has no imported defining module: {declName}\"",
            "  let actualModule := env.header.moduleNames[moduleIdx.toNat]!",
            "  unless actualModule == expectedModule do",
            "    throwError \"declaration {declName} belongs to {actualModule}, expected {expectedModule}\"",
            "",
            "/-- Require the actual non-standard axiom set to equal the declared set. -/",
            "private def assertExactAxioms (declName : Name) (expectedNames : Array Name) : CommandElabM Unit := do",
            "  let collected ← Lean.collectAxioms declName",
            "  let actual := collected.filter fun name =>",
            "    name != ``propext && name != ``Classical.choice && name != ``Quot.sound",
            "  let missing := expectedNames.filter fun name => !actual.contains name",
            "  let undeclared := actual.filter fun name => !expectedNames.contains name",
            "  unless missing.isEmpty && undeclared.isEmpty do",
            "    throwError \"axiom mismatch for {declName}; undeclared actual axioms: "
            "{undeclared}; declared but unused axioms: {missing}\"",
            "",
            "elab \"#assert_axioms \" decl:ident \" [\" expected:ident,* \"]\" : command => do",
            "  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl",
            "  assertExactAxioms declName (expected.getElems.map Syntax.getId)",
            "",
            "/-- Test fixture for the exact generated axiom gate. -/",
            "axiom FormalizationStatusGateFixture.dependency : True",
            "",
            "/-- Test fixture whose dependency set is exactly one project axiom. -/",
            "theorem FormalizationStatusGateFixture.consumer : True :=",
            "  FormalizationStatusGateFixture.dependency",
            "",
            "/-- A second fixture used to reject a declared but unused dependency. -/",
            "axiom FormalizationStatusGateFixture.unused : True",
            "",
            "#assert_axioms FormalizationStatusGateFixture.consumer [FormalizationStatusGateFixture.dependency]",
            "",
            "elab \"#self_test_exact_axiom_gate\" : command => do",
            "  let undeclaredRejected ← try",
            "    assertExactAxioms ``FormalizationStatusGateFixture.consumer #[]",
            "    pure false",
            "  catch _ => pure true",
            "  let unusedRejected ← try",
            "    assertExactAxioms ``FormalizationStatusGateFixture.consumer",
            "      #[``FormalizationStatusGateFixture.dependency, ``FormalizationStatusGateFixture.unused]",
            "    pure false",
            "  catch _ => pure true",
            "  unless undeclaredRejected && unusedRejected do",
            "    throwError \"exact axiom gate negative fixtures were not rejected\"",
            "",
            "#self_test_exact_axiom_gate",
            "",
        )
    )
    for name, module, dependencies in declarations:
        dependency_list = ", ".join(dependencies)
        lines.extend(
            (
                f"#assert_decl_module {name} in {module}",
                f"#check {name}",
                f"#assert_axioms {name} [{dependency_list}]",
                f"#print axioms {name}",
            )
        )
    lines.append("")
    return "\n".join(lines)


def write_output(path: Path, text: str) -> None:
    """Write deterministic generated scratch output."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as output:
        output.write(text)


def run_self_tests(contract: Contract, repo_root: Path) -> list[str]:
    """Run dependency-free positive, negative, and schema-parity regressions."""
    failures: list[str] = []

    def check(condition: bool, message: str) -> None:
        if not condition:
            failures.append(message)

    exact_gate_fixture = lean_check(
        [
            {
                "axiom_dependencies": ["LatticeSystem.Axiom.fact"],
                "lean_name": "LatticeSystem.Consumer.result",
                "module": "LatticeSystem.Consumer",
            }
        ]
    )
    check("Lean.collectAxioms" in exact_gate_fixture, "generated Lean lacks actual axiom collection")
    check(
        "#assert_axioms LatticeSystem.Consumer.result [LatticeSystem.Axiom.fact]"
        in exact_gate_fixture,
        "generated Lean lacks the declared exact dependency set",
    )
    check("#self_test_exact_axiom_gate" in exact_gate_fixture, "generated Lean lacks negative gate fixtures")
    check("erase ``sorryAx" not in exact_gate_fixture, "generated Lean incorrectly ignores sorryAx")

    check(contract.lean_name.fullmatch("LatticeSystem.Quantum.state'") is not None, "apostrophe Lean name rejected")
    check(contract.lean_name.fullmatch("LatticeSystem.Quantum.σ_mul") is not None, "Unicode Lean name rejected")
    for bad_name in (
        "pauliX_mul_self",
        "LatticeSystem.Quantum.foo*",
        "LatticeSystem.Quantum.foo{1}",
        "LatticeSystem/Quantum/foo",
    ):
        check(contract.lean_name.fullmatch(bad_name) is None, f"invalid Lean name accepted: {bad_name}")
    check(
        source_declares(
            repo_root / "LatticeSystem/Lattice/Scale.lean",
            "definition",
            "LatticeSystem.Lattice.spacingOf",
        ),
        "same-line @[simp] def spacingOf was not detected",
    )
    duplicate_name = (
        "LatticeSystem.Quantum.InfiniteSpinSystem.IsPhysicalGroundState."
        "boxLocalHamiltonian_apply"
    )
    check(
        source_declares(
            repo_root / "LatticeSystem/Quantum/SpinS/PhysicalGroundStateConsequences.lean",
            "theorem",
            duplicate_name,
        ),
        "fully qualified duplicate-name fixture was not found in its defining file",
    )
    check(
        not source_declares(
            repo_root / "LatticeSystem/Quantum/SpinS/BoxLocalEnergyDensity.lean",
            "theorem",
            duplicate_name,
        ),
        "terminal-name collision was accepted from the wrong namespace and file",
    )
    value = {"b": 1, "a": 2}
    check(canonical_json(json.loads(canonical_json(value))) == canonical_json(value), "canonical JSON unstable")
    order_validation = Validation()
    check(
        require_unique_strings_preserve_order(
            ["4.1.9", "4.1.10"],
            "equations",
            order_validation,
        ),
        "semantic equation order rejected",
    )
    check(not order_validation.errors, "semantic equation order produced errors")
    unknown_validation = Validation()
    unknown_validation.keys({"id": "x", "unknown": 1}, {"id"}, {"id"}, "fixture")
    check(unknown_validation.errors == ["fixture: unknown fields: unknown"], "unknown field not rejected")
    state_validation = Validation()
    validate_state_dimensions(
        {
            "axiom_dependencies": [],
            "capstone": True,
            "declaration_kind": "theorem",
            "implementation_state": "implemented",
            "source_coverage": "complete",
            "trust_state": "axiom_free",
        },
        "fixture",
        state_validation,
    )
    check(not state_validation.errors, "valid orthogonal state rejected")
    bad_state = Validation()
    validate_state_dimensions(
        {
            "axiom_dependencies": ["LatticeSystem.bad"],
            "capstone": False,
            "declaration_kind": "theorem",
            "implementation_state": "implemented",
            "source_coverage": "complete",
            "trust_state": "axiom_free",
        },
        "fixture",
        bad_state,
    )
    check(bool(bad_state.errors), "invalid trust/dependency combination accepted")
    source_validation = Validation()
    validate_sources(
        {
            "schema_version": 1,
            "sources": [
                {
                    "authors": ["A. Author"],
                    "id": "older-source-1900",
                    "year": 1900,
                }
            ],
        },
        contract,
        source_validation,
    )
    check(not source_validation.errors, "source without optional URL was rejected")
    bad_source_validation = Validation()
    validate_sources(
        {
            "schema_version": 1,
            "sources": [
                {
                    "authors": ["A. Author"],
                    "id": "bad-source-10000",
                    "url": "http://example.invalid",
                    "year": 10000,
                }
            ],
        },
        contract,
        bad_source_validation,
    )
    check(bool(bad_source_validation.errors), "bad year and non-HTTPS URL were accepted")
    dependency_validation = Validation()
    validate_dependencies(
        [
            {
                "axiom_dependencies": ["LatticeSystem.Axiom.fact"],
                "id": "consumer",
                "lean_name": "LatticeSystem.Consumer.result",
            },
            {
                "axiom_dependencies": ["LatticeSystem.Axiom.fact"],
                "declaration_kind": "axiom",
                "id": "axiom",
                "lean_name": "LatticeSystem.Axiom.fact",
                "trust_state": "documented_axiom",
            },
        ],
        dependency_validation,
    )
    check(not dependency_validation.errors, "documented axiom dependency did not resolve")
    missing_validation = Validation()
    validate_dependencies(
        [
            {
                "axiom_dependencies": ["LatticeSystem.Missing.fact"],
                "id": "consumer",
                "lean_name": "LatticeSystem.Consumer.result",
            }
        ],
        missing_validation,
    )
    check(bool(missing_validation.errors), "missing axiom dependency accepted")
    digest_prototype = input_digest(
        [("manifest.json", canonical_json({"catalog_state": "prototype"}).encode("utf-8"))]
    )
    digest_authoritative = input_digest(
        [("manifest.json", canonical_json({"catalog_state": "authoritative"}).encode("utf-8"))]
    )
    check(digest_prototype != digest_authoritative, "manifest catalog_state did not affect input digest")

    for unsafe in (
        "/etc/passwd",
        "../schema.json",
        "records/../../schema.json",
        "records//shard.json",
        "records/./shard.json",
        "records\\shard.json",
        None,
        {"not": "a-path"},
    ):
        path_validation = Validation()
        check(
            safe_relative_path(repo_root, unsafe, "fixture.path", path_validation) is None
            and bool(path_validation.errors),
            f"unsafe schema/shard path was accepted: {unsafe!r}",
        )
    wrong_schema_validation = Validation()
    check(
        safe_expected_relative_path(
            repo_root / "formalization-status" / "v1",
            "records/shastry-1992.json",
            "schema.json",
            "fixture.schema",
            wrong_schema_validation,
        )
        is None
        and bool(wrong_schema_validation.errors),
        "safe but incorrect schema path was accepted for reading",
    )
    scratch = repo_root / ".self-local" / "tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    escape_link = scratch / f"formalization-status-path-self-test-{os.getpid()}"
    try:
        escape_link.symlink_to("/etc/passwd")
        link_validation = Validation()
        relative_link = str(escape_link.relative_to(repo_root))
        check(
            safe_relative_path(repo_root, relative_link, "fixture.symlink", link_validation)
            is None
            and bool(link_validation.errors),
            "symlink escape was accepted",
        )
    except OSError as error:
        failures.append(f"could not exercise symlink path test: {error}")
    finally:
        try:
            escape_link.unlink()
        except FileNotFoundError:
            pass

    for label, mutate in (
        (
            "axiom_free maxItems",
            lambda schema: schema["$defs"]["declaration_record"]["allOf"][0]["then"][
                "properties"
            ]["axiom_dependencies"].__setitem__("maxItems", 1),
        ),
        (
            "aggregate input_sha256",
            lambda schema: schema["$defs"]["aggregate"]["properties"].pop("input_sha256"),
        ),
        (
            "source authors minItems",
            lambda schema: schema["$defs"]["source"]["properties"]["authors"].__setitem__(
                "minItems", 0
            ),
        ),
        (
            "inline text control pattern",
            lambda schema: schema["$defs"]["inline_text"].__setitem__(
                "pattern", "^unsafe$"
            ),
        ),
    ):
        mutated = copy.deepcopy(contract.schema)
        mutate(mutated)
        parity_validation = Validation()
        mutated_contract = Contract(mutated, parity_validation)
        mutated_contract.check_parity()
        check(bool(parity_validation.errors), f"schema parity mutation was accepted: {label}")

    structural_mutations: tuple[tuple[str, Any, Any, Any], ...] = (
        (
            "inline text newline pattern",
            lambda schema: schema["$defs"]["inline_text"].__setitem__("pattern", "^safe$"),
            lambda schema: schema["$defs"]["inline_text"],
            "line one\nline two",
        ),
        (
            "manifest human_publication_root pattern",
            lambda schema: schema["$defs"]["manifest"]["properties"][
                "human_publication_root"
            ].__setitem__("pattern", "^/never/$"),
            lambda schema: schema["$defs"]["manifest"]["properties"][
                "human_publication_root"
            ],
            "/lattice-system/formalization/",
        ),
        (
            "axiom_free maxItems",
            lambda schema: schema["$defs"]["declaration_record"]["allOf"][0]["then"][
                "properties"
            ]["axiom_dependencies"].__setitem__("maxItems", 0),
            lambda schema: schema["$defs"]["declaration_record"]["allOf"][0]["then"][
                "properties"
            ]["axiom_dependencies"],
            ["LatticeSystem.fixture"],
        ),
        (
            "source authors minItems",
            lambda schema: schema["$defs"]["source"]["properties"]["authors"].__setitem__(
                "minItems", 2
            ),
            lambda schema: schema["$defs"]["source"]["properties"]["authors"],
            ["A. Author"],
        ),
    )
    for label, mutate, select, fixture in structural_mutations:
        mutated = copy.deepcopy(contract.schema)
        mutate(mutated)
        structural_validation = Validation()
        validate_schema_instance(fixture, select(mutated), mutated, label, structural_validation)
        check(bool(structural_validation.errors), f"schema mutation was not enforced: {label}")

    for bad_inline in (
        "\nleading line",
        "trailing line\n",
        "line one\nline two",
        "tab\ttext",
        "control\x01text",
        "delete\x7ftext",
        "c1-control\x85text",
    ):
        inline_validation = Validation()
        require_inline_text(bad_inline, "inline fixture", inline_validation)
        check(bool(inline_validation.errors), f"inline control text was accepted: {bad_inline!r}")
        schema_inline_validation = Validation()
        validate_schema_instance(
            bad_inline,
            contract.defs["inline_text"],
            contract.schema,
            "inline fixture",
            schema_inline_validation,
        )
        check(
            bool(schema_inline_validation.errors),
            f"schema accepted inline control text: {bad_inline!r}",
        )

    for bad_url in (
        "\nhttps://example.invalid",
        "https://example.invalid\n",
        "https://example.\ninvalid",
        "https://example.invalid\x85",
        "https://example.invalid\x7f",
    ):
        semantic_url_validation = Validation()
        validate_sources(
            {
                "schema_version": 1,
                "sources": [
                    {
                        "authors": ["A. Author"],
                        "id": "url-fixture",
                        "url": bad_url,
                        "year": 2000,
                    }
                ],
            },
            contract,
            semantic_url_validation,
        )
        check(
            bool(semantic_url_validation.errors),
            f"semantic validator accepted URL control text: {bad_url!r}",
        )
        schema_url_validation = Validation()
        validate_schema_instance(
            bad_url,
            contract.defs["source"]["properties"]["url"],
            contract.schema,
            "URL fixture",
            schema_url_validation,
        )
        check(
            bool(schema_url_validation.errors),
            f"schema evaluator accepted URL control text: {bad_url!r}",
        )

    aggregate_schema = copy.deepcopy(contract.schema)
    aggregate_schema["$defs"]["aggregate"]["properties"].pop("input_sha256")
    aggregate_fixture = {
        "catalog_state": "prototype",
        "generated_by": "scripts/validate_formalization_status.py",
        "generator_version": GENERATOR_VERSION,
        "input_sha256": "0" * 64,
        "records": [],
        "schema_version": SCHEMA_VERSION,
        "source_items": [],
        "sources": [],
        "topics": [],
    }
    aggregate_validation = Validation()
    validate_schema_instance(
        aggregate_fixture,
        aggregate_schema["$defs"]["aggregate"],
        aggregate_schema,
        "aggregate mutation",
        aggregate_validation,
    )
    check(bool(aggregate_validation.errors), "deleted aggregate input_sha256 property was accepted")

    root = repo_root / "formalization-status" / "v1"
    fixture_sources = json.loads((root / "sources.json").read_text(encoding="utf-8"))
    fixture_items = json.loads((root / "source-items.json").read_text(encoding="utf-8"))
    fixture_topics = json.loads((root / "topics.json").read_text(encoding="utf-8"))
    source_map = {item["id"]: item for item in fixture_sources["sources"]}
    item_map = {item["id"]: item for item in fixture_items["source_items"]}
    topic_map = {item["id"]: item for item in fixture_topics["topics"]}
    record_fixture = json.loads(
        (root / "records/tasaki-2020-ch02.json").read_text(encoding="utf-8")
    )["records"][0]
    collision_record = copy.deepcopy(record_fixture)
    collision_record.update(
        {
            "declaration_kind": "theorem",
            "lean_name": duplicate_name,
            "module": "LatticeSystem.Quantum.SpinS.BoxLocalEnergyDensity",
            "source_path": "LatticeSystem/Quantum/SpinS/BoxLocalEnergyDensity.lean",
        }
    )
    collision_validation = Validation()
    validate_record(
        collision_record,
        "duplicate-terminal-name-record",
        contract,
        repo_root,
        item_map,
        set(topic_map),
        collision_validation,
    )
    check(
        any("source does not declare" in error for error in collision_validation.errors),
        "duplicate fully qualified name paired with the other file/module was accepted",
    )
    for field in ("axiom_dependencies", "topic_ids", "source_relations"):
        for malformed in (
            None,
            "not-an-array",
            {"not": "an-array"},
            [None],
            ["not-an-object"] if field == "source_relations" else [{"not": "a-string"}],
            [{}],
        ):
            malformed_record = copy.deepcopy(record_fixture)
            malformed_record[field] = malformed
            malformed_validation = Validation()
            validate_record(
                malformed_record,
                "malformed-record",
                contract,
                repo_root,
                item_map,
                set(topic_map),
                malformed_validation,
            )
            check(bool(malformed_validation.errors), f"malformed {field} was accepted: {malformed!r}")
    reversed_record = copy.deepcopy(record_fixture)
    reversed_record["source_relations"] = list(reversed(reversed_record["source_relations"]))
    reversed_validation = Validation()
    validate_record(
        reversed_record,
        "reversed-relations",
        contract,
        repo_root,
        item_map,
        set(topic_map),
        reversed_validation,
    )
    check(bool(reversed_validation.errors), "noncanonical source relation order was accepted")
    malformed_shard_validation = Validation()
    validate_shards(
        [
            (
                "malformed-shard",
                {
                    "records": [None, "not-an-object", {}],
                    "schema_version": 1,
                    "source_id": None,
                    "source_unit": "fixture",
                },
            )
        ],
        contract,
        repo_root,
        source_map,
        item_map,
        topic_map,
        malformed_shard_validation,
    )
    check(bool(malformed_shard_validation.errors), "malformed declarations were accepted")
    for malformed_records in (None, "not-an-array", {"not": "an-array"}):
        malformed_records_validation = Validation()
        validate_shards(
            [
                (
                    "malformed-record-array",
                    {
                        "records": malformed_records,
                        "schema_version": 1,
                        "source_id": {"not": "a-source-id"},
                        "source_unit": "fixture",
                    },
                )
            ],
            contract,
            repo_root,
            source_map,
            item_map,
            topic_map,
            malformed_records_validation,
        )
        check(
            bool(malformed_records_validation.errors),
            f"malformed declaration array accepted: {malformed_records!r}",
        )
    for malformed_registry in (None, "not-an-object", {}):
        registry_validation = Validation()
        validate_sources(malformed_registry, contract, registry_validation)
        validate_source_items(malformed_registry, contract, set(source_map), registry_validation)
        validate_topics(malformed_registry, contract, registry_validation)
        check(bool(registry_validation.errors), f"malformed registries accepted: {malformed_registry!r}")
    malformed_members_validation = Validation()
    validate_sources(
        {"schema_version": 1, "sources": [None, "not-an-object", {}]},
        contract,
        malformed_members_validation,
    )
    validate_source_items(
        {"schema_version": 1, "source_items": [None, "not-an-object", {}]},
        contract,
        set(source_map),
        malformed_members_validation,
    )
    validate_topics(
        {"schema_version": 1, "topics": [None, "not-an-object", {}]},
        contract,
        malformed_members_validation,
    )
    check(bool(malformed_members_validation.errors), "malformed registry members were accepted")

    baseline_rows = [
        {
            **row,
            "mapped_record_ids": [],
            "outcome": "not_a_declaration",
            "disposition": "non_declaration",
        }
        for row in reconstruct_legacy_rows(repo_root)
    ]
    baseline_rows[0].update(
        mapped_record_ids=["fixture-record"], outcome="mapped", disposition=None
    )
    baseline_fixture = {
        "baseline_commit": "6519099024bf156b87ac0c807c6633c513792581",
        "baseline_path": "docs/index.md",
        "cutover_record_ids": ["fixture-record"],
        "legacy_rows": baseline_rows,
        "non_legacy_record_ids": [],
        "schema_version": 1,
    }
    baseline_schema_validation = Validation()
    validate_schema_instance(
        baseline_fixture,
        contract.schema,
        contract.schema,
        "cutover baseline self-test",
        baseline_schema_validation,
    )
    check(
        not baseline_schema_validation.errors,
        "valid cutover baseline schema fixture was rejected: "
        f"{baseline_schema_validation.errors}",
    )
    for label, mutation in (
        ("short row array", lambda value: value["legacy_rows"].pop()),
        (
            "mapped row without IDs",
            lambda value: value["legacy_rows"][0].update(mapped_record_ids=[]),
        ),
        (
            "mapped row with non-record disposition",
            lambda value: value["legacy_rows"][0].update(disposition="non_declaration"),
        ),
        (
            "non-record row with mapped IDs",
            lambda value: value["legacy_rows"][1].update(mapped_record_ids=["fixture-record"]),
        ),
        (
            "non-record row without disposition",
            lambda value: value["legacy_rows"][1].update(disposition=None),
        ),
        ("unknown field", lambda value: value.update(unknown=True)),
    ):
        mutated = copy.deepcopy(baseline_fixture)
        mutation(mutated)
        mutation_validation = Validation()
        validate_schema_instance(
            mutated,
            contract.schema,
            contract.schema,
            f"cutover baseline mutation: {label}",
            mutation_validation,
        )
        check(bool(mutation_validation.errors), f"cutover schema accepted {label}")
    certificate_fixture = {
        "baseline_sha256": "0" * 64,
        "cutover_record_ids_sha256": "1" * 64,
        "exceptional_mapping_ordinals": [],
        "legacy_mapping_sha256": "2" * 64,
        "non_record_ordinals": [2],
        "schema_version": 1,
    }
    certificate_schema_validation = Validation()
    validate_schema_instance(
        certificate_fixture,
        contract.schema,
        contract.schema,
        "cutover certificate self-test",
        certificate_schema_validation,
    )
    check(
        not certificate_schema_validation.errors,
        "valid cutover certificate schema fixture was rejected: "
        f"{certificate_schema_validation.errors}",
    )
    for label, mutation in (
        ("duplicate ordinal", lambda value: value.update(non_record_ordinals=[2, 2])),
        ("out-of-range ordinal", lambda value: value.update(non_record_ordinals=[2053])),
        ("bad digest", lambda value: value.update(baseline_sha256="bad")),
        ("unknown field", lambda value: value.update(unknown=True)),
    ):
        mutated = copy.deepcopy(certificate_fixture)
        mutation(mutated)
        mutation_validation = Validation()
        validate_schema_instance(
            mutated,
            contract.schema,
            contract.schema,
            f"cutover certificate mutation: {label}",
            mutation_validation,
        )
        check(bool(mutation_validation.errors), f"cutover certificate schema accepted {label}")
    return failures


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-aggregate", type=Path, help="write deterministic aggregate JSON")
    parser.add_argument("--emit-lean-check", type=Path, help="write Lean #check/#print-axioms input")
    parser.add_argument("--self-test", action="store_true", help="run built-in contract regressions")
    return parser.parse_args()


def main() -> int:
    """Validate the version-1 catalogue and optionally emit deterministic views."""
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    root = repo_root / "formalization-status" / "v1"
    validation = Validation()
    manifest_path = root / "manifest.json"
    manifest, manifest_raw = read_json(manifest_path, validation)
    if not isinstance(manifest, dict):
        validation.errors.append("manifest.json: expected object")
        return report_errors(validation.errors)
    validation.keys(manifest, MANIFEST_KEYS, MANIFEST_REQUIRED_KEYS, "manifest.json")
    validation.require(manifest.get("schema_version") == SCHEMA_VERSION, "manifest.json: bad version")
    schema_path = manifest.get("schema")
    safe_schema_path = safe_expected_relative_path(
        root, schema_path, "schema.json", "manifest.json.schema", validation
    )
    if safe_schema_path is None:
        return report_errors(validation.errors)
    schema, schema_raw = read_json(safe_schema_path, validation)
    if not isinstance(schema, dict):
        validation.errors.append("schema.json: expected object")
        return report_errors(validation.errors)
    validation.require(
        schema.get("$schema") == "https://json-schema.org/draft/2020-12/schema",
        "schema.json: expected draft 2020-12",
    )
    contract = Contract(schema, validation)
    contract.check_parity()
    validate_schema_instance(manifest, schema, schema, "manifest.json", validation)
    if args.self_test:
        for failure in run_self_tests(contract, repo_root):
            validation.errors.append(f"self-test: {failure}")
        for failure in cutover_self_test(repo_root):
            validation.errors.append(f"cutover self-test: {failure}")
    catalog_states = contract.enum("catalog_state")
    validation.require(manifest.get("catalog_state") in catalog_states, "manifest.json: bad catalog state")
    registries = manifest.get("registries")
    validation.keys(registries, REGISTRY_KEYS, REGISTRY_KEYS, "manifest.json.registries")
    expected_registries = {
        "source_items": "source-items.json",
        "sources": "sources.json",
        "topics": "topics.json",
    }
    if not isinstance(registries, dict):
        registries = {}
    safe_registry_paths: dict[str, tuple[str, Path]] = {}
    for name, path in expected_registries.items():
        declared = registries.get(name)
        safe = safe_expected_relative_path(
            root, declared, path, f"manifest.json.registries.{name}", validation
        )
        if isinstance(declared, str) and safe is not None:
            safe_registry_paths[name] = (declared, safe)
    shards = manifest.get("record_shards")
    if not require_sorted_unique_strings(shards, "manifest.json.record_shards", validation):
        shards = []
    shard_pattern = re.compile(
        contract.defs["manifest"]["properties"]["record_shards"]["items"]["pattern"]
    )
    safe_shard_paths: dict[str, Path] = {}
    for shard in shards:
        validation.require(shard_pattern.fullmatch(shard) is not None, f"manifest: bad shard {shard}")
        safe = safe_relative_path(root, shard, "manifest.json.record_shards", validation)
        if safe is not None:
            safe_shard_paths[shard] = safe
    for field in ("human_publication_root", "machine_publication_root"):
        value = manifest.get(field)
        validation.require(
            isinstance(value, str) and value.startswith("/lattice-system/") and value.endswith("/"),
            f"manifest.json.{field}: invalid publication root",
        )
    baseline_declared = manifest.get("cutover_baseline")
    certificate_declared = manifest.get("cutover_certificate")
    validation.errors.extend(
        validate_cutover_requirement(
            manifest.get("catalog_state"), baseline_declared, certificate_declared
        )
    )
    safe_baseline_path: Path | None = None
    if baseline_declared is not None:
        safe_baseline_path = safe_expected_relative_path(
            root,
            baseline_declared,
            "cutover-baseline.json",
            "manifest.json.cutover_baseline",
            validation,
        )
    safe_certificate_path: Path | None = None
    if certificate_declared is not None:
        safe_certificate_path = safe_expected_relative_path(
            root,
            certificate_declared,
            "cutover-certificate.json",
            "manifest.json.cutover_certificate",
            validation,
        )
    listed_paths = [schema_path]
    listed_paths.extend(
        safe_registry_paths[key][0] for key in sorted(safe_registry_paths)
    )
    listed_paths.extend(shard for shard in shards if shard in safe_shard_paths)
    if isinstance(baseline_declared, str) and safe_baseline_path is not None:
        listed_paths.append(baseline_declared)
    if isinstance(certificate_declared, str) and safe_certificate_path is not None:
        listed_paths.append(certificate_declared)
    expected_json = {"manifest.json", *listed_paths}
    actual_json = {str(path.relative_to(root)) for path in root.rglob("*.json")}
    validation.require(
        actual_json == expected_json,
        f"manifest ownership mismatch: expected {sorted(expected_json)}, found {sorted(actual_json)}",
    )
    input_raw: dict[str, bytes] = {schema_path: schema_raw}
    data: dict[str, Any] = {}
    safe_listed_paths = {
        **{declared: safe for declared, safe in safe_registry_paths.values()},
        **safe_shard_paths,
    }
    if isinstance(baseline_declared, str) and safe_baseline_path is not None:
        safe_listed_paths[baseline_declared] = safe_baseline_path
    if isinstance(certificate_declared, str) and safe_certificate_path is not None:
        safe_listed_paths[certificate_declared] = safe_certificate_path
    for path in listed_paths[1:]:
        safe_path = safe_listed_paths.get(path)
        if safe_path is None:
            continue
        data[path], input_raw[path] = read_json(safe_path, validation)
        validate_schema_instance(data[path], schema, schema, path, validation)
    sources = validate_sources(data.get("sources.json"), contract, validation)
    source_items = validate_source_items(
        data.get("source-items.json"), contract, set(sources), validation
    )
    topics = validate_topics(data.get("topics.json"), contract, validation)
    shard_data = [(shard, data.get(shard)) for shard in shards]
    records = validate_shards(
        shard_data,
        contract,
        repo_root,
        sources,
        source_items,
        topics,
        validation,
    )
    if isinstance(baseline_declared, str) and isinstance(certificate_declared, str):
        baseline = data.get(baseline_declared)
        certificate = data.get(certificate_declared)
        if baseline is not None and certificate is not None:
            validation.errors.extend(
                validate_cutover_certificate(
                    certificate,
                    input_raw[certificate_declared],
                    baseline,
                    input_raw[baseline_declared],
                    manifest.get("catalog_state"),
                    records,
                )
            )
            non_record_ordinals = certificate.get("non_record_ordinals", [])
            exceptional_ordinals = certificate.get("exceptional_mapping_ordinals", [])
            for error in validate_cutover_baseline(
                baseline,
                records,
                reconstruct_legacy_rows(repo_root),
                set(non_record_ordinals) if isinstance(non_record_ordinals, list) else set(),
                set(exceptional_ordinals) if isinstance(exceptional_ordinals, list) else set(),
            ):
                validation.errors.append(error)
    validate_prototype_coverage(
        manifest.get("catalog_state"), shard_data, records, source_items, validation
    )
    if validation.errors:
        return report_errors(validation.errors)
    digest_inputs = [("manifest.json", manifest_raw)] + [
        (path, input_raw[path]) for path in listed_paths
    ]
    digest = input_digest(digest_inputs)
    result = aggregate(
        manifest["catalog_state"],
        digest,
        records,
        source_items.values(),
        sources.values(),
        topics.values(),
    )
    validate_schema_instance(result, schema, schema, "generated aggregate", validation)
    if validation.errors:
        return report_errors(validation.errors)
    serialized = canonical_json(result)
    if canonical_json(json.loads(serialized)) != serialized:
        return report_errors(["aggregate generation is not deterministic"])
    if args.emit_aggregate:
        write_output(args.emit_aggregate, serialized)
    if args.emit_lean_check:
        write_output(args.emit_lean_check, lean_check(records))
    self_test_suffix = ", self-tests passed" if args.self_test else ""
    print(
        f"formalization-status v1: valid {manifest['catalog_state']} catalogue "
        f"({len(records)} records, {len(sources)} sources, "
        f"{len(source_items)} source items, {len(topics)} topics{self_test_suffix})"
    )
    return 0


def report_errors(errors: Iterable[str]) -> int:
    """Print validation errors and return a failing exit status."""
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
