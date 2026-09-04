#!/usr/bin/env python3
"""Validate and deterministically aggregate formalization-status version 2."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable, NamedTuple

from formalization_cutover import (
    CUTOVER_BASELINE_KEYS,
    CUTOVER_CERTIFICATE_KEYS,
    CUTOVER_EXCEPTIONAL_MAPPING_KEYS,
    CUTOVER_RETIRED_DECLARATION_KEYS,
    CUTOVER_RETIRED_DECLARATION_REQUIRED_KEYS,
    LEGACY_ROW_KEYS,
    PROTOTYPE_RECORD_IDS,
    current_lean_declaration_names,
    exceptional_mapping_map,
    lean_declaration_inventory,
    project_lean_sources,
    reconstruct_legacy_rows,
    retired_declaration_map,
    self_test as cutover_self_test,
    validate_cutover_baseline,
    validate_cutover_certificate,
    validate_cutover_requirement,
)


SCHEMA_VERSION = 2
GENERATOR_VERSION = 2
# Cutover evidence is versioned independently of the catalogue: the frozen
# formalization_cutover.py validators accept only version 1 artifacts.
CUTOVER_SCHEMA_VERSION = 1
RESERVED_SOURCE_ROUTE_IDS = {"foundations", "index"}
RESERVED_TOPIC_ROUTE_IDS = {"index"}
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
RECORD_SHARD_DIRECTORY = "formalization-status/v2/records"
# A retired record describes a declaration that no longer exists, so nothing can re-measure
# these fields against the Lean tree: they stay as durable main published them while the
# record was active, and a retirement must not repoint a published ID at another declaration.
FROZEN_RECORD_FIELDS = (
    "implementation_state",
    "lean_name",
    "module",
    "source_coverage",
    "source_path",
    "trust_state",
)
_MAIN_HISTORY_REF_CACHE: dict[Path, str | None] = {}
_MAIN_RECORD_INDEX_CACHE: dict[tuple[Path, str], "MainRecordIndex"] = {}
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
# `isIdRest` of the pinned Lean toolchain (`Init/Meta/Defs.lean`), spelled as a
# regular-expression character class: ASCII alphanumerics, `_`, `'`, `!`, `?`, every
# `isLetterLike` range (Latin-1 supplement letters without the multiplication and division
# signs, Latin Extended-A, Greek without lambda, Pi and Sigma, Coptic, polytonic Greek,
# letterlike symbols, and script letters) and every `isSubScriptAlnum` range (subscript
# digits, subscript Latin letters, and subscript j). The retirement scan must end identifiers
# exactly where Lean ends them: brackets such as U+2983 and U+27E9 and the French quotes of a
# guillemet name are delimiters that must not hide a mention, while a trailing subscript,
# Greek or accented letter continues the identifier into a different name.
LEAN_IDENTIFIER_REST_CLASS = (
    "A-Za-z0-9_'!?"
    "\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
    "\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    "\u03b1-\u03ba\u03bc-\u03c9"
    "\u03ca-\u03fb"
    "\u1d62-\u1d6a"
    "\u1f00-\u1ffe"
    "\u2080-\u2089\u2090-\u209c"
    "\u2100-\u214f"
    "\u2c7c"
    "\U0001d49c-\U0001d59f"
)


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
        self.lifecycles = self.enum("lifecycle")
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
            "lifecycle",
            "module",
            "origin",
            "proof_guide_anchor",
            "retirement",
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
        expected_retirement = {"present_at_commit", "reason", "superseded_by"}
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
            (
                "cutover_exceptional_mapping",
                CUTOVER_EXCEPTIONAL_MAPPING_KEYS,
                CUTOVER_EXCEPTIONAL_MAPPING_KEYS,
            ),
            (
                "cutover_retired_declaration",
                CUTOVER_RETIRED_DECLARATION_KEYS,
                CUTOVER_RETIRED_DECLARATION_REQUIRED_KEYS,
            ),
            ("cutover_legacy_row", LEGACY_ROW_KEYS, LEGACY_ROW_KEYS),
            ("manifest", MANIFEST_KEYS, MANIFEST_REQUIRED_KEYS),
            ("record_retirement", expected_retirement, expected_retirement),
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
            self.lifecycles == {"active", "retired"},
            "schema parity: lifecycle vocabulary drifted",
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
            implication(
                "lifecycle",
                "active",
                {"properties": {"retirement": {"type": "null"}}},
            ),
            implication(
                "lifecycle",
                "retired",
                {
                    "properties": {
                        "capstone": {"const": False},
                        "retirement": {"type": "object"},
                    }
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
    """Evaluate the JSON Schema subset used by the version-2 contract."""
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
        validation.require(
            identifier not in RESERVED_SOURCE_ROUTE_IDS,
            f"{location}.id: reserved human publication route",
        )
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
        validation.require(
            identifier not in RESERVED_TOPIC_ROUTE_IDS,
            f"{location}.id: reserved human publication route",
        )
        validation.keys(topic, properties, required, location)
        require_inline_text(topic.get("description"), f"{location}.description", validation)
        require_inline_text(topic.get("label"), f"{location}.label", validation)
    return topics


def expected_module(source_path: str) -> str:
    """Convert a repository Lean path to its module name."""
    return source_path.removesuffix(".lean").replace("/", ".")


def declaration_in_source(source: str, kind: str, lean_name: str) -> bool:
    """Check one Lean source text for the stated fully qualified declaration."""
    keyword = "def" if kind == "definition" else kind
    return keyword in lean_declaration_inventory(source).get(lean_name, set())


def source_declares(path: Path, kind: str, lean_name: str) -> bool:
    """Check source syntax for the stated fully qualified declaration name."""
    try:
        source = path.read_text(encoding="utf-8")
    except OSError:
        return False
    return declaration_in_source(source, kind, lean_name)


def lean_leaf_mention(repo_root: Path, lean_name: str) -> str | None:
    """Return one Lean source that still spells the declaration's short name, if any."""
    leaf = lean_name.rsplit(".", 1)[-1]
    pattern = re.compile(
        f"(?<![{LEAN_IDENTIFIER_REST_CLASS}]){re.escape(leaf)}(?![{LEAN_IDENTIFIER_REST_CLASS}])"
    )
    for source_path in project_lean_sources(repo_root):
        try:
            source = source_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if pattern.search(source):
            return source_path.relative_to(repo_root).as_posix()
    return None


def git_capture(repo_root: Path, arguments: list[str]) -> subprocess.CompletedProcess[str]:
    """Run one read-only Git query from the repository root."""
    try:
        return subprocess.run(
            ["git", *arguments],
            cwd=repo_root,
            check=False,
            capture_output=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError as error:
        # An absent Git binary or unreadable repository path is a failed query, not a crash:
        # callers turn it into a validation error instead of a traceback.
        return subprocess.CompletedProcess(["git", *arguments], 1, "", str(error))


def main_history_ref(repo_root: Path) -> str | None:
    """Resolve the durable main-branch ref that retirement evidence is measured against."""
    # Every record in a catalogue resolves the same ref against the same checkout, so the
    # answer is kept rather than re-spawned once per record.
    resolved_root = repo_root.resolve()
    if resolved_root not in _MAIN_HISTORY_REF_CACHE:
        _MAIN_HISTORY_REF_CACHE[resolved_root] = read_main_history_ref(repo_root)
    return _MAIN_HISTORY_REF_CACHE[resolved_root]


def read_main_history_ref(repo_root: Path) -> str | None:
    """Return the first durable main-branch ref that resolves in this checkout."""
    for ref in ("origin/main", "main"):
        resolved = git_capture(repo_root, ["rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}"])
        if resolved.returncode == 0:
            return ref
    return None


class MainRecordIndex(NamedTuple):
    """Records durable main history publishes, and the shard that could not be read."""

    records: dict[str, dict[str, Any]]
    unreadable: str | None


def main_record_index(repo_root: Path, history_ref: str) -> MainRecordIndex:
    """Index the records durable main history publishes."""
    # Every record asks the same question of the same already-merged history, and each answer
    # costs one `git ls-tree` plus one `git show` per shard, so a catalogue with many retired
    # records would otherwise spend several Git subprocesses per record.
    cache_key = (repo_root.resolve(), history_ref)
    if cache_key not in _MAIN_RECORD_INDEX_CACHE:
        _MAIN_RECORD_INDEX_CACHE[cache_key] = read_main_record_index(repo_root, history_ref)
    return _MAIN_RECORD_INDEX_CACHE[cache_key]


def record_comparison_base(repo_root: Path, history_ref: str) -> str:
    """Return the commit whose published records a candidate catalogue is measured against."""
    # A run whose HEAD is the resolved ref's own commit is validating what main just published:
    # measuring against the ref itself would compare that commit with itself, so a reversal or a
    # frozen-field drift landing directly on main could never be seen. The durable state is the
    # ref's first parent, which is the commit main published before this one for a squash merge
    # and for a merge commit alike. A first commit has no such parent, and nothing precedes it
    # that self-comparison could hide.
    head = git_capture(repo_root, ["rev-parse", "--verify", "--quiet", "HEAD^{commit}"])
    resolved = git_capture(
        repo_root, ["rev-parse", "--verify", "--quiet", f"{history_ref}^{{commit}}"]
    )
    if head.returncode != 0 or resolved.returncode != 0:
        return history_ref
    if head.stdout.strip() != resolved.stdout.strip():
        return history_ref
    parent = git_capture(
        repo_root, ["rev-parse", "--verify", "--quiet", f"{history_ref}^{{commit}}^"]
    )
    if parent.returncode != 0:
        return history_ref
    return parent.stdout.strip()


def read_main_record_index(repo_root: Path, history_ref: str) -> MainRecordIndex:
    """Read every record shard the durable history behind this checkout publishes."""
    # History that publishes no shard tree yet and history whose shards cannot be read are
    # different answers, and only the first is a legitimate bootstrap: an absent tree yields an
    # empty readable index, while every listing, read, or parse failure names its shard so a
    # caller can fail closed instead of mistaking an anomaly for a catalogue with no records.
    base = record_comparison_base(repo_root, history_ref)
    listing = git_capture(
        repo_root, ["ls-tree", "--name-only", base, f"{RECORD_SHARD_DIRECTORY}/"]
    )
    if listing.returncode != 0:
        return MainRecordIndex(
            {}, f"record shards under {RECORD_SHARD_DIRECTORY} cannot be listed on {base}"
        )
    shard_paths = sorted(
        line for line in listing.stdout.splitlines() if line.endswith(".json")
    )
    index: dict[str, dict[str, Any]] = {}
    for shard_path in shard_paths:
        blob = git_capture(repo_root, ["show", f"{base}:{shard_path}"])
        if blob.returncode != 0:
            return MainRecordIndex(
                {}, f"record shard {shard_path} cannot be read on {base}"
            )
        try:
            shard = json.loads(blob.stdout)
        except json.JSONDecodeError:
            return MainRecordIndex(
                {}, f"record shard {shard_path} on {base} is not valid JSON"
            )
        if not isinstance(shard, dict):
            return MainRecordIndex(
                {}, f"record shard {shard_path} on {base} is not a JSON object"
            )
        records = shard.get("records")
        if not isinstance(records, list):
            return MainRecordIndex(
                {}, f"record shard {shard_path} on {base} has no records array"
            )
        for published in records:
            identifier = published.get("id") if isinstance(published, dict) else None
            if isinstance(identifier, str):
                index[identifier] = published
    return MainRecordIndex(index, None)


def retired_supersession_targets(record: dict[str, Any]) -> list[str]:
    """Return the record IDs one retired record names as its replacements."""
    if record.get("lifecycle") != "retired":
        return []
    retirement = record.get("retirement")
    if not isinstance(retirement, dict):
        return []
    superseded = retirement.get("superseded_by")
    if not isinstance(superseded, list):
        return []
    return [entry for entry in superseded if isinstance(entry, str)]


def supersession_cycle(
    record: dict[str, Any], identifier: str, records_by_id: dict[str, dict[str, Any]]
) -> list[str] | None:
    """Return the supersession path leading a retired record back to its own ID, if any."""
    # A published supersession may never be dropped, so a cycle merged once could never be
    # corrected: it would leave every record on it pointing at a replacement that is itself
    # retired, with no live declaration anywhere along the chain.
    pending = [(target, [identifier, target]) for target in retired_supersession_targets(record)]
    visited: set[str] = set()
    while pending:
        current, path = pending.pop()
        if current == identifier:
            return path
        if current in visited:
            continue
        visited.add(current)
        following = records_by_id.get(current)
        if not isinstance(following, dict):
            continue
        pending.extend(
            (target, [*path, target]) for target in retired_supersession_targets(following)
        )
    return None


def validate_frozen_identity(
    record: dict[str, Any],
    identifier: str,
    location: str,
    history_ref: str,
    repo_root: Path,
    validation: Validation,
) -> None:
    """Hold a retiring record to the identity durable main history published for its ID."""
    published = main_record_index(repo_root, history_ref)
    if published.unreadable is not None:
        validation.errors.append(
            f"{location}: {identifier}: {published.unreadable}, so the frozen fields of a "
            "retired record cannot be proven"
        )
        return
    former = published.records.get(identifier)
    if former is None:
        validation.errors.append(
            f"{location}: {identifier} is absent from every record shard on {history_ref}, "
            "so the frozen fields of a retired record cannot be proven"
        )
        return
    for field in FROZEN_RECORD_FIELDS:
        validation.require(
            record.get(field) == former.get(field),
            f"{location}: {identifier}: frozen field {field} is {record.get(field)!r}, "
            f"not the {former.get(field)!r} published on {history_ref}",
        )
    if former.get("lifecycle") != "retired":
        return
    # Durable main history already settled which commit is the record's proof, and nothing can
    # re-measure it, so the pinned commit is frozen too. The prose and the supersession list
    # stay open: a reason may be corrected, and a replacement declaration may only be written
    # after the retirement merged, but a supersession that history already publishes must not
    # silently disappear.
    retirement = record.get("retirement")
    retirement = retirement if isinstance(retirement, dict) else {}
    former_retirement = former.get("retirement")
    former_retirement = former_retirement if isinstance(former_retirement, dict) else {}
    validation.require(
        retirement.get("present_at_commit") == former_retirement.get("present_at_commit"),
        f"{location}: {identifier}: frozen field retirement.present_at_commit is "
        f"{retirement.get('present_at_commit')!r}, not the "
        f"{former_retirement.get('present_at_commit')!r} published on {history_ref}",
    )
    superseded = retirement.get("superseded_by")
    former_superseded = former_retirement.get("superseded_by")
    former_entries = former_superseded if isinstance(former_superseded, list) else []
    # A published shard is arbitrary data here, not a catalogue this run validated, so an entry
    # of the wrong type must name the record it came from rather than reach the comparison and
    # raise out of the validator.
    validation.require(
        all(isinstance(entry, str) for entry in former_entries),
        f"{location}: {identifier}: {history_ref} publishes a retirement.superseded_by entry "
        "that is not a record ID string, so its supersessions cannot be compared",
    )
    dropped = sorted(
        {entry for entry in former_entries if isinstance(entry, str)}
        - {
            entry
            for entry in (superseded if isinstance(superseded, list) else [])
            if isinstance(entry, str)
        }
    )
    validation.require(
        not dropped,
        f"{location}: {identifier}: retirement.superseded_by no longer lists "
        f"{', '.join(dropped)}, which {history_ref} publishes for this retired record",
    )


def reject_retirement_reversal(
    record: dict[str, Any],
    location: str,
    repo_root: Path,
    validation: Validation,
) -> None:
    """Keep an ID durable main history publishes as retired out of the active catalogue."""
    identifier = record.get("id")
    if not isinstance(identifier, str):
        return
    # Readable history that publishes no record shard tree leaves this guard silent, because a
    # catalogue must be able to publish its first records before any exist on main. Every other
    # unanswerable case fails closed here as it does on the retired path: an unresolvable ref or
    # an unreadable shard would otherwise switch the guard off for every record without saying
    # so.
    history_ref = main_history_ref(repo_root)
    if history_ref is None:
        validation.errors.append(
            f"{location}: {identifier}: neither origin/main nor main resolves, so a retirement "
            "that history may already publish for this ID cannot be ruled out"
        )
        return
    published = main_record_index(repo_root, history_ref)
    if published.unreadable is not None:
        validation.errors.append(
            f"{location}: {identifier}: {published.unreadable}, so a retirement that history "
            "may already publish for this ID cannot be ruled out"
        )
        return
    former = published.records.get(identifier)
    if not isinstance(former, dict) or former.get("lifecycle") != "retired":
        return
    validation.errors.append(
        f"{location}: {identifier} is retired on {history_ref}: retirement is terminal, "
        "so the ID cannot return to the active catalogue"
    )


def validate_retirement(
    record: dict[str, Any],
    location: str,
    contract: Contract,
    repo_root: Path,
    records_by_id: dict[str, dict[str, Any]],
    validation: Validation,
) -> None:
    """Enforce the lifecycle axis and history-proven retirement evidence."""
    lifecycle = record.get("lifecycle")
    validation.require(
        isinstance(lifecycle, str) and lifecycle in contract.lifecycles,
        f"{location}.lifecycle: invalid",
    )
    retirement = record.get("retirement")
    if lifecycle != "retired":
        validation.require(
            retirement is None,
            f"{location}: an active record must not carry retirement evidence",
        )
        reject_retirement_reversal(record, location, repo_root, validation)
        return
    validation.require(
        record.get("capstone") is False,
        f"{location}: a retired record cannot be a capstone",
    )
    if not isinstance(retirement, dict):
        validation.errors.append(
            f"{location}: a retired record requires retirement evidence"
        )
        return
    properties, required = contract.object_keys("record_retirement")
    validation.keys(retirement, properties, required, f"{location}.retirement")
    require_inline_text(retirement.get("reason"), f"{location}.retirement.reason", validation)
    superseded = retirement.get("superseded_by")
    if not isinstance(superseded, list) or not all(
        isinstance(identifier, str) for identifier in superseded
    ):
        validation.errors.append(
            f"{location}.retirement.superseded_by: expected an array of record IDs"
        )
    else:
        validation.require(
            superseded == sorted(set(superseded)),
            f"{location}.retirement.superseded_by: expected sorted unique record IDs",
        )
        # A replacement may itself be retired later, and a published supersession may never be
        # dropped, so requiring the target to stay active would leave the pair unsatisfiable
        # from that point on: the target only has to exist in the catalogue, and only has to be
        # a record other than this one, reached without returning here.
        for identifier in superseded:
            validation.require(
                identifier in records_by_id,
                f"{location}.retirement.superseded_by: unresolved superseded_by "
                f"record {identifier}",
            )
        record_identifier = record.get("id")
        if isinstance(record_identifier, str):
            if record_identifier in superseded:
                validation.errors.append(
                    f"{location}.retirement.superseded_by: a retired record cannot supersede "
                    f"itself: {record_identifier}"
                )
            else:
                cycle = supersession_cycle(record, record_identifier, records_by_id)
                if cycle is not None:
                    validation.errors.append(
                        f"{location}.retirement.superseded_by: supersession cycle through "
                        f"retired records: {' -> '.join(cycle)}"
                    )
    # The retiring change and its evidence land together, and this repository
    # squash-merges, so the pinned commit is one whose tree still contained the declaration
    # rather than the one that deleted it. Squash merges also discard branch commits, so
    # both the ancestry of that commit and the frozen identity below are measured against
    # durable main history: evidence that only the pull-request branch reaches would pass
    # here and fail forever once merged.
    history_ref = main_history_ref(repo_root)
    if history_ref is None:
        validation.errors.append(
            f"{location}.retirement.present_at_commit: neither origin/main nor main "
            "resolves, so ancestry cannot be proven"
        )
        return
    record_id = record.get("id")
    if isinstance(record_id, str):
        # A malformed commit must not buy silence about the record's identity, so the
        # frozen comparison runs before the evidence itself is inspected.
        validate_frozen_identity(record, record_id, location, history_ref, repo_root, validation)
    commit = retirement.get("present_at_commit")
    if not isinstance(commit, str) or re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        validation.errors.append(
            f"{location}.retirement.present_at_commit: expected one 40-character commit ID"
        )
        return
    if git_capture(repo_root, ["merge-base", "--is-ancestor", commit, history_ref]).returncode != 0:
        validation.errors.append(
            f"{location}.retirement.present_at_commit: commit is not an ancestor of "
            f"{history_ref}"
        )
        return
    kind = record.get("declaration_kind")
    lean_name = record.get("lean_name")
    source_path = record.get("source_path")
    if (
        not isinstance(kind, str)
        or not isinstance(lean_name, str)
        or not isinstance(source_path, str)
    ):
        return
    blob = git_capture(repo_root, ["show", f"{commit}:{source_path}"])
    if blob.returncode != 0 or not declaration_in_source(blob.stdout, kind, lean_name):
        validation.errors.append(
            f"{location}.retirement.present_at_commit: tree does not declare "
            f"{kind} {lean_name} at {source_path}"
        )


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
    records_by_id: dict[str, dict[str, Any]] | None = None,
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
    retired = record.get("lifecycle") == "retired"
    if isinstance(module, str) and isinstance(source_path, str):
        validation.require(module == expected_module(source_path), f"{location}: module/path mismatch")
        path = safe_relative_path(repo_root, source_path, f"{location}.source_path", validation)
        if retired:
            if isinstance(kind, str) and isinstance(lean_name, str):
                # The declaration matcher recognizes only a fixed modifier set, so it misses
                # `nonrec`, `partial`, `scoped instance` and similar live forms; absence is
                # therefore proven by the broader whole-word scan, which fails closed.
                mention = lean_leaf_mention(repo_root, lean_name)
                declared = lean_name in current_lean_declaration_names(repo_root) or (
                    path is not None
                    and path.is_file()
                    and source_declares(path, kind, lean_name)
                )
                if declared or mention is not None:
                    where = f" in {mention}" if mention is not None else ""
                    validation.errors.append(
                        f"{location}: a retired record's Lean name is still declared or "
                        f"mentioned: {lean_name}{where}"
                    )
        else:
            if path is not None:
                validation.require(path.is_file(), f"{location}.source_path: file does not exist")
            if (
                path is not None
                and path.is_file()
                and isinstance(kind, str)
                and isinstance(lean_name, str)
            ):
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
    validate_retirement(
        record, location, contract, repo_root, records_by_id or {}, validation
    )


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
                validation.require(
                    record.get("lifecycle") == "retired"
                    or target.get("lifecycle") != "retired",
                    f"{record.get('id')}: active record depends on a retired "
                    f"declaration: {dependency}",
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
    records_by_id = {
        record["id"]: record
        for _, data in shard_data
        if isinstance(data, dict) and isinstance(data.get("records"), list)
        for record in data["records"]
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    }
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
            validate_record(
                record,
                location,
                contract,
                repo_root,
                source_items,
                set(topics),
                validation,
                records_by_id,
            )
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
    records = [record for record in records if record.get("lifecycle") != "retired"]
    active_ids = {record.get("id") for record in records}
    tasaki_units = {
        data.get("source_unit")
        for _, data in shard_data
        if isinstance(data, dict)
        and data.get("source_id") == "tasaki-2020"
        and any(
            isinstance(record, dict) and record.get("id") in active_ids
            for record in data.get("records") or []
        )
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


def validate_prototype_pin(record_ids: Iterable[str], validation: Validation) -> None:
    """Require the catalogue to retain every pinned prototype record ID."""
    missing = sorted(PROTOTYPE_RECORD_IDS - set(record_ids))
    validation.require(
        not missing,
        f"catalogue removed pinned prototype record IDs: {', '.join(missing)}",
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
    # A retired record describes a declaration that no longer exists, so neither its
    # assertions nor its import may reach the generated file.
    active = [record for record in records if record.get("lifecycle") != "retired"]
    modules = sorted({record["module"] for record in active})
    declarations = sorted(
        {
            (
                record["lean_name"],
                record["module"],
                tuple(record["axiom_dependencies"]),
            )
            for record in active
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
    parser_fixture = """
namespace LatticeSystem
namespace Fixture
section Inner
@[simp] private noncomputable theorem attributedResult : True := by trivial
end Inner
namespace Nested
protected def value : Nat := 0
end Nested
end Fixture
end LatticeSystem
"""
    parser_inventory = lean_declaration_inventory(parser_fixture)
    check(
        "theorem"
        in parser_inventory.get("LatticeSystem.Fixture.attributedResult", set()),
        "shared inventory missed same-line attributes/modifiers in a nested namespace",
    )
    check(
        "def" in parser_inventory.get("LatticeSystem.Fixture.Nested.value", set()),
        "shared inventory missed a protected declaration in a nested namespace",
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
            "schema_version": SCHEMA_VERSION,
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
            "schema_version": SCHEMA_VERSION,
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
    for reserved in sorted(RESERVED_SOURCE_ROUTE_IDS):
        reserved_validation = Validation()
        validate_sources(
            {
                "schema_version": SCHEMA_VERSION,
                "sources": [
                    {
                        "authors": ["A. Author"],
                        "id": reserved,
                        "year": 2000,
                    }
                ],
            },
            contract,
            reserved_validation,
        )
        check(
            bool(reserved_validation.errors),
            f"reserved source publication route was accepted: {reserved}",
        )
    reserved_topic_validation = Validation()
    validate_topics(
        {
            "schema_version": SCHEMA_VERSION,
            "topics": [
                {
                    "description": "Reserved route fixture",
                    "id": "index",
                    "label": "Reserved",
                }
            ],
        },
        contract,
        reserved_topic_validation,
    )
    check(
        bool(reserved_topic_validation.errors),
        "reserved topic publication route was accepted: index",
    )
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
            repo_root / "formalization-status" / "v2",
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
                "schema_version": SCHEMA_VERSION,
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

    root = repo_root / "formalization-status" / "v2"
    fixture_sources = json.loads((root / "sources.json").read_text(encoding="utf-8"))
    fixture_items = json.loads((root / "source-items.json").read_text(encoding="utf-8"))
    fixture_topics = json.loads((root / "topics.json").read_text(encoding="utf-8"))
    source_map = {item["id"]: item for item in fixture_sources["sources"]}
    item_map = {item["id"]: item for item in fixture_items["source_items"]}
    topic_map = {item["id"]: item for item in fixture_topics["topics"]}
    ch02_records = json.loads(
        (root / "records/tasaki-2020-ch02.json").read_text(encoding="utf-8")
    )["records"]
    check(bool(ch02_records), "tasaki-2020-ch02.json holds no record to build fixtures from")
    # An emptied shard must still reach the pinned-record check in the main validation rather
    # than abort the run here.
    record_fixture = ch02_records[0] if ch02_records else {"source_relations": []}
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
                    "schema_version": SCHEMA_VERSION,
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
                        "schema_version": SCHEMA_VERSION,
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
    version_one_shard_validation = Validation()
    validate_shards(
        [
            (
                "version-one-shard",
                {
                    "records": [],
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
        version_one_shard_validation,
    )
    check(
        any("bad version" in error for error in version_one_shard_validation.errors),
        "a version 1 shard was accepted by the version 2 reader",
    )
    for malformed_registry in (None, "not-an-object", {}):
        registry_validation = Validation()
        validate_sources(malformed_registry, contract, registry_validation)
        validate_source_items(malformed_registry, contract, set(source_map), registry_validation)
        validate_topics(malformed_registry, contract, registry_validation)
        check(bool(registry_validation.errors), f"malformed registries accepted: {malformed_registry!r}")
    malformed_members_validation = Validation()
    validate_sources(
        {"schema_version": SCHEMA_VERSION, "sources": [None, "not-an-object", {}]},
        contract,
        malformed_members_validation,
    )
    validate_source_items(
        {"schema_version": SCHEMA_VERSION, "source_items": [None, "not-an-object", {}]},
        contract,
        set(source_map),
        malformed_members_validation,
    )
    validate_topics(
        {"schema_version": SCHEMA_VERSION, "topics": [None, "not-an-object", {}]},
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
    baseline_rows[2].update(
        mapped_record_ids=[],
        outcome="retired",
        disposition="retired_declarations",
    )
    baseline_fixture = {
        "baseline_commit": "6519099024bf156b87ac0c807c6633c513792581",
        "baseline_path": "docs/index.md",
        "cutover_record_ids": ["fixture-record"],
        "legacy_rows": baseline_rows,
        "non_legacy_record_ids": [],
        "schema_version": CUTOVER_SCHEMA_VERSION,
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
            "mapped row with retired disposition",
            lambda value: value["legacy_rows"][0].update(
                disposition="retired_declarations"
            ),
        ),
        (
            "non-record row with mapped IDs",
            lambda value: value["legacy_rows"][1].update(mapped_record_ids=["fixture-record"]),
        ),
        (
            "non-record row without disposition",
            lambda value: value["legacy_rows"][1].update(disposition=None),
        ),
        (
            "unclosed waived disposition",
            lambda value: value["legacy_rows"][1].update(disposition="waived"),
        ),
        (
            "non-record row with retired disposition",
            lambda value: value["legacy_rows"][1].update(
                disposition="retired_declarations"
            ),
        ),
        (
            "retired row with mapped IDs",
            lambda value: value["legacy_rows"][2].update(
                mapped_record_ids=["fixture-record"]
            ),
        ),
        (
            "retired row without retired disposition",
            lambda value: value["legacy_rows"][2].update(disposition=None),
        ),
        (
            "unknown grouping syntax",
            lambda value: value["legacy_rows"][1].update(
                legacy_grouping_syntax=["unknown"]
            ),
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
        "exceptional_mappings": [],
        "legacy_mapping_sha256": "2" * 64,
        "non_record_ordinals": [2],
        "retired_declarations": [],
        "schema_version": CUTOVER_SCHEMA_VERSION,
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
        (
            "malformed exceptional mapping",
            lambda value: value.update(
                exceptional_mappings=[
                    {
                        "expected_lean_names": ["not-qualified"],
                        "ordinal": 1,
                        "row_sha256": "0" * 64,
                    }
                ]
            ),
        ),
        (
            "malformed retired declaration",
            lambda value: value.update(
                retired_declarations=[
                    {
                        "deletion_commit": "0" * 40,
                        "former_lean_name": "not a name",
                        "former_path": "outside.lean",
                        "legacy_leaf": "bad leaf",
                        "ordinal": 1,
                        "reason": "",
                        "row_sha256": "0" * 64,
                    }
                ]
            ),
        ),
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

    # -- retirement / lifecycle regressions --------------------------------------------------
    # Each check asserts on the specific retirement message rather than on `bool(errors)`,
    # so a fixture cannot pass because of an unrelated structural rejection.
    def with_record_overrides(overrides: dict[str, Any]) -> dict[str, Any]:
        """Build a v2-shaped record fixture from the real Pauli-involution record."""
        record = copy.deepcopy(record_fixture)
        record.update(overrides)
        return record

    def record_errors(
        record: dict[str, Any],
        location: str,
        records_by_id: dict[str, dict[str, Any]] | None = None,
    ) -> list[str]:
        """Validate one fixture record against an optional fixture catalogue."""
        record_validation = Validation()
        validate_record(
            record,
            location,
            contract,
            repo_root,
            item_map,
            set(topic_map),
            record_validation,
            records_by_id,
        )
        return record_validation.errors

    active_record_errors = record_errors(
        with_record_overrides({"lifecycle": "active", "retirement": None}),
        "active-record",
    )
    check(
        not active_record_errors,
        "a record with lifecycle=active and retirement=null was rejected "
        f"(positive control): {active_record_errors}",
    )

    retirement_evidence = {
        "present_at_commit": "7b65d59ec539b195d449bd97f94b08dbf99bf66e",
        "reason": "superseded by a directly proved converse",
        "superseded_by": [],
    }
    retired_but_present_errors = record_errors(
        with_record_overrides(
            {
                "declaration_kind": "definition",
                "lean_name": "LatticeSystem.Lattice.spacingOf",
                "lifecycle": "retired",
                "module": "LatticeSystem.Lattice.Scale",
                "retirement": retirement_evidence,
                "source_path": "LatticeSystem/Lattice/Scale.lean",
            }
        ),
        "retired-but-present-record",
    )
    check(
        any("still declared" in error for error in retired_but_present_errors),
        "retired record naming a Lean declaration that still exists in the current tree "
        f"was not rejected for the intended reason: {retired_but_present_errors}",
    )

    # The location strings below are the neutral "fixture" on purpose: a descriptive
    # location (e.g. "retired-capstone-record") is echoed inside every error message for
    # that record, so its own text can satisfy a substring check against an unrelated
    # error — a green for the wrong reason.
    null_retirement_errors = record_errors(
        with_record_overrides({"lifecycle": "retired", "retirement": None}), "fixture"
    )
    check(
        any("requires retirement evidence" in error for error in null_retirement_errors),
        "retired record with retirement: null was not rejected for the intended reason: "
        f"{null_retirement_errors}",
    )
    non_null_retirement_on_active_errors = record_errors(
        with_record_overrides({"lifecycle": "active", "retirement": retirement_evidence}),
        "fixture",
    )
    check(
        any(
            "must not carry retirement evidence" in error
            for error in non_null_retirement_on_active_errors
        ),
        "active record with non-null retirement was not rejected for the intended reason: "
        f"{non_null_retirement_on_active_errors}",
    )

    retired_capstone_errors = record_errors(
        with_record_overrides(
            {"capstone": True, "lifecycle": "retired", "retirement": retirement_evidence}
        ),
        "fixture",
    )
    check(
        any("cannot be a capstone" in error for error in retired_capstone_errors),
        "retired record with capstone: true was not rejected for the intended reason: "
        f"{retired_capstone_errors}",
    )

    # Regression pin: the retirement branch must not relax the active path, where a
    # record naming a nonexistent declaration stays rejected.
    nonexistent_active_errors = record_errors(
        with_record_overrides({"lean_name": "LatticeSystem.Quantum.doesNotExistAnywhere"}),
        "nonexistent-active-record",
    )
    check(
        any("source does not declare" in error for error in nonexistent_active_errors),
        "active record naming a nonexistent declaration was accepted "
        f"(regression): {nonexistent_active_errors}",
    )

    dependency_on_retired_validation = Validation()
    validate_dependencies(
        [
            {
                "axiom_dependencies": ["LatticeSystem.Axiom.retiredFact"],
                "id": "active-consumer",
                "lean_name": "LatticeSystem.Consumer.result",
                "lifecycle": "active",
            },
            {
                "axiom_dependencies": [],
                "declaration_kind": "axiom",
                "id": "retired-axiom",
                "lean_name": "LatticeSystem.Axiom.retiredFact",
                "lifecycle": "retired",
                "trust_state": "documented_axiom",
            },
        ],
        dependency_on_retired_validation,
    )
    check(
        any(
            "active record depends on a retired declaration" in error
            for error in dependency_on_retired_validation.errors
        ),
        "active record depending on a retired declaration was not rejected for the "
        f"intended reason: {dependency_on_retired_validation.errors}",
    )

    non_ancestor_errors = record_errors(
        with_record_overrides(
            {
                "lifecycle": "retired",
                "retirement": {
                    "present_at_commit": "0" * 40,
                    "reason": "fixture: non-ancestor commit",
                    "superseded_by": [],
                },
            }
        ),
        "fixture",
    )
    check(
        any(
            "present_at_commit: commit is not an ancestor of" in error
            for error in non_ancestor_errors
        ),
        "retired record whose present_at_commit is not an ancestor of main history was "
        f"not rejected for the intended reason: {non_ancestor_errors}",
    )

    wrong_content_errors = record_errors(
        with_record_overrides(
            {
                "declaration_kind": "definition",
                "lean_name": "LatticeSystem.Lattice.NeverDeclaredAtThatCommit",
                "lifecycle": "retired",
                "module": "LatticeSystem.Lattice.Scale",
                "retirement": {
                    "present_at_commit": "7b65d59ec539b195d449bd97f94b08dbf99bf66e",
                    "reason": "fixture: commit tree does not declare this name",
                    "superseded_by": [],
                },
                "source_path": "LatticeSystem/Lattice/Scale.lean",
            }
        ),
        "fixture",
    )
    check(
        any(
            "does not declare" in error and "present_at_commit" in error
            for error in wrong_content_errors
        ),
        "retired record whose present_at_commit tree does not declare the recorded name "
        f"was not rejected for the intended reason: {wrong_content_errors}",
    )

    # Supersession resolves against the whole catalogue, so distinguishing an unknown
    # ID from one the catalogue publishes requires the record map this fixture supplies.
    superseded_catalogue = {
        "some-other-retired-record": {
            "id": "some-other-retired-record",
            "lifecycle": "retired",
        },
    }
    for label, superseded_by, expected_phrase in (
        (
            "unknown superseded_by ID",
            ["unknown-record-id-does-not-exist"],
            "unresolved superseded_by",
        ),
        (
            "unsorted superseded_by",
            ["zzz-record", "aaa-record"],
            "superseded_by: expected sorted",
        ),
    ):
        superseded_errors = record_errors(
            with_record_overrides(
                {
                    "lifecycle": "retired",
                    "retirement": {**retirement_evidence, "superseded_by": superseded_by},
                }
            ),
            "fixture",
            superseded_catalogue,
        )
        check(
            any(expected_phrase in error for error in superseded_errors),
            f"retirement.superseded_by fixture ({label}) was not rejected for the "
            f"intended reason: {superseded_errors}",
        )

    # Positive control for the same rule: a target the catalogue publishes as retired
    # resolves, so it raises no supersession error even though it is no longer active.
    retired_target_errors = record_errors(
        with_record_overrides(
            {
                "lifecycle": "retired",
                "retirement": {
                    **retirement_evidence,
                    "superseded_by": ["some-other-retired-record"],
                },
            }
        ),
        "fixture",
        superseded_catalogue,
    )
    check(
        not any("superseded_by" in error for error in retired_target_errors),
        "retirement.superseded_by fixture (retired superseded_by ID) was rejected even "
        f"though the target resolves in the catalogue: {retired_target_errors}",
    )

    lean_check_retirement_output = lean_check(
        [
            {
                "axiom_dependencies": [],
                "lean_name": "LatticeSystem.Consumer.activeResult",
                "lifecycle": "active",
                "module": "LatticeSystem.Consumer",
            },
            {
                "axiom_dependencies": [],
                "lean_name": "LatticeSystem.Retired.formerResult",
                "lifecycle": "retired",
                "module": "LatticeSystem.RetiredModule",
            },
        ]
    )
    check(
        "LatticeSystem.Consumer.activeResult" in lean_check_retirement_output,
        "lean_check dropped the active record it should still assert (positive control)",
    )
    check(
        "import LatticeSystem.Consumer" in lean_check_retirement_output,
        "lean_check dropped the active record's import (positive control)",
    )
    check(
        "LatticeSystem.Retired.formerResult" not in lean_check_retirement_output,
        "lean_check emitted an #assert/#check/#print line for a retired record",
    )
    check(
        "import LatticeSystem.RetiredModule" not in lean_check_retirement_output,
        "lean_check emitted an import line for a retired record's (possibly deleted) module",
    )

    all_shard_data = [
        (shard_name.name, json.loads(shard_name.read_text(encoding="utf-8")))
        for shard_name in sorted((root / "records").glob("*.json"))
    ]
    all_records = [
        record
        for _, shard in all_shard_data
        for record in shard.get("records", [])
        if isinstance(record, dict)
    ]
    check(
        PROTOTYPE_RECORD_IDS <= {record.get("id") for record in all_records},
        "PROTOTYPE_RECORD_IDS is not a subset of the real catalogue's record IDs "
        "(positive control on main)",
    )
    # Negative control: retirement keeps a pinned prototype record in the catalogue, so
    # dropping one of those IDs entirely must fail.
    catalogue_without_pinned_id_ids = {
        record.get("id")
        for record in all_records
        if record.get("id") != "shastry-1992-staggered-susceptibility-bound"
    }
    missing_pin_validation = Validation()
    validate_prototype_pin(catalogue_without_pinned_id_ids, missing_pin_validation)
    check(
        bool(missing_pin_validation.errors),
        "deleting a PROTOTYPE_RECORD_IDS member from the catalogue was accepted: "
        f"{missing_pin_validation.errors}",
    )
    present_pin_validation = Validation()
    validate_prototype_pin(
        {record.get("id") for record in all_records}, present_pin_validation
    )
    check(
        not present_pin_validation.errors,
        "validate_prototype_pin rejected the real, complete catalogue record ID set "
        f"(positive control): {present_pin_validation.errors}",
    )

    retired_coverage_records = [
        {
            **record,
            "lifecycle": "retired",
        }
        if record.get("id")
        in {
            "shastry-1992-staggered-susceptibility-bound",
            "tasaki-2020-theorem-4-2-shastry-energy-gain",
            "tasaki-2020-theorem-3-1-finite-dimensional-core",
        }
        else record
        for record in all_records
    ]
    retired_coverage_validation = Validation()
    validate_prototype_coverage(
        "prototype",
        all_shard_data,
        retired_coverage_records,
        item_map,
        retired_coverage_validation,
    )
    check(
        bool(retired_coverage_validation.errors),
        "prototype coverage passed using only retired documented-axiom and capstone "
        f"records: {retired_coverage_validation.errors}",
    )

    # -- prototype coverage counts only active records per shard ----------------------------
    # A shard whose records are all retired must not count toward "two Tasaki source units",
    # so retiring every record of the ch02 and ch04 shards leaves ch03 as the only active
    # Tasaki unit and has to be rejected.
    tasaki_ch02_ch04_ids = {
        record.get("id")
        for shard_name, shard in all_shard_data
        if shard_name in {"tasaki-2020-ch02.json", "tasaki-2020-ch04.json"}
        for record in shard.get("records", [])
        if isinstance(record, dict)
    }
    check(
        bool(tasaki_ch02_ch04_ids),
        "fixture setup: tasaki-2020-ch02.json/tasaki-2020-ch04.json shard scan found no "
        "records (fixture is stale against the live catalogue)",
    )
    ch02_ch04_retired_records = [
        {**record, "lifecycle": "retired"} if record.get("id") in tasaki_ch02_ch04_ids else record
        for record in all_records
    ]
    ch02_ch04_retired_validation = Validation()
    validate_prototype_coverage(
        "prototype",
        all_shard_data,
        ch02_ch04_retired_records,
        item_map,
        ch02_ch04_retired_validation,
    )
    check(
        any(
            "expected two Tasaki source units" in error
            for error in ch02_ch04_retired_validation.errors
        ),
        "active-only coverage: retiring every record in two of three Tasaki shards, leaving "
        "chapter-03 active, was not rejected for the intended reason "
        f"(errors: {ch02_ch04_retired_validation.errors})",
    )

    # -- retirement guards exercised against a throwaway git repository ----------------------
    # These fixtures must not depend on the live LatticeSystem/ tree state, so each builds a
    # dedicated two-commit temp repository under .self-local/tmp (never /tmp; sandbox policy).
    fixture_scratch_root = repo_root / ".self-local" / "tmp"
    fixture_scratch_root.mkdir(parents=True, exist_ok=True)

    def fixture_git(arguments: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
        """Run one git command against a throwaway fixture repository."""
        return subprocess.run(
            ["git", *arguments],
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
            env={
                **os.environ,
                "GIT_AUTHOR_NAME": "formalization-status fixture",
                "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
                "GIT_COMMITTER_NAME": "formalization-status fixture",
                "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
            },
        )

    def fixture_head(cwd: Path) -> str:
        """Read the current HEAD commit ID of a fixture repository."""
        return fixture_git(["rev-parse", "HEAD"], cwd).stdout.strip()

    def fixture_candidate_commit(cwd: Path) -> None:
        """Move a fixture's HEAD one commit ahead of main, as a candidate change under review."""
        # Records are compared against main's first parent when HEAD is main's own commit, so a
        # fixture meaning "durable main already publishes this" must not leave HEAD on the
        # commit that published it.
        fixture_git(["checkout", "-q", "-b", "candidate"], cwd)
        fixture_git(
            ["commit", "-q", "--allow-empty", "-m", "candidate catalogue under validation"], cwd
        )

    # `lean_declaration_inventory` accepts a fixed modifier set only, and `nonrec theorem` is
    # a measured miss, so the whole-word scan is what keeps the "declaration is gone" guard
    # closed. The fixture commits the declaration as a plain `theorem` first (a real
    # `present_at_commit`), then adds `nonrec` while it stays live in the tree.
    hidden_decl_root = Path(
        tempfile.mkdtemp(prefix="retirement-fail-open-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], hidden_decl_root)
        hidden_decl_module = hidden_decl_root / "LatticeSystem" / "FailOpenFixture.lean"
        hidden_decl_module.parent.mkdir(parents=True, exist_ok=True)
        hidden_decl_module.write_text(
            "namespace LatticeSystem\n\ntheorem gone : True := trivial\n\nend LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/FailOpenFixture.lean"], hidden_decl_root)
        fixture_git(["commit", "-q", "-m", "add gone as a plain theorem"], hidden_decl_root)
        hidden_decl_present_at_commit = fixture_head(hidden_decl_root)
        hidden_decl_module.write_text(
            "namespace LatticeSystem\n\nnonrec theorem gone : True := trivial\n\n"
            "end LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/FailOpenFixture.lean"], hidden_decl_root)
        fixture_git(["commit", "-q", "-m", "refactor gone to nonrec theorem"], hidden_decl_root)

        fail_open_validation = Validation()
        validate_record(
            with_record_overrides(
                {
                    "declaration_kind": "theorem",
                    "lean_name": "LatticeSystem.gone",
                    "lifecycle": "retired",
                    "module": "LatticeSystem.FailOpenFixture",
                    "retirement": {
                        "present_at_commit": hidden_decl_present_at_commit,
                        "reason": "fixture: nonrec-theorem parser miss",
                        "superseded_by": [],
                    },
                    "source_path": "LatticeSystem/FailOpenFixture.lean",
                }
            ),
            "fail-open-nonrec-fixture",
            contract,
            hidden_decl_root,
            item_map,
            set(topic_map),
            fail_open_validation,
        )
        check(
            any(
                "still declared" in error and "LatticeSystem.gone" in error
                for error in fail_open_validation.errors
            ),
            "live nonrec declaration: a retired record naming LatticeSystem.gone, which the "
            "tree still declares as `nonrec theorem gone`, was accepted "
            f"(errors: {fail_open_validation.errors})",
        )
    finally:
        shutil.rmtree(hidden_decl_root, ignore_errors=True)

    # The schema's `lean_name` pattern permits leaves ending in `'`, which `\b` treats as a
    # non-word character in both directions, so the scan must delimit matches by Lean's own
    # `isIdRest` set instead: ASCII alphanumerics, `_`, `'`, `!`, `?`, the letterlike Greek,
    # Coptic, letterlike-symbol and script ranges, and subscript alphanumerics.
    primed_leaf_root = Path(
        tempfile.mkdtemp(prefix="lean-leaf-mention-apostrophe-", dir=fixture_scratch_root)
    )
    try:
        primed_leaf_dir = primed_leaf_root / "LatticeSystem"
        primed_leaf_dir.mkdir(parents=True, exist_ok=True)
        primed_leaf_probe = primed_leaf_dir / "Probe.lean"
        primed_leaf_cases = {
            "(gone')": True,
            "gone' ": True,
            "agone'": False,
            "gone'b": False,
        }
        for body, expect_found in primed_leaf_cases.items():
            primed_leaf_probe.write_text(body + "\n", encoding="utf-8")
            found = lean_leaf_mention(primed_leaf_root, "LatticeSystem.gone'") is not None
            check(
                found == expect_found,
                "primed leaf name: lean_leaf_mention(..., \"LatticeSystem.gone'\") against a "
                f"file containing {body!r} returned found={found}, expected {expect_found}",
            )
            primed_leaf_probe.unlink()
    finally:
        shutil.rmtree(primed_leaf_root, ignore_errors=True)

    # A primed leaf must also be caught where a retirement is actually gated, not only by the
    # direct probe above, so the same tree is mirrored through `validate_record`.
    primed_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-fail-open-apostrophe-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], primed_repo_root)
        primed_module = primed_repo_root / "LatticeSystem" / "FailOpenApostropheFixture.lean"
        primed_module.parent.mkdir(parents=True, exist_ok=True)
        primed_module.write_text(
            "namespace LatticeSystem\n\ntheorem gone' : True := trivial\n\nend LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/FailOpenApostropheFixture.lean"], primed_repo_root)
        fixture_git(["commit", "-q", "-m", "add gone' as a plain theorem"], primed_repo_root)
        primed_present_at_commit = fixture_head(primed_repo_root)
        primed_module.write_text(
            "namespace LatticeSystem\n\nnonrec theorem gone' : True := trivial\n\n"
            "end LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/FailOpenApostropheFixture.lean"], primed_repo_root)
        fixture_git(["commit", "-q", "-m", "refactor gone' to nonrec theorem"], primed_repo_root)

        primed_validation = Validation()
        validate_record(
            with_record_overrides(
                {
                    "declaration_kind": "theorem",
                    "lean_name": "LatticeSystem.gone'",
                    "lifecycle": "retired",
                    "module": "LatticeSystem.FailOpenApostropheFixture",
                    "retirement": {
                        "present_at_commit": primed_present_at_commit,
                        "reason": "fixture: apostrophe-leaf boundary miss",
                        "superseded_by": [],
                    },
                    "source_path": "LatticeSystem/FailOpenApostropheFixture.lean",
                }
            ),
            "fail-open-apostrophe-fixture",
            contract,
            primed_repo_root,
            item_map,
            set(topic_map),
            primed_validation,
        )
        check(
            any(
                "still declared" in error and "LatticeSystem.gone'" in error
                for error in primed_validation.errors
            ),
            "primed leaf name: a retired record naming LatticeSystem.gone', which the tree "
            "still declares as `nonrec theorem gone'`, was accepted "
            f"(errors: {primed_validation.errors})",
        )
    finally:
        shutil.rmtree(primed_repo_root, ignore_errors=True)

    # `present_at_commit` ancestry must be checked against durable `main` history
    # (`origin/main` if present, else `main`), never against `HEAD`. A commit that is only
    # reachable from a side branch must be rejected even though it is trivially an ancestor
    # of its own branch's HEAD.
    side_branch_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-ancestry-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], side_branch_repo_root)
        (side_branch_repo_root / "trunk.txt").write_text("trunk\n", encoding="utf-8")
        fixture_git(["add", "trunk.txt"], side_branch_repo_root)
        fixture_git(["commit", "-q", "-m", "trunk commit"], side_branch_repo_root)
        main_commit = fixture_head(side_branch_repo_root)
        fixture_git(["checkout", "-q", "-b", "side"], side_branch_repo_root)
        (side_branch_repo_root / "side.txt").write_text("side\n", encoding="utf-8")
        fixture_git(["add", "side.txt"], side_branch_repo_root)
        fixture_git(["commit", "-q", "-m", "side-only commit"], side_branch_repo_root)
        side_only_commit = fixture_head(side_branch_repo_root)

        side_records_by_id: dict[str, dict[str, Any]] = {}

        def ancestry_errors(commit: str) -> list[str]:
            """Validate one retirement's present_at_commit ancestry in isolation."""
            ancestry_validation = Validation()
            validate_retirement(
                {
                    "capstone": False,
                    "declaration_kind": None,
                    "lean_name": None,
                    "lifecycle": "retired",
                    "retirement": {
                        "present_at_commit": commit,
                        "reason": "fixture: ancestry regression",
                        "superseded_by": [],
                    },
                    "source_path": None,
                },
                "fixture",
                contract,
                side_branch_repo_root,
                side_records_by_id,
                ancestry_validation,
            )
            return ancestry_validation.errors

        side_only_errors = ancestry_errors(side_only_commit)
        check(
            any("ancestor" in error for error in side_only_errors),
            "durable-history ancestry: a present_at_commit reachable only from a side branch "
            "(not from main) was accepted because ancestry was checked against HEAD "
            f"instead of main (errors: {side_only_errors})",
        )
        main_commit_errors = ancestry_errors(main_commit)
        check(
            not main_commit_errors,
            "a present_at_commit that is an ancestor of main was rejected "
            f"(positive control): {main_commit_errors}",
        )
    finally:
        shutil.rmtree(side_branch_repo_root, ignore_errors=True)

    # When neither `origin/main` nor `main` resolves, ancestry must be rejected outright,
    # never silently skipped by falling back to HEAD.
    no_durable_main_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-ancestry-no-main-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "trunk"], no_durable_main_repo_root)
        (no_durable_main_repo_root / "trunk.txt").write_text("trunk\n", encoding="utf-8")
        fixture_git(["add", "trunk.txt"], no_durable_main_repo_root)
        fixture_git(["commit", "-q", "-m", "trunk-only commit"], no_durable_main_repo_root)
        trunk_only_commit = fixture_head(no_durable_main_repo_root)
        no_main_validation = Validation()
        validate_retirement(
            {
                "capstone": False,
                "declaration_kind": None,
                "lean_name": None,
                "lifecycle": "retired",
                "retirement": {
                    "present_at_commit": trunk_only_commit,
                    "reason": "fixture: no-resolvable-main regression",
                    "superseded_by": [],
                },
                "source_path": None,
            },
            "fixture",
            contract,
            no_durable_main_repo_root,
            {},
            no_main_validation,
        )
        check(
            bool(no_main_validation.errors),
            "durable-history ancestry: a repository with neither `origin/main` nor `main` "
            "accepted a present_at_commit by silently falling back to HEAD instead of "
            f"failing closed (errors: {no_main_validation.errors})",
        )
    finally:
        shutil.rmtree(no_durable_main_repo_root, ignore_errors=True)

    # -- retirement must freeze the active record's identity as recorded on durable main -----
    # An active record's Lean name, module, source path, and status dimensions are the
    # historical description of that declaration; retiring it must not be usable to
    # silently repoint a published record ID at an unrelated declaration.
    frozen_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-frozen-fields-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], frozen_repo_root)
        frozen_shard_dir = frozen_repo_root / "formalization-status" / "v2" / "records"
        frozen_shard_dir.mkdir(parents=True, exist_ok=True)
        frozen_shard_path = frozen_shard_dir / "frozen-fixture-shard.json"
        frozen_shard_path.write_text(
            json.dumps(
                {
                    "records": [
                        {
                            "axiom_dependencies": [],
                            "capstone": False,
                            "declaration_kind": "theorem",
                            "id": "frozen-fixture-record",
                            "implementation_state": "implemented",
                            "lean_name": "LatticeSystem.kept",
                            "lifecycle": "active",
                            "module": "LatticeSystem.FrozenFixture",
                            "origin": "project_original",
                            "proof_guide_anchor": None,
                            "retirement": None,
                            "source_coverage": "not_applicable",
                            "source_path": "LatticeSystem/FrozenFixture.lean",
                            "source_relations": [],
                            "summary": "fixture: frozen field regression",
                            "topic_ids": [],
                            "trust_state": "axiom_free",
                        }
                    ],
                    "schema_version": 2,
                    "source_id": "frozen-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        frozen_module = frozen_repo_root / "LatticeSystem" / "FrozenFixture.lean"
        frozen_module.parent.mkdir(parents=True, exist_ok=True)
        frozen_module.write_text(
            "namespace LatticeSystem\n\ntheorem kept : True := trivial\n\nend LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(
            [
                "add",
                "formalization-status/v2/records/frozen-fixture-shard.json",
                "LatticeSystem/FrozenFixture.lean",
            ],
            frozen_repo_root,
        )
        fixture_git(["commit", "-q", "-m", "add frozen-fixture-record as active"], frozen_repo_root)
        frozen_kept_commit = fixture_head(frozen_repo_root)
        frozen_changed_module = frozen_repo_root / "LatticeSystem" / "FrozenFixtureChanged.lean"
        frozen_changed_module.write_text(
            "namespace LatticeSystem\n\ntheorem changed : True := trivial\n\nend LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/FrozenFixtureChanged.lean"], frozen_repo_root)
        fixture_git(["commit", "-q", "-m", "add an unrelated declaration"], frozen_repo_root)
        frozen_changed_commit = fixture_head(frozen_repo_root)

        def frozen_field_errors(overrides: dict[str, Any]) -> list[str]:
            """Retire frozen-fixture-record with the given field overrides."""
            frozen_validation = Validation()
            record = {
                "capstone": False,
                "declaration_kind": "theorem",
                "id": "frozen-fixture-record",
                "implementation_state": "implemented",
                "lean_name": "LatticeSystem.kept",
                "lifecycle": "retired",
                "module": "LatticeSystem.FrozenFixture",
                "source_coverage": "not_applicable",
                "source_path": "LatticeSystem/FrozenFixture.lean",
                "trust_state": "axiom_free",
                "retirement": {
                    "present_at_commit": frozen_kept_commit,
                    "reason": "fixture: frozen field regression",
                    "superseded_by": [],
                },
            }
            record.update(overrides)
            validate_retirement(
                record, "frozen-fixture-repoint", contract, frozen_repo_root, {}, frozen_validation
            )
            return frozen_validation.errors

        unchanged_errors = frozen_field_errors({})
        check(
            not any("frozen" in error.lower() for error in unchanged_errors),
            "frozen fields positive control: retiring frozen-fixture-record with every "
            f"frozen field unchanged from durable main was rejected (errors: {unchanged_errors})",
        )

        # Each of the six frozen fields must be individually pinned: perturbing exactly one at
        # a time and asserting its own name appears in the error is the only way to prove the
        # tuple is not a decoy that only `lean_name` actually reads.
        frozen_field_alternate_values = {
            "implementation_state": "in_progress",
            "lean_name": "LatticeSystem.changed",
            "module": "LatticeSystem.FrozenFixtureChanged",
            "source_coverage": "complete",
            "source_path": "LatticeSystem/FrozenFixtureChanged.lean",
            "trust_state": "documented_axiom",
        }
        # The loop below is driven by this literal mapping's keys, not by FROZEN_RECORD_FIELDS
        # itself, so shrinking the tuple cannot shrink the loop along with it; this equality is
        # the only place that pins the tuple's full membership against an independent list.
        check(
            tuple(sorted(FROZEN_RECORD_FIELDS)) == tuple(sorted(frozen_field_alternate_values)),
            f"frozen fields: FROZEN_RECORD_FIELDS {tuple(sorted(FROZEN_RECORD_FIELDS))!r} does "
            "not equal the fixture's independently listed six field names "
            f"{tuple(sorted(frozen_field_alternate_values))!r}",
        )
        for frozen_field in frozen_field_alternate_values:
            single_field_errors = frozen_field_errors(
                {frozen_field: frozen_field_alternate_values[frozen_field]}
            )
            check(
                any(
                    "frozen-fixture-record" in error and frozen_field in error
                    for error in single_field_errors
                ),
                f"frozen fields: retiring frozen-fixture-record while changing only {frozen_field} "
                "away from the active record's value recorded on durable main was accepted "
                f"(errors: {single_field_errors})",
            )

        missing_id_validation = Validation()
        validate_retirement(
            {
                "capstone": False,
                "declaration_kind": "theorem",
                "id": "frozen-fixture-record-with-no-main-counterpart",
                "implementation_state": "implemented",
                "lean_name": "LatticeSystem.changed",
                "lifecycle": "retired",
                "module": "LatticeSystem.FrozenFixtureChanged",
                "source_coverage": "not_applicable",
                "source_path": "LatticeSystem/FrozenFixtureChanged.lean",
                "trust_state": "axiom_free",
                "retirement": {
                    "present_at_commit": frozen_changed_commit,
                    "reason": "fixture: missing main counterpart",
                    "superseded_by": [],
                },
            },
            "frozen-fixture-missing-id",
            contract,
            frozen_repo_root,
            {},
            missing_id_validation,
        )
        check(
            any(
                "absent from every record shard" in error
                for error in missing_id_validation.errors
            ),
            "frozen fields fail-closed: retiring an id absent from every shard on durable "
            f"main was accepted (errors: {missing_id_validation.errors})",
        )
    finally:
        shutil.rmtree(frozen_repo_root, ignore_errors=True)

    no_shard_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-frozen-fields-no-shard-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], no_shard_repo_root)
        no_shard_module = no_shard_repo_root / "LatticeSystem" / "FrozenFixtureChanged.lean"
        no_shard_module.parent.mkdir(parents=True, exist_ok=True)
        no_shard_module.write_text(
            "namespace LatticeSystem\n\ntheorem changed : True := trivial\n\nend LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/FrozenFixtureChanged.lean"], no_shard_repo_root)
        fixture_git(
            ["commit", "-q", "-m", "add an unrelated declaration, no v2 shard tree"],
            no_shard_repo_root,
        )
        no_shard_commit = fixture_head(no_shard_repo_root)
        no_shard_validation = Validation()
        validate_retirement(
            {
                "capstone": False,
                "declaration_kind": "theorem",
                "id": "frozen-fixture-record",
                "implementation_state": "implemented",
                "lean_name": "LatticeSystem.changed",
                "lifecycle": "retired",
                "module": "LatticeSystem.FrozenFixtureChanged",
                "source_coverage": "not_applicable",
                "source_path": "LatticeSystem/FrozenFixtureChanged.lean",
                "trust_state": "axiom_free",
                "retirement": {
                    "present_at_commit": no_shard_commit,
                    "reason": "fixture: no v2 shard tree on main",
                    "superseded_by": [],
                },
            },
            "frozen-fixture-no-shard",
            contract,
            no_shard_repo_root,
            {},
            no_shard_validation,
        )
        check(
            any(
                "absent from every record shard" in error
                for error in no_shard_validation.errors
            ),
            "frozen fields fail-closed: retiring a record when durable main has no "
            f"formalization-status/v2/records tree at all was accepted "
            f"(errors: {no_shard_validation.errors})",
        )
    finally:
        shutil.rmtree(no_shard_repo_root, ignore_errors=True)

    # -- reject_retirement_reversal must fail closed on an unreadable durable-main shard, not
    # only on an absent shard tree: an absent shard tree is the legitimate bootstrap case and
    # yields a readable empty index, but a shard that exists and fails to parse must not be
    # folded into that same empty result, since doing so would switch the terminal-retirement
    # guard off for every record without saying so.
    unreadable_shard_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-reversal-unreadable-shard-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], unreadable_shard_repo_root)
        (unreadable_shard_repo_root / "README.md").write_text("fixture\n", encoding="utf-8")
        fixture_git(["add", "README.md"], unreadable_shard_repo_root)
        fixture_git(["commit", "-q", "-m", "seed"], unreadable_shard_repo_root)
        unreadable_shard_dir = (
            unreadable_shard_repo_root / "formalization-status" / "v2" / "records"
        )
        unreadable_shard_dir.mkdir(parents=True, exist_ok=True)
        (unreadable_shard_dir / "retired-rec-a-shard.json").write_text(
            json.dumps(
                {
                    "records": [
                        {
                            "id": "rec-a",
                            "lifecycle": "retired",
                            "retirement": {
                                "present_at_commit": "a" * 40,
                                "reason": "fixture: rec-a retired on durable main",
                                "superseded_by": [],
                            },
                        }
                    ],
                    "schema_version": 2,
                    "source_id": "unreadable-shard-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        malformed_shard_name = "malformed-shard.json"
        (unreadable_shard_dir / malformed_shard_name).write_text(
            "{ this is not valid JSON", encoding="utf-8"
        )
        fixture_git(["add", "formalization-status/v2/records"], unreadable_shard_repo_root)
        fixture_git(
            ["commit", "-q", "-m", "publish rec-a retired alongside an unreadable shard"],
            unreadable_shard_repo_root,
        )
        fixture_candidate_commit(unreadable_shard_repo_root)
        unreadable_shard_validation = Validation()
        validate_retirement(
            {"id": "rec-a", "lifecycle": "active", "retirement": None},
            "retirement-reversal-unreadable-shard",
            contract,
            unreadable_shard_repo_root,
            {},
            unreadable_shard_validation,
        )
        check(
            any(
                "rec-a" in error and malformed_shard_name in error
                for error in unreadable_shard_validation.errors
            ),
            "terminal retirement fail-closed: durable main publishes rec-a retired but one "
            "shard alongside it is unreadable, and an active follow-up record for rec-a was "
            "accepted instead of rejected naming the unreadable shard "
            f"(errors: {unreadable_shard_validation.errors})",
        )
    finally:
        shutil.rmtree(unreadable_shard_repo_root, ignore_errors=True)

    # Positive control: when durable main publishes no record shard tree at all (bootstrap),
    # an active record must still be accepted -- absence, not unreadability, is the only
    # legitimate reason reject_retirement_reversal may stay silent.
    no_shard_reversal_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-reversal-no-shard-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], no_shard_reversal_repo_root)
        (no_shard_reversal_repo_root / "README.md").write_text("fixture\n", encoding="utf-8")
        fixture_git(["add", "README.md"], no_shard_reversal_repo_root)
        fixture_git(["commit", "-q", "-m", "seed, no v2 shard tree"], no_shard_reversal_repo_root)
        no_shard_reversal_validation = Validation()
        validate_retirement(
            {"id": "rec-a", "lifecycle": "active", "retirement": None},
            "retirement-reversal-no-shard",
            contract,
            no_shard_reversal_repo_root,
            {},
            no_shard_reversal_validation,
        )
        check(
            not no_shard_reversal_validation.errors,
            "terminal retirement bootstrap positive control: durable main publishing no "
            "formalization-status/v2/records tree at all rejected an active record "
            f"(errors: {no_shard_reversal_validation.errors})",
        )
    finally:
        shutil.rmtree(no_shard_reversal_repo_root, ignore_errors=True)

    # -- a supersession target must itself be retirable: once B is retired with its own valid
    # evidence, A's superseded_by entry naming B must not be treated as pointing to an inactive
    # record forever, and A's own frozen-identity check for the supersession list must not
    # report a drop when the id is merely no longer active.
    supersession_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-supersession-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], supersession_repo_root)
        supersession_module = supersession_repo_root / "LatticeSystem" / "SupersessionFixture.lean"
        supersession_module.parent.mkdir(parents=True, exist_ok=True)
        supersession_module.write_text(
            "namespace LatticeSystem\n\n"
            "theorem supersessionRetiredA : True := trivial\n\n"
            "theorem supersessionTargetB : True := trivial\n\n"
            "end LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(["add", "LatticeSystem/SupersessionFixture.lean"], supersession_repo_root)
        fixture_git(
            ["commit", "-q", "-m", "add supersessionRetiredA and supersessionTargetB"],
            supersession_repo_root,
        )
        supersession_present_at_commit = fixture_head(supersession_repo_root)
        supersession_shard_dir = supersession_repo_root / "formalization-status" / "v2" / "records"
        supersession_shard_dir.mkdir(parents=True, exist_ok=True)
        supersession_record_a = {
            "axiom_dependencies": [],
            "capstone": False,
            "declaration_kind": "theorem",
            "id": "supersession-record-a",
            "implementation_state": "implemented",
            "lean_name": "LatticeSystem.supersessionRetiredA",
            "lifecycle": "retired",
            "module": "LatticeSystem.SupersessionFixture",
            "origin": "project_original",
            "proof_guide_anchor": None,
            "retirement": {
                "present_at_commit": supersession_present_at_commit,
                "reason": "fixture: supersession target must itself be retirable",
                "superseded_by": ["supersession-record-b"],
            },
            "source_coverage": "not_applicable",
            "source_path": "LatticeSystem/SupersessionFixture.lean",
            "source_relations": [],
            "summary": "fixture: supersession source",
            "topic_ids": [],
            "trust_state": "axiom_free",
        }
        supersession_record_b_published = {
            "axiom_dependencies": [],
            "capstone": False,
            "declaration_kind": "theorem",
            "id": "supersession-record-b",
            "implementation_state": "implemented",
            "lean_name": "LatticeSystem.supersessionTargetB",
            "lifecycle": "active",
            "module": "LatticeSystem.SupersessionFixture",
            "origin": "project_original",
            "proof_guide_anchor": None,
            "retirement": None,
            "source_coverage": "complete",
            "source_path": "LatticeSystem/SupersessionFixture.lean",
            "source_relations": [],
            "summary": "fixture: supersession target",
            "topic_ids": [],
            "trust_state": "axiom_free",
        }
        (supersession_shard_dir / "supersession-shard.json").write_text(
            json.dumps(
                {
                    "records": [supersession_record_a, supersession_record_b_published],
                    "schema_version": 2,
                    "source_id": "supersession-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        fixture_git(
            ["add", "formalization-status/v2/records/supersession-shard.json"],
            supersession_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "publish supersession-record-a retired, -b active"],
            supersession_repo_root,
        )
        fixture_candidate_commit(supersession_repo_root)

        supersession_followup_a = dict(supersession_record_a)
        supersession_followup_b = dict(supersession_record_b_published)
        supersession_followup_b["lifecycle"] = "retired"
        supersession_followup_b["capstone"] = False
        supersession_followup_b["retirement"] = {
            "present_at_commit": supersession_present_at_commit,
            "reason": "fixture: supersession target retired in the same catalogue",
            "superseded_by": [],
        }
        supersession_records_by_id = {
            "supersession-record-a": supersession_followup_a,
            "supersession-record-b": supersession_followup_b,
        }

        supersession_a_validation = Validation()
        validate_retirement(
            supersession_followup_a,
            "supersession-fixture-a",
            contract,
            supersession_repo_root,
            supersession_records_by_id,
            supersession_a_validation,
        )
        check(
            not any(
                "superseded_by record is not active" in error or "no longer lists" in error
                for error in supersession_a_validation.errors
            ),
            "supersession target retirable: retiring supersession-record-b while "
            "supersession-record-a still lists it in superseded_by was rejected as an "
            "inactive-target or dropped-supersession violation "
            f"(errors: {supersession_a_validation.errors})",
        )

        # Negative control: an id that resolves nowhere in the follow-up catalogue must still
        # be rejected, so the fix above must not relax resolution itself.
        supersession_dangling_a = dict(supersession_followup_a)
        supersession_dangling_a["retirement"] = dict(supersession_followup_a["retirement"])
        supersession_dangling_a["retirement"]["superseded_by"] = ["supersession-record-nowhere"]
        supersession_dangling_validation = Validation()
        validate_retirement(
            supersession_dangling_a,
            "supersession-fixture-dangling",
            contract,
            supersession_repo_root,
            {"supersession-record-a": supersession_dangling_a},
            supersession_dangling_validation,
        )
        check(
            any(
                "unresolved superseded_by" in error
                for error in supersession_dangling_validation.errors
            ),
            "supersession resolution: a superseded_by id that resolves nowhere in the "
            "follow-up catalogue was accepted "
            f"(errors: {supersession_dangling_validation.errors})",
        )
    finally:
        shutil.rmtree(supersession_repo_root, ignore_errors=True)

    # -- an unhashable element in durable main's published superseded_by must not crash the
    # validator with a bare TypeError: every other read of a published main shard is
    # isinstance-guarded, so this set construction must be too.
    unhashable_superseded_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-unhashable-superseded-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], unhashable_superseded_repo_root)
        unhashable_module = (
            unhashable_superseded_repo_root / "LatticeSystem" / "UnhashableSupersededFixture.lean"
        )
        unhashable_module.parent.mkdir(parents=True, exist_ok=True)
        unhashable_module.write_text(
            "namespace LatticeSystem\n\n"
            "theorem unhashableSupersededFixture : True := trivial\n\n"
            "end LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(
            ["add", "LatticeSystem/UnhashableSupersededFixture.lean"],
            unhashable_superseded_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "add unhashableSupersededFixture while it still existed"],
            unhashable_superseded_repo_root,
        )
        unhashable_present_at_commit = fixture_head(unhashable_superseded_repo_root)
        unhashable_shard_dir = (
            unhashable_superseded_repo_root / "formalization-status" / "v2" / "records"
        )
        unhashable_shard_dir.mkdir(parents=True, exist_ok=True)
        # Written as raw JSON text, not through the schema, because a well-formed catalogue
        # cannot itself publish this: the point is what a malformed durable-main shard does to
        # the reader, not whether our own writer would ever produce one.
        (unhashable_shard_dir / "unhashable-superseded-shard.json").write_text(
            json.dumps(
                {
                    "records": [
                        {
                            "capstone": False,
                            "declaration_kind": "theorem",
                            "id": "unhashable-superseded-record",
                            "implementation_state": "implemented",
                            "lean_name": "LatticeSystem.unhashableSupersededFixture",
                            "lifecycle": "retired",
                            "module": "LatticeSystem.UnhashableSupersededFixture",
                            "retirement": {
                                "present_at_commit": unhashable_present_at_commit,
                                "reason": "fixture: main publishes an unhashable superseded_by entry",
                                "superseded_by": [["nested-list-entry"]],
                            },
                            "source_coverage": "not_applicable",
                            "source_path": "LatticeSystem/UnhashableSupersededFixture.lean",
                            "trust_state": "axiom_free",
                        }
                    ],
                    "schema_version": 2,
                    "source_id": "unhashable-superseded-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        fixture_git(
            ["add", "formalization-status/v2/records/unhashable-superseded-shard.json"],
            unhashable_superseded_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "publish an unhashable superseded_by entry"],
            unhashable_superseded_repo_root,
        )
        fixture_candidate_commit(unhashable_superseded_repo_root)
        unhashable_followup = {
            "capstone": False,
            "declaration_kind": "theorem",
            "id": "unhashable-superseded-record",
            "implementation_state": "implemented",
            "lean_name": "LatticeSystem.unhashableSupersededFixture",
            "lifecycle": "retired",
            "module": "LatticeSystem.UnhashableSupersededFixture",
            "retirement": {
                "present_at_commit": unhashable_present_at_commit,
                "reason": "fixture: follow-up drops the unhashable entry",
                "superseded_by": [],
            },
            "source_coverage": "not_applicable",
            "source_path": "LatticeSystem/UnhashableSupersededFixture.lean",
            "trust_state": "axiom_free",
        }
        unhashable_validation = Validation()
        unhashable_crashed: TypeError | None = None
        try:
            validate_retirement(
                unhashable_followup,
                "unhashable-superseded-fixture",
                contract,
                unhashable_superseded_repo_root,
                {},
                unhashable_validation,
            )
        except TypeError as error:
            unhashable_crashed = error
        check(
            unhashable_crashed is None and bool(unhashable_validation.errors),
            "unhashable superseded_by: durable main publishing a non-string, unhashable "
            "superseded_by entry either crashed the validator with a bare TypeError "
            f"({unhashable_crashed!r}) instead of a validation error, or was accepted "
            f"(errors: {unhashable_validation.errors})",
        )
    finally:
        shutil.rmtree(unhashable_superseded_repo_root, ignore_errors=True)

    # -- retirement is terminal: once durable main publishes an id as retired, a follow-up
    # record for that id must not silently repoint present_at_commit, must accept a corrected
    # reason or an appended superseded_by entry, must reject a removed superseded_by entry, and
    # must reject flipping lifecycle back to active even though every frozen identity field
    # still matches.
    retired_main_repo_root = Path(
        tempfile.mkdtemp(prefix="retirement-terminal-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], retired_main_repo_root)
        retired_main_module = (
            retired_main_repo_root / "LatticeSystem" / "RetirementTerminalFixture.lean"
        )
        retired_main_module.parent.mkdir(parents=True, exist_ok=True)
        retired_main_module.write_text(
            "namespace LatticeSystem\n\n"
            "theorem retiredTerminalFixture : True := trivial\n\n"
            "end LatticeSystem\n",
            encoding="utf-8",
        )
        fixture_git(
            ["add", "LatticeSystem/RetirementTerminalFixture.lean"], retired_main_repo_root
        )
        fixture_git(
            ["commit", "-q", "-m", "add retiredTerminalFixture while it still existed"],
            retired_main_repo_root,
        )
        retired_main_present_at_commit = fixture_head(retired_main_repo_root)
        retired_main_shard_dir = retired_main_repo_root / "formalization-status" / "v2" / "records"
        retired_main_shard_dir.mkdir(parents=True, exist_ok=True)
        retired_main_original_retirement = {
            "present_at_commit": retired_main_present_at_commit,
            "reason": "fixture: original retirement reason",
            "superseded_by": ["retirement-replacement-record"],
        }
        (retired_main_shard_dir / "retirement-terminal-shard.json").write_text(
            json.dumps(
                {
                    "records": [
                        {
                            "axiom_dependencies": [],
                            "capstone": False,
                            "declaration_kind": "theorem",
                            "id": "retirement-terminal-record",
                            "implementation_state": "implemented",
                            "lean_name": "LatticeSystem.retiredTerminalFixture",
                            "lifecycle": "retired",
                            "module": "LatticeSystem.RetirementTerminalFixture",
                            "origin": "project_original",
                            "proof_guide_anchor": None,
                            "retirement": retired_main_original_retirement,
                            "source_coverage": "not_applicable",
                            "source_path": "LatticeSystem/RetirementTerminalFixture.lean",
                            "source_relations": [],
                            "summary": "fixture: retirement is terminal",
                            "topic_ids": [],
                            "trust_state": "axiom_free",
                        },
                        {
                            "axiom_dependencies": [],
                            "capstone": False,
                            "declaration_kind": "theorem",
                            "id": "retirement-replacement-record",
                            "implementation_state": "implemented",
                            "lean_name": "LatticeSystem.retirementReplacement",
                            "lifecycle": "active",
                            "module": "LatticeSystem.RetirementTerminalFixture",
                            "origin": "project_original",
                            "proof_guide_anchor": None,
                            "retirement": None,
                            "source_coverage": "not_applicable",
                            "source_path": "LatticeSystem/RetirementTerminalFixture.lean",
                            "source_relations": [],
                            "summary": "fixture: retirement replacement target",
                            "topic_ids": [],
                            "trust_state": "axiom_free",
                        },
                    ],
                    "schema_version": 2,
                    "source_id": "retirement-terminal-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        fixture_git(
            ["add", "formalization-status/v2/records/retirement-terminal-shard.json"],
            retired_main_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "publish retirement-terminal-record as retired"],
            retired_main_repo_root,
        )
        fixture_candidate_commit(retired_main_repo_root)

        def retirement_terminal_record(overrides: dict[str, Any]) -> dict[str, Any]:
            """Build a follow-up record for retirement-terminal-record with given overrides."""
            record = {
                "capstone": False,
                "declaration_kind": "theorem",
                "id": "retirement-terminal-record",
                "implementation_state": "implemented",
                "lean_name": "LatticeSystem.retiredTerminalFixture",
                "lifecycle": "retired",
                "module": "LatticeSystem.RetirementTerminalFixture",
                "source_coverage": "not_applicable",
                "source_path": "LatticeSystem/RetirementTerminalFixture.lean",
                "trust_state": "axiom_free",
                "retirement": dict(retired_main_original_retirement),
            }
            record.update(overrides)
            return record

        retirement_terminal_records_by_id = {
            "retirement-terminal-record": retirement_terminal_record({}),
            "retirement-replacement-record": {"lifecycle": "active"},
        }

        def retirement_terminal_errors(overrides: dict[str, Any]) -> list[str]:
            """Validate one follow-up retirement-terminal-record against durable main."""
            terminal_validation = Validation()
            validate_retirement(
                retirement_terminal_record(overrides),
                "retirement-terminal-fixture",
                contract,
                retired_main_repo_root,
                retirement_terminal_records_by_id,
                terminal_validation,
            )
            return terminal_validation.errors

        # (a) present_at_commit differs from the evidence durable main already publishes.
        present_at_commit_changed_errors = retirement_terminal_errors(
            {
                "retirement": {
                    "present_at_commit": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                    "reason": retired_main_original_retirement["reason"],
                    "superseded_by": list(retired_main_original_retirement["superseded_by"]),
                }
            }
        )
        check(
            any(
                "retirement-terminal-record" in error and "present_at_commit" in error
                for error in present_at_commit_changed_errors
            ),
            "retirement is terminal: changing present_at_commit away from the value durable "
            "main already publishes for a retired record was accepted, or was rejected without "
            f"naming present_at_commit (errors: {present_at_commit_changed_errors})",
        )

        # (b) a corrected reason is accepted; the freeze must not cover free-text prose.
        reason_changed_errors = retirement_terminal_errors(
            {
                "retirement": {
                    "present_at_commit": retired_main_original_retirement["present_at_commit"],
                    "reason": "fixture: corrected retirement reason",
                    "superseded_by": list(retired_main_original_retirement["superseded_by"]),
                }
            }
        )
        check(
            not any(
                "frozen" in error.lower() or "retirement evidence differs" in error
                for error in reason_changed_errors
            ),
            "retirement is terminal: correcting only the retirement reason of an already-"
            f"retired record was rejected as a frozen-evidence violation (errors: {reason_changed_errors})",
        )

        # (c) an appended superseded_by entry is accepted (supersession may be discovered later).
        superseded_by_appended_errors = retirement_terminal_errors(
            {
                "retirement": {
                    "present_at_commit": retired_main_original_retirement["present_at_commit"],
                    "reason": retired_main_original_retirement["reason"],
                    "superseded_by": sorted(
                        {*retired_main_original_retirement["superseded_by"], "retirement-terminal-record-2"}
                    ),
                }
            }
        )
        check(
            not any(
                "frozen" in error.lower() or "retirement evidence differs" in error
                for error in superseded_by_appended_errors
            ),
            "retirement is terminal: appending a superseded_by entry to an already-retired "
            f"record was rejected as a frozen-evidence violation (errors: {superseded_by_appended_errors})",
        )

        # (d) removing a superseded_by entry that main already publishes must be rejected.
        superseded_by_removed_errors = retirement_terminal_errors(
            {
                "retirement": {
                    "present_at_commit": retired_main_original_retirement["present_at_commit"],
                    "reason": retired_main_original_retirement["reason"],
                    "superseded_by": [],
                }
            }
        )
        check(
            bool(superseded_by_removed_errors),
            "retirement is terminal: removing a superseded_by entry that durable main already "
            f"publishes for a retired record was accepted (errors: {superseded_by_removed_errors})",
        )
        check(
            any(
                "superseded_by" in error and "no longer lists" in error
                for error in superseded_by_removed_errors
            ),
            "retirement is terminal: removing a superseded_by entry that durable main already "
            "publishes for a retired record was rejected for an unrelated reason instead of "
            f"naming the dropped entry (errors: {superseded_by_removed_errors})",
        )

        # (e) retirement is terminal: flipping lifecycle back to active must be rejected even
        # though every frozen identity field still matches durable main.
        reactivated_errors = retirement_terminal_errors({"lifecycle": "active", "retirement": None})
        check(
            bool(reactivated_errors),
            "retirement is terminal: a follow-up record with lifecycle flipped back to active "
            "for an id durable main already publishes as retired was accepted with identity "
            f"fields unchanged (errors: {reactivated_errors})",
        )
        check(
            any(
                "retirement-terminal-record" in error and "terminal" in error
                for error in reactivated_errors
            ),
            "retirement is terminal: flipping lifecycle back to active for an id durable main "
            "already publishes as retired was rejected for an unrelated reason instead of "
            f"naming the terminal-retirement rule (errors: {reactivated_errors})",
        )

        # (f) positive control: an unchanged retired record (the steady state after merge) must
        # not be rejected.
        retirement_terminal_unchanged_errors = retirement_terminal_errors({})
        check(
            not retirement_terminal_unchanged_errors,
            "retirement is terminal positive control: re-validating retirement-terminal-record "
            "identical to what durable main already publishes was rejected "
            f"(errors: {retirement_terminal_unchanged_errors})",
        )
    finally:
        shutil.rmtree(retired_main_repo_root, ignore_errors=True)

    # -- the schema admits only the retirement evidence key that does not overclaim ---------
    # A record naming a commit proves the declaration was PRESENT there, not that it was the
    # LAST commit to have it (the ancestry checks above accept any ancestor whose tree still
    # declares the name), so the key that would promise the stronger claim is rejected. Its
    # spelling is written once, here, and reused by the published-prose scan below so the two
    # gates cannot drift apart.
    rejected_evidence_key = "last_present_commit"
    retirement_properties, retirement_required = contract.object_keys("record_retirement")
    old_key_retirement_evidence = {
        rejected_evidence_key: "7b65d59ec539b195d449bd97f94b08dbf99bf66e",
        "reason": "fixture: overclaiming retirement evidence key",
        "superseded_by": [],
    }
    old_key_validation = Validation()
    old_key_validation.keys(
        old_key_retirement_evidence,
        retirement_properties,
        retirement_required,
        "rejected-retirement-key-fixture",
    )
    check(
        bool(old_key_validation.errors),
        "record_retirement schema: a retirement object keyed by "
        f"{rejected_evidence_key} was accepted",
    )

    # -- the leaf-mention scan must end an identifier exactly where Lean's own isIdRest ends
    # it, in both directions: brackets and guillemets are delimiters that must not hide a
    # mention, while a trailing subscript, Greek, accented, Latin Extended-A or subscript-j
    # code point continues the leaf into a different identifier.
    idrest_probe_root = Path(
        tempfile.mkdtemp(prefix="lean-leaf-mention-idrest-", dir=fixture_scratch_root)
    )
    try:
        idrest_probe_dir = idrest_probe_root / "LatticeSystem"
        idrest_probe_dir.mkdir(parents=True, exist_ok=True)
        idrest_probe_file = idrest_probe_dir / "Probe.lean"
        idrest_probe_cases = [
            ("LatticeSystem.gone", "gone⦃x", True),  # U+2983: strict-implicit binder opener
            ("LatticeSystem.gone", "gone⟩", True),  # U+27E9: anonymous-constructor closer
            ("LatticeSystem.gone", "«gone»", True),  # U+00AB/U+00BB: French-quote name
            ("LatticeSystem.foo", "foo·", True),  # U+00B7 ·: not letter-like, a real delimiter
            ("LatticeSystem.gone", "gone₁", False),  # U+2081: subscript digit
            ("LatticeSystem.gone", "goneα", False),  # U+03B1 α: letterlike continuation
            ("LatticeSystem.hop", "Ĥhop", False),  # U+0124 Ĥ: Latin Extended-A continuation
            ("LatticeSystem.foo", "fooé", False),  # U+00E9 é: Latin-1 supplement continuation
            ("LatticeSystem.foo", "fooἀ", False),  # U+1F00 ἀ: polytonic Greek continuation
            ("LatticeSystem.foo", "fooⱼ", False),  # U+2C7C ⱼ: subscript-j continuation
        ]
        for lean_name, body, expect_found in idrest_probe_cases:
            idrest_probe_file.write_text(body + "\n", encoding="utf-8")
            found = lean_leaf_mention(idrest_probe_root, lean_name) is not None
            check(
                found == expect_found,
                f"isIdRest class: lean_leaf_mention(..., {lean_name!r}) against a file "
                f"containing {body!r} returned found={found}, expected {expect_found}",
            )
            idrest_probe_file.unlink()
    finally:
        shutil.rmtree(idrest_probe_root, ignore_errors=True)

    # -- LEAN_IDENTIFIER_REST_CLASS membership must match the pinned toolchain's `isIdRest`
    # code-point-for-code-point, not merely "adjacent to an ASCII leaf" as the probes above
    # sample: an oracle table pinned to the boundary of every range `isIdRest` adds beyond the
    # current class, plus code points that must stay excluded (mathematical-notation look-alikes
    # `isLetterLike` deliberately excludes, and the existing subscript-Latin boundary).
    lean_identifier_rest_pattern = re.compile(f"[{LEAN_IDENTIFIER_REST_CLASS}]")
    lean_isidrest_oracle = (
        (0x00C0, True),  # Latin-1 supplement letter (À), range start
        (0x00D6, True),  # Latin-1 supplement letter (Ö), range end before the gap
        (0x00D7, False),  # × multiplication sign: excluded gap inside the Latin-1 range
        (0x00D8, True),  # Latin-1 supplement letter (Ø), range restart after the gap
        (0x00F6, True),  # Latin-1 supplement letter (ö), range end before the gap
        (0x00F7, False),  # ÷ division sign: excluded gap inside the Latin-1 range
        (0x00F8, True),  # Latin Extended-A letter (ø), range restart
        (0x017F, True),  # Latin Extended-A letter (ſ), range end
        (0x0180, False),  # first code point past Latin Extended-A
        (0x1F00, True),  # polytonic Greek Extended letter, range start
        (0x1FFE, True),  # polytonic Greek Extended letter, range end
        (0x1FFF, False),  # first code point past polytonic Greek Extended
        (0x2C7C, True),  # subscript Latin letter j (isSubScriptAlnum)
        (0x2C7D, False),  # not a subscript-alnum code point
        (0x03BB, False),  # λ: mathematical-notation look-alike isLetterLike excludes
        (0x03A0, False),  # Π: mathematical-notation look-alike isLetterLike excludes
        (0x03A3, False),  # Σ: mathematical-notation look-alike isLetterLike excludes
        (0x2080, True),  # subscript digit 0 (isSubScriptAlnum), already in the current class
        (0x1D6A, True),  # subscript Latin letter x, the current class's subscript-Latin boundary
        (0x1D6B, False),  # first code point past the subscript-Latin range
    )
    for code_point, expect_member in lean_isidrest_oracle:
        character = chr(code_point)
        is_member = lean_identifier_rest_pattern.fullmatch(character) is not None
        check(
            is_member == expect_member,
            f"isIdRest class membership: U+{code_point:04X} membership in "
            f"LEAN_IDENTIFIER_REST_CLASS was {is_member}, expected {expect_member}",
        )

    # -- schema.json must agree with the frozen cutover validators --------------------------
    # `validate_cutover_baseline` and `validate_cutover_certificate` reject any
    # `schema_version` other than 1, so the schema's const for those two $defs stays 1 even
    # though the catalogue itself is version 2, and the title must not advertise version 1.
    cutover_defs = contract.defs
    for def_name in ("cutover_baseline", "cutover_certificate"):
        schema_version_const = (
            cutover_defs.get(def_name, {}).get("properties", {}).get("schema_version", {}).get("const")
        )
        check(
            schema_version_const == 1,
            f"cutover schema parity: schema.json $defs.{def_name}.properties.schema_version.const "
            f"is {schema_version_const!r}, not 1, contradicting the frozen "
            "formalization_cutover.py validators that require exactly 1",
        )
    check(
        "version 2" in contract.schema.get("title", "") and "version 1" not in contract.schema.get("title", ""),
        "schema title: schema.json title does not say 'version 2' "
        f"(got {contract.schema.get('title')!r})",
    )

    # -- git_capture fails closed and decodes as UTF-8 --------------------------------------
    # An unavailable git binary or repository path is a failed query rather than a traceback,
    # and subprocess output must decode as UTF-8 whatever locale the caller runs under.
    try:
        missing_git_result = git_capture(
            Path("/nonexistent/formalization-status-fixture-path"), ["status"]
        )
    except OSError as error:
        missing_git_result = None
        missing_git_error = error
    else:
        missing_git_error = None
    check(
        missing_git_error is None
        and isinstance(missing_git_result, subprocess.CompletedProcess)
        and missing_git_result.returncode != 0,
        "git_capture: a nonexistent repository path raised an "
        f"uncaught OSError instead of returning a failed CompletedProcess: {missing_git_error!r}",
    )
    utf8_repo_root = Path(
        tempfile.mkdtemp(prefix="git-capture-utf8-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], utf8_repo_root)
        (utf8_repo_root / "note.txt").write_text("note\n", encoding="utf-8")
        fixture_git(["add", "note.txt"], utf8_repo_root)
        non_ascii_message = "fixture commit éèê non-ASCII message"
        fixture_git(["commit", "-q", "-m", non_ascii_message], utf8_repo_root)
        utf8_env = {**os.environ, "LC_ALL": "C"}
        utf8_result = subprocess.run(
            ["git", "log", "-1", "--format=%s"],
            cwd=utf8_repo_root,
            check=False,
            capture_output=True,
            text=True,
            env=utf8_env,
        )
        check(
            non_ascii_message in utf8_result.stdout,
            "fixture setup: git itself did not echo the non-ASCII commit message under "
            f"LC_ALL=C (got {utf8_result.stdout!r})",
        )
        decoded = git_capture(utf8_repo_root, ["log", "-1", "--format=%s"])
        check(
            non_ascii_message in decoded.stdout,
            "git_capture: a non-ASCII commit subject was not decoded as UTF-8 "
            f"(got {decoded.stdout!r})",
        )
    finally:
        shutil.rmtree(utf8_repo_root, ignore_errors=True)

    # A commit subject can contain bytes that are not valid UTF-8 at all (not merely a
    # locale mismatch); `git_capture` must decode them without raising, since one
    # unparseable subject line should not crash validation of every other record.
    invalid_utf8_repo_root = Path(
        tempfile.mkdtemp(prefix="git-capture-invalid-utf8-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], invalid_utf8_repo_root)
        (invalid_utf8_repo_root / "note.txt").write_text("note\n", encoding="utf-8")
        fixture_git(["add", "note.txt"], invalid_utf8_repo_root)
        fixture_git(["commit", "-q", "-m", "seed commit"], invalid_utf8_repo_root)
        seed_commit = fixture_head(invalid_utf8_repo_root)
        tree_id = fixture_git(["write-tree"], invalid_utf8_repo_root).stdout.strip()
        # `git commit -F` and `git commit-tree` both measurably sanitize an invalid UTF-8
        # message into valid UTF-8 before storing it (byte 0xFF becomes the two-byte UTF-8
        # encoding of U+00FF), so the only way to land a genuinely invalid byte in a commit
        # object is to write the raw object with `git hash-object`, which performs no such
        # rewrite.
        raw_commit_path = invalid_utf8_repo_root / "invalid-utf8-commit.raw"
        raw_commit_path.write_bytes(
            b"tree " + tree_id.encode("ascii") + b"\n"
            b"parent " + seed_commit.encode("ascii") + b"\n"
            b"author formalization-status fixture <fixture@example.invalid> 1700000000 +0000\n"
            b"committer formalization-status fixture <fixture@example.invalid> 1700000000 +0000\n"
            b"\n"
            b"bad \xff byte"
        )
        invalid_commit_id = fixture_git(
            ["hash-object", "-t", "commit", "-w", str(raw_commit_path)],
            invalid_utf8_repo_root,
        ).stdout.strip()
        try:
            invalid_utf8_result: subprocess.CompletedProcess[str] | None = git_capture(
                invalid_utf8_repo_root, ["log", "-1", "--format=%s", invalid_commit_id]
            )
        except UnicodeDecodeError as error:
            invalid_utf8_error: UnicodeDecodeError | None = error
            invalid_utf8_result = None
        else:
            invalid_utf8_error = None
        check(
            invalid_utf8_error is None
            and invalid_utf8_result is not None
            and "�" in invalid_utf8_result.stdout,
            "git_capture: a commit subject containing an invalid UTF-8 byte either raised "
            f"{invalid_utf8_error!r} or was not decoded with a replacement character "
            f"(got {invalid_utf8_result.stdout if invalid_utf8_result else None!r})",
        )
    finally:
        shutil.rmtree(invalid_utf8_repo_root, ignore_errors=True)

    # -- the published prose must not promise what the schema key refuses to promise: the
    # contract and the runbook describe the same evidence field, so neither may spell the
    # stronger claim the schema rejects above. Prose writes that claim with hyphens and a
    # separate noun, so the scan matches the hyphenated stem rather than the exact key.
    rejected_evidence_prose = rejected_evidence_key.replace("_", "-").removesuffix("-commit")
    for docs_vocabulary_relative_path in (
        "docs/formalization-status-contract.md",
        "docs/formalization-publication.md",
    ):
        docs_vocabulary_path = repo_root / docs_vocabulary_relative_path
        docs_vocabulary_text = docs_vocabulary_path.read_text(encoding="utf-8")
        check(
            rejected_evidence_key not in docs_vocabulary_text
            and rejected_evidence_prose not in docs_vocabulary_text,
            f"{docs_vocabulary_relative_path}: uses the vocabulary "
            f"'{rejected_evidence_prose}' or '{rejected_evidence_key}' instead of "
            "'present at commit' / present_at_commit",
        )

    # -- the contract's set-relation claim about the schema's lean_name pattern must not
    # overclaim a strict superset it is not: it is looser inside the BMP but stricter for `!`,
    # `?`, and the astral letterlike block (U+1D49C-U+1D59F), so an unqualified "looser" repeats
    # the same class of overclaim the pinned isIdRest comparison above just corrected for the
    # scanning class itself.
    contract_vocabulary_text = " ".join(
        (repo_root / "docs" / "formalization-status-contract.md")
        .read_text(encoding="utf-8")
        .split()
    )
    check(
        "separate and looser syntactic filter" not in contract_vocabulary_text,
        "docs/formalization-status-contract.md: describes the schema's lean_name pattern as "
        "an unqualified 'looser' filter, which is false above U+FFFF and for `!`/`?`",
    )

    # -- the contract must state the terminal-retirement guard's bootstrap exception in prose,
    # not only in a code comment, because a reader who only has the contract cannot otherwise
    # tell apart the two cases reject_retirement_reversal treats differently: it stays silent
    # while durable main publishes no record shard tree at all (bootstrap), and it fails closed
    # (an error, not a silent skip) on any shard that exists but cannot be read.
    check(
        "the bootstrap exception: while durable main-branch history publishes no record "
        "shard tree at all, active records are not compared against it; any shard that "
        "exists but cannot be read is a validation error, not a silent skip"
        in contract_vocabulary_text,
        "docs/formalization-status-contract.md: does not state the terminal-retirement "
        "guard's bootstrap exception (expected phrase: 'the bootstrap exception: while "
        "durable main-branch history publishes no record shard tree at all, active records "
        "are not compared against it; any shard that exists but cannot be read is a "
        "validation error, not a silent skip')",
    )

    # -- main_record_index must not re-read durable main's record shards from scratch for
    # every retired record in a catalogue: `validate_frozen_identity` calls it once per
    # retired record, so an unmemoised implementation re-runs `git ls-tree` plus one `git show`
    # per shard for every single retired record in the catalogue.
    from unittest.mock import patch as memoization_patch

    memoization_repo_root = Path(
        tempfile.mkdtemp(prefix="main-record-index-memoization-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], memoization_repo_root)
        memoization_shard_dir = memoization_repo_root / "formalization-status" / "v2" / "records"
        memoization_shard_dir.mkdir(parents=True, exist_ok=True)
        (memoization_shard_dir / "memoization-fixture-shard.json").write_text(
            json.dumps(
                {
                    "records": [
                        {
                            "id": "memoization-fixture-record",
                            "lifecycle": "active",
                        }
                    ],
                    "schema_version": 2,
                    "source_id": "memoization-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        fixture_git(
            ["add", "formalization-status/v2/records/memoization-fixture-shard.json"],
            memoization_repo_root,
        )
        fixture_git(["commit", "-q", "-m", "publish one memoization fixture shard"], memoization_repo_root)

        git_capture_call_log: list[None] = []
        real_git_capture = git_capture

        def counting_git_capture(
            root: Path, arguments: list[str]
        ) -> subprocess.CompletedProcess[str]:
            """Wrap git_capture to count invocations without changing its behaviour."""
            git_capture_call_log.append(None)
            return real_git_capture(root, arguments)

        with memoization_patch(
            f"{__name__}.git_capture", side_effect=counting_git_capture
        ):
            main_record_index(memoization_repo_root, "main")
            calls_after_first_lookup = len(git_capture_call_log)
            main_record_index(memoization_repo_root, "main")
            calls_after_second_lookup = len(git_capture_call_log)
        check(
            calls_after_first_lookup > 0
            and calls_after_second_lookup == calls_after_first_lookup,
            "main_record_index memoization: the first lookup invoked git_capture "
            f"{calls_after_first_lookup} time(s) (must be > 0 to prove the reader actually ran), "
            "and a second lookup for the same ref and shard set invoked git_capture "
            f"{calls_after_second_lookup - calls_after_first_lookup} more "
            f"time(s) instead of reusing the first lookup's result "
            f"(first lookup: {calls_after_first_lookup} calls, "
            f"second lookup: {calls_after_second_lookup} calls)",
        )
    finally:
        shutil.rmtree(memoization_repo_root, ignore_errors=True)

    # -- main history must be read as durable history, not only main's own tip tree -------------
    # A run that validates the very commit landing on main compares a candidate change against
    # itself if the base is main's own tip: the base for that discrimination must be the commit
    # main published immediately before the candidate, not the candidate's own published state.
    main_reversal_repo_root = Path(
        tempfile.mkdtemp(prefix="main-history-tip-reversal-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], main_reversal_repo_root)
        reversal_shard_dir = main_reversal_repo_root / "formalization-status" / "v2" / "records"
        reversal_shard_dir.mkdir(parents=True, exist_ok=True)
        reversal_shard_path = reversal_shard_dir / "reversal-shard.json"

        def write_reversal_shard(lifecycle: str) -> None:
            """Publish rec-a on the reversal fixture's shard tree with the given lifecycle."""
            record: dict[str, Any] = {"id": "rec-a", "lifecycle": lifecycle}
            record["retirement"] = (
                {
                    "present_at_commit": "a" * 40,
                    "reason": "fixture: rec-a retired on durable main",
                    "superseded_by": [],
                }
                if lifecycle == "retired"
                else None
            )
            reversal_shard_path.write_text(
                json.dumps(
                    {
                        "records": [record],
                        "schema_version": 2,
                        "source_id": "reversal-fixture",
                        "source_unit": "fixture",
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )

        write_reversal_shard("retired")
        fixture_git(
            ["add", "formalization-status/v2/records/reversal-shard.json"],
            main_reversal_repo_root,
        )
        fixture_git(["commit", "-q", "-m", "publish rec-a retired"], main_reversal_repo_root)
        write_reversal_shard("active")
        fixture_git(
            ["add", "formalization-status/v2/records/reversal-shard.json"],
            main_reversal_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "publish rec-a active again, on main's own tip"],
            main_reversal_repo_root,
        )

        reversal_validation = Validation()
        validate_retirement(
            {"id": "rec-a", "lifecycle": "active", "retirement": None},
            "main-history-tip-reversal",
            contract,
            main_reversal_repo_root,
            {},
            reversal_validation,
        )
        check(
            any(
                "retired" in error and "terminal" in error
                for error in reversal_validation.errors
            ),
            "main history base: durable main's own tip commit lands rec-a active in the same "
            "commit whose immediate parent still publishes rec-a retired (HEAD == main), and "
            f"the reversal was accepted instead of rejected (errors: {reversal_validation.errors})",
        )
    finally:
        shutil.rmtree(main_reversal_repo_root, ignore_errors=True)

    # Positive control: HEAD == main and main's immediate parent also publishes rec-a active, so
    # there is no reversal anywhere in history and the record must be accepted either way.
    main_no_reversal_repo_root = Path(
        tempfile.mkdtemp(prefix="main-history-tip-no-reversal-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], main_no_reversal_repo_root)
        no_reversal_shard_dir = (
            main_no_reversal_repo_root / "formalization-status" / "v2" / "records"
        )
        no_reversal_shard_dir.mkdir(parents=True, exist_ok=True)
        no_reversal_shard_path = no_reversal_shard_dir / "no-reversal-shard.json"
        no_reversal_shard_text = json.dumps(
            {
                "records": [{"id": "rec-a", "lifecycle": "active", "retirement": None}],
                "schema_version": 2,
                "source_id": "no-reversal-fixture",
                "source_unit": "fixture",
            },
            indent=2,
        )
        no_reversal_shard_path.write_text(no_reversal_shard_text, encoding="utf-8")
        fixture_git(
            ["add", "formalization-status/v2/records/no-reversal-shard.json"],
            main_no_reversal_repo_root,
        )
        fixture_git(["commit", "-q", "-m", "publish rec-a active"], main_no_reversal_repo_root)
        fixture_git(
            ["commit", "-q", "--allow-empty", "-m", "no change, rec-a stays active"],
            main_no_reversal_repo_root,
        )

        no_reversal_validation = Validation()
        validate_retirement(
            {"id": "rec-a", "lifecycle": "active", "retirement": None},
            "main-history-tip-no-reversal",
            contract,
            main_no_reversal_repo_root,
            {},
            no_reversal_validation,
        )
        check(
            not no_reversal_validation.errors,
            "main history base positive control: rec-a is active both at main's tip and at "
            f"main's immediate parent, yet was rejected (errors: {no_reversal_validation.errors})",
        )
    finally:
        shutil.rmtree(main_no_reversal_repo_root, ignore_errors=True)

    # The same base rule must apply to validate_frozen_identity: a frozen-field change committed
    # directly on main's own tip, in the same commit that would need to compare against its
    # parent, must be rejected when HEAD == main.
    main_frozen_reversal_repo_root = Path(
        tempfile.mkdtemp(prefix="main-history-tip-frozen-drift-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], main_frozen_reversal_repo_root)
        frozen_drift_shard_dir = (
            main_frozen_reversal_repo_root / "formalization-status" / "v2" / "records"
        )
        frozen_drift_shard_dir.mkdir(parents=True, exist_ok=True)
        frozen_drift_shard_path = frozen_drift_shard_dir / "frozen-drift-shard.json"

        def write_frozen_drift_shard(lean_name: str) -> None:
            """Publish rec-frozen-drift retired, with the given lean_name, on the shard tree."""
            frozen_drift_shard_path.write_text(
                json.dumps(
                    {
                        "records": [
                            {
                                "id": "rec-frozen-drift",
                                "lifecycle": "retired",
                                "lean_name": lean_name,
                                "retirement": {
                                    "present_at_commit": "a" * 40,
                                    "reason": "fixture: frozen field drift",
                                    "superseded_by": [],
                                },
                            }
                        ],
                        "schema_version": 2,
                        "source_id": "frozen-drift-fixture",
                        "source_unit": "fixture",
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )

        write_frozen_drift_shard("LatticeSystem.kept")
        fixture_git(
            ["add", "formalization-status/v2/records/frozen-drift-shard.json"],
            main_frozen_reversal_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "publish rec-frozen-drift retired"],
            main_frozen_reversal_repo_root,
        )
        write_frozen_drift_shard("LatticeSystem.changed")
        fixture_git(
            ["add", "formalization-status/v2/records/frozen-drift-shard.json"],
            main_frozen_reversal_repo_root,
        )
        fixture_git(
            ["commit", "-q", "-m", "publish rec-frozen-drift with lean_name changed, on tip"],
            main_frozen_reversal_repo_root,
        )

        frozen_drift_validation = Validation()
        validate_retirement(
            {
                "id": "rec-frozen-drift",
                "lifecycle": "retired",
                "capstone": False,
                "lean_name": "LatticeSystem.changed",
                "retirement": {
                    "present_at_commit": "a" * 40,
                    "reason": "fixture: frozen field drift",
                    "superseded_by": [],
                },
            },
            "main-history-tip-frozen-drift",
            contract,
            main_frozen_reversal_repo_root,
            {},
            frozen_drift_validation,
        )
        check(
            any("frozen field lean_name" in error for error in frozen_drift_validation.errors),
            "main history base (validate_frozen_identity): a frozen-field change (lean_name) "
            "committed on main's own tip, whose immediate parent still publishes the original "
            f"lean_name, was accepted (errors: {frozen_drift_validation.errors})",
        )
    finally:
        shutil.rmtree(main_frozen_reversal_repo_root, ignore_errors=True)

    # -- a retired record's supersession graph must not admit self-reference or cycles ----------
    # `superseded_by` resolution only checks that the target id exists in the follow-up
    # catalogue, so a record can currently name itself, or two retired records can name each
    # other, and neither can ever be corrected once merged (a published supersession may never
    # be dropped).
    supersession_graph_repo_root = Path(
        tempfile.mkdtemp(prefix="supersession-graph-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], supersession_graph_repo_root)
        (supersession_graph_repo_root / "README.md").write_text("fixture\n", encoding="utf-8")
        fixture_git(["add", "README.md"], supersession_graph_repo_root)
        fixture_git(["commit", "-q", "-m", "seed, no v2 shard tree"], supersession_graph_repo_root)

        def supersession_graph_record(record_id: str, superseded_by: list[str]) -> dict[str, Any]:
            """Build one retired supersession-graph fixture record naming superseded_by."""
            return {
                "id": record_id,
                "lifecycle": "retired",
                "capstone": False,
                "retirement": {
                    "present_at_commit": "a" * 40,
                    "reason": "fixture: supersession graph",
                    "superseded_by": superseded_by,
                },
            }

        # (a) a retired record may not name itself as its own replacement.
        self_named = supersession_graph_record("graph-self", ["graph-self"])
        self_validation = Validation()
        validate_retirement(
            self_named,
            "supersession-graph-self",
            contract,
            supersession_graph_repo_root,
            {"graph-self": self_named},
            self_validation,
        )
        check(
            any(
                "graph-self" in error and "superseded_by" in error
                for error in self_validation.errors
            ),
            "supersession graph: a retired record naming its own id in superseded_by was "
            f"accepted (errors: {self_validation.errors})",
        )

        # (b) a mutual cycle: A supersedes B and B supersedes A, both retired. The pair's own
        # ids and locations must not contain "cycle" or "superseded_by" themselves, so an
        # unrelated error naming the id (e.g. the absent-on-main-history message) cannot be
        # mistaken for a dedicated supersession-graph rejection.
        cycle_a = supersession_graph_record("graph-mutual-a", ["graph-mutual-b"])
        cycle_b = supersession_graph_record("graph-mutual-b", ["graph-mutual-a"])
        cycle_records_by_id = {"graph-mutual-a": cycle_a, "graph-mutual-b": cycle_b}
        cycle_a_validation = Validation()
        validate_retirement(
            cycle_a,
            "supersession-graph-mutual-a",
            contract,
            supersession_graph_repo_root,
            cycle_records_by_id,
            cycle_a_validation,
        )
        cycle_b_validation = Validation()
        validate_retirement(
            cycle_b,
            "supersession-graph-mutual-b",
            contract,
            supersession_graph_repo_root,
            cycle_records_by_id,
            cycle_b_validation,
        )
        check(
            any(
                "superseded_by" in error or "cycle" in error
                for error in cycle_a_validation.errors
            )
            and any(
                "superseded_by" in error or "cycle" in error
                for error in cycle_b_validation.errors
            ),
            "supersession graph: a mutual cycle (graph-mutual-a and graph-mutual-b, both "
            "retired, naming each other) was accepted on at least one side "
            f"(errors a: {cycle_a_validation.errors}, errors b: {cycle_b_validation.errors})",
        )

        # (c) positive control: a chain ending in an active record must be accepted.
        chain_a = supersession_graph_record("graph-chain-a", ["graph-chain-b"])
        chain_b = supersession_graph_record("graph-chain-b", ["graph-chain-c"])
        chain_c = {"id": "graph-chain-c", "lifecycle": "active", "retirement": None}
        chain_records_by_id = {
            "graph-chain-a": chain_a,
            "graph-chain-b": chain_b,
            "graph-chain-c": chain_c,
        }
        chain_errors: list[str] = []
        for chain_record, chain_location in (
            (chain_a, "supersession-graph-chain-a"),
            (chain_b, "supersession-graph-chain-b"),
            (chain_c, "supersession-graph-chain-c"),
        ):
            chain_validation = Validation()
            validate_retirement(
                chain_record,
                chain_location,
                contract,
                supersession_graph_repo_root,
                chain_records_by_id,
                chain_validation,
            )
            chain_errors.extend(
                error
                for error in chain_validation.errors
                if "superseded_by" in error or "cycle" in error
            )
        check(
            not chain_errors,
            "supersession graph positive control: a chain graph-chain-a -> graph-chain-b -> "
            f"graph-chain-c ending in an active record was rejected (errors: {chain_errors})",
        )

        # (d) a longer cycle of three retired records.
        long_cycle_a = supersession_graph_record("graph-long-a", ["graph-long-b"])
        long_cycle_b = supersession_graph_record("graph-long-b", ["graph-long-c"])
        long_cycle_c = supersession_graph_record("graph-long-c", ["graph-long-a"])
        long_cycle_records_by_id = {
            "graph-long-a": long_cycle_a,
            "graph-long-b": long_cycle_b,
            "graph-long-c": long_cycle_c,
        }
        long_cycle_hits = 0
        for long_record, long_location in (
            (long_cycle_a, "supersession-graph-long-a"),
            (long_cycle_b, "supersession-graph-long-b"),
            (long_cycle_c, "supersession-graph-long-c"),
        ):
            long_validation = Validation()
            validate_retirement(
                long_record,
                long_location,
                contract,
                supersession_graph_repo_root,
                long_cycle_records_by_id,
                long_validation,
            )
            if any("cycle" in error for error in long_validation.errors):
                long_cycle_hits += 1
        check(
            long_cycle_hits > 0,
            "supersession graph: a longer three-record cycle (graph-long-a -> graph-long-b -> "
            "graph-long-c -> graph-long-a, all retired) was accepted on every side "
            f"(hits: {long_cycle_hits})",
        )
    finally:
        shutil.rmtree(supersession_graph_repo_root, ignore_errors=True)

    # -- with neither origin/main nor main resolvable, the terminal-retirement guard is silent
    # on the active path even though it fails closed on the retired path: a checkout whose
    # default branch has a different name (no origin remote either) must still fail closed
    # instead of certifying a catalogue it never actually compared against history.
    no_ref_repo_root = Path(
        tempfile.mkdtemp(prefix="main-history-ref-absent-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "trunk"], no_ref_repo_root)
        no_ref_shard_dir = no_ref_repo_root / "formalization-status" / "v2" / "records"
        no_ref_shard_dir.mkdir(parents=True, exist_ok=True)
        (no_ref_shard_dir / "no-ref-shard.json").write_text(
            json.dumps(
                {
                    "records": [
                        {
                            "id": "rec-no-ref",
                            "lifecycle": "retired",
                            "retirement": {
                                "present_at_commit": "a" * 40,
                                "reason": "fixture: retired with no origin/main or main ref",
                                "superseded_by": [],
                            },
                        }
                    ],
                    "schema_version": 2,
                    "source_id": "no-ref-fixture",
                    "source_unit": "fixture",
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        fixture_git(
            ["add", "formalization-status/v2/records/no-ref-shard.json"], no_ref_repo_root
        )
        fixture_git(
            ["commit", "-q", "-m", "publish rec-no-ref retired, on trunk not main"],
            no_ref_repo_root,
        )

        no_ref_validation = Validation()
        validate_retirement(
            {"id": "rec-no-ref", "lifecycle": "active", "retirement": None},
            "main-history-ref-absent",
            contract,
            no_ref_repo_root,
            {},
            no_ref_validation,
        )
        check(
            bool(no_ref_validation.errors),
            "ref-absence fail-open: a checkout whose default branch is named trunk (neither "
            "origin/main nor main resolves) accepted an active follow-up record for an id its "
            "own repository history already publishes as retired, with no error at all "
            f"(errors: {no_ref_validation.errors})",
        )
    finally:
        shutil.rmtree(no_ref_repo_root, ignore_errors=True)

    # -- the retired-name absence proof must also scan the tracked root umbrella LatticeSystem.lean
    # `lean_leaf_mention` and `current_lean_declaration_names` both root at repo_root/LatticeSystem,
    # so a declaration mentioned only in the tracked, CI-built repo_root/LatticeSystem.lean is
    # invisible to the absence proof even though it is live in the built library.
    root_umbrella_root = Path(
        tempfile.mkdtemp(prefix="lean-leaf-mention-root-umbrella-", dir=fixture_scratch_root)
    )
    try:
        (root_umbrella_root / "LatticeSystem").mkdir(parents=True, exist_ok=True)
        root_umbrella_file = root_umbrella_root / "LatticeSystem.lean"
        root_umbrella_file.write_text(
            "import LatticeSystem.RootUmbrellaFixture\n\n"
            "namespace LatticeSystem\n\n"
            "theorem rootUmbrellaMention : True := trivial\n\n"
            "end LatticeSystem\n",
            encoding="utf-8",
        )
        root_umbrella_mention = lean_leaf_mention(
            root_umbrella_root, "LatticeSystem.rootUmbrellaMention"
        )
        check(
            root_umbrella_mention is not None,
            "root umbrella scan: lean_leaf_mention(..., "
            '"LatticeSystem.rootUmbrellaMention") against a declaration that exists only in '
            "the tracked root umbrella LatticeSystem.lean returned None instead of naming that "
            f"file (found: {root_umbrella_mention!r})",
        )
        root_umbrella_declared = (
            "LatticeSystem.rootUmbrellaMention" in current_lean_declaration_names(root_umbrella_root)
        )
        check(
            root_umbrella_declared,
            "root umbrella scan: current_lean_declaration_names(...) omits a declaration that "
            "exists only in the tracked root umbrella LatticeSystem.lean",
        )
    finally:
        shutil.rmtree(root_umbrella_root, ignore_errors=True)

    # -- (pin) the isIdRest membership oracle must be exhaustive, not a boundary sample ----------
    # This reimplements `isIdRest` / `isLetterLike` / `isSubScriptAlnum` / the ASCII alphanumeric
    # test from the pinned Lean v4.29.0 toolchain source
    # (~/.elan/toolchains/leanprover--lean4---v4.29.0/src/lean/Init/Meta/Defs.lean:98-134 and
    # Init/Data/Char/Basic.lean:105-139) and compares it against LEAN_IDENTIFIER_REST_CLASS
    # membership over every non-surrogate code point, so a class edit that widens or narrows the
    # scan anywhere in the 0x110000 range is caught, not only at the boundary probes above.
    def lean_isIdRest_oracle(codepoint: int) -> bool:
        """Decide isIdRest membership for one code point from the pinned toolchain source."""
        is_ascii_alnum = (
            0x30 <= codepoint <= 0x39 or 0x41 <= codepoint <= 0x5A or 0x61 <= codepoint <= 0x7A
        )
        if is_ascii_alnum or codepoint in (0x5F, 0x27, 0x21, 0x3F):
            return True
        is_letter_like = (
            (0x3B1 <= codepoint <= 0x3C9 and codepoint != 0x3BB)
            or (0x391 <= codepoint <= 0x3A9 and codepoint not in (0x3A0, 0x3A3))
            or (0x3CA <= codepoint <= 0x3FB)
            or (0x1F00 <= codepoint <= 0x1FFE)
            or (0x2100 <= codepoint <= 0x214F)
            or (0x1D49C <= codepoint <= 0x1D59F)
            or (0xC0 <= codepoint <= 0xFF and codepoint not in (0xD7, 0xF7))
            or (0x100 <= codepoint <= 0x17F)
        )
        if is_letter_like:
            return True
        return (
            0x2080 <= codepoint <= 0x2089
            or 0x2090 <= codepoint <= 0x209C
            or 0x1D62 <= codepoint <= 0x1D6A
            or codepoint == 0x2C7C
        )

    isidrest_class_pattern = re.compile(f"[{LEAN_IDENTIFIER_REST_CLASS}]")

    def isidrest_scan_class_contains(codepoint: int) -> bool:
        """Decide LEAN_IDENTIFIER_REST_CLASS membership for one code point."""
        return isidrest_class_pattern.fullmatch(chr(codepoint)) is not None

    isidrest_oracle_mismatches = 0
    isidrest_first_mismatch: tuple[int, bool, bool] | None = None
    for codepoint in range(0x110000):
        if 0xD800 <= codepoint <= 0xDFFF:
            continue
        oracle_member = lean_isIdRest_oracle(codepoint)
        scanned_member = isidrest_scan_class_contains(codepoint)
        if oracle_member != scanned_member:
            isidrest_oracle_mismatches += 1
            if isidrest_first_mismatch is None:
                isidrest_first_mismatch = (codepoint, oracle_member, scanned_member)
    check(
        isidrest_oracle_mismatches == 0,
        "isIdRest exhaustive oracle: LEAN_IDENTIFIER_REST_CLASS disagrees with the pinned "
        f"isIdRest reimplementation at {isidrest_oracle_mismatches} code point(s) out of "
        f"1,112,064 non-surrogate code points, first at {isidrest_first_mismatch!r} "
        "(code point, isIdRest, scan class)",
    )

    # -- (pin) main_history_ref must not re-resolve the ref from scratch on every call ----------
    # `main_record_index` is memoized above, but nothing pinned that `main_history_ref` itself
    # reuses its first answer instead of re-spawning git for every record in a catalogue.
    main_history_ref_memo_repo_root = Path(
        tempfile.mkdtemp(prefix="main-history-ref-memoization-", dir=fixture_scratch_root)
    )
    try:
        fixture_git(["init", "-q", "-b", "main"], main_history_ref_memo_repo_root)
        (main_history_ref_memo_repo_root / "README.md").write_text("fixture\n", encoding="utf-8")
        fixture_git(["add", "README.md"], main_history_ref_memo_repo_root)
        fixture_git(["commit", "-q", "-m", "seed"], main_history_ref_memo_repo_root)

        ref_call_log: list[None] = []
        real_git_capture_for_ref = git_capture

        def counting_git_capture_for_ref(
            root: Path, arguments: list[str]
        ) -> subprocess.CompletedProcess[str]:
            """Wrap git_capture to count invocations without changing its behaviour."""
            ref_call_log.append(None)
            return real_git_capture_for_ref(root, arguments)

        with memoization_patch(
            f"{__name__}.git_capture", side_effect=counting_git_capture_for_ref
        ):
            main_history_ref(main_history_ref_memo_repo_root)
            ref_calls_after_first_lookup = len(ref_call_log)
            main_history_ref(main_history_ref_memo_repo_root)
            ref_calls_after_second_lookup = len(ref_call_log)
        check(
            ref_calls_after_first_lookup > 0
            and ref_calls_after_second_lookup == ref_calls_after_first_lookup,
            "main_history_ref memoization: the first lookup invoked git_capture "
            f"{ref_calls_after_first_lookup} time(s) (must be > 0 to prove the reader actually "
            "ran), and a second lookup for the same repository invoked git_capture "
            f"{ref_calls_after_second_lookup - ref_calls_after_first_lookup} more time(s) "
            "instead of reusing the first lookup's result "
            f"(first lookup: {ref_calls_after_first_lookup} calls, "
            f"second lookup: {ref_calls_after_second_lookup} calls)",
        )
    finally:
        shutil.rmtree(main_history_ref_memo_repo_root, ignore_errors=True)

    return failures


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-aggregate", type=Path, help="write deterministic aggregate JSON")
    parser.add_argument("--emit-lean-check", type=Path, help="write Lean #check/#print-axioms input")
    parser.add_argument("--self-test", action="store_true", help="run built-in contract regressions")
    return parser.parse_args()


def main() -> int:
    """Validate the version-2 catalogue and optionally emit deterministic views."""
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    root = repo_root / "formalization-status" / "v2"
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
                    repo_root,
                )
            )
            non_record_ordinals = certificate.get("non_record_ordinals", [])
            exceptional_mappings, _exceptional_errors = exceptional_mapping_map(
                certificate.get("exceptional_mappings")
            )
            retired_declarations, _retired_errors = retired_declaration_map(
                certificate.get("retired_declarations"), repo_root
            )
            for error in validate_cutover_baseline(
                baseline,
                records,
                reconstruct_legacy_rows(repo_root),
                set(non_record_ordinals) if isinstance(non_record_ordinals, list) else set(),
                exceptional_mappings,
                retired_declarations,
            ):
                validation.errors.append(error)
    validate_prototype_coverage(
        manifest.get("catalog_state"), shard_data, records, source_items, validation
    )
    validate_prototype_pin(
        {record["id"] for record in records if isinstance(record.get("id"), str)},
        validation,
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
        f"formalization-status v2: valid {manifest['catalog_state']} catalogue "
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
