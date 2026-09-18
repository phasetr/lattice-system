#!/usr/bin/env python3
"""Generate the public registry view without exposing private source metadata."""

import argparse
import csv
import html
import json
import re
import sys
import tempfile
import unittest
from collections import OrderedDict, defaultdict
from pathlib import Path


HEADERS = {
    "tracks": ["track_id", "position", "title", "public_slug"],
    "sources": [
        "source_id", "track_id", "source_position", "source_kind",
        "citation_key", "title", "authors", "year", "edition",
        "identifier_kind", "identifier", "public_url", "public_slug",
        "local_ref_key", "pdf_oid", "text_oid", "coverage",
    ],
    "source_progress": ["source_id", "lifecycle", "review_ref"],
    "pages": [
        "page_id", "source_id", "order_key", "printed_page", "pdf_page",
        "section", "page_kind", "pass1", "pass2", "source_oid",
    ],
    "claims": [
        "claim_id", "source_id", "order_key", "page_id", "locator",
        "disposition", "subkind", "normalized_content", "content_oid",
        "exclusion_rationale", "exclusion_review_ref", "tombstone",
        "superseded_by", "tombstone_rationale", "tombstone_review_ref",
    ],
    "source_items": [
        "item_id", "source_id", "order_key", "page_id", "item_kind",
        "source_label", "title", "locator", "public_group", "public_slug",
        "review_ref",
    ],
    "item_claims": ["item_id", "position", "claim_id"],
    "claim_vocabulary_review": ["claim_id", "basis", "review_ref"],
    "vocabulary": [
        "vocabulary_id", "declaration", "module", "declaration_kind",
        "origin", "parent_vocabulary_id", "type_oid", "declaration_oid",
        "design_role", "finiteness_scope",
    ],
    "claim_vocabulary": ["claim_id", "vocabulary_id"],
    "bindings": [
        "claim_id", "statement_decl", "proof_decl", "module",
        "statement_oid", "nonvacuity_decl",
    ],
    "axioms": [
        "axiom_id", "declaration", "module", "category", "source_locator",
        "rationale", "reopen_condition",
    ],
    "claim_axioms": ["claim_id", "axiom_id"],
    "phase": ["phase"],
}

SOURCE_ITEM_REVIEW = "PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"
NAMED_LABEL = re.compile(
    r"^(Theorem|Lemma|Corollary|Proposition|Definition|Problem|Conjecture|"
    r"Example|Exercise)\s+([^,]+)"
)
OTHER_LABELS = [
    (re.compile(r"^(Remark|Note) unnumbered line [0-9]+"), None),
    (re.compile(r"^[Ee]quation\s+\([^;]+\)"), "equation"),
    (re.compile(r"^Fig\.\s+[^ ,;]+"), "figure"),
    (re.compile(r"^Footnote\s+[^ ,;]+"), "footnote"),
    (re.compile(r"^Table\s+[^ ,;]+"), "table"),
]
KIND_BY_PREFIX = {
    "Theorem": "theorem",
    "Lemma": "lemma",
    "Corollary": "corollary",
    "Proposition": "proposition",
    "Definition": "definition",
    "Problem": "problem",
    "Conjecture": "conjecture",
    "Example": "example",
    "Exercise": "exercise",
    "Remark": "remark",
    "Note": "note",
}


class CatalogError(Exception):
    """Raised when public documentation inputs are inconsistent."""


def read_tsv(path, expected_header):
    with path.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != expected_header:
            raise CatalogError(
                "bad header for {}: expected {!r}, found {!r}".format(
                    path, expected_header, reader.fieldnames
                )
            )
        return list(reader)


def write_tsv(path, header, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=header, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def extract_source_label(locator):
    """Return (kind, label, canonical locator) using locator text only."""
    segments = [segment.strip() for segment in locator.split(";")]
    for index, segment in enumerate(segments):
        match = NAMED_LABEL.match(segment)
        if match:
            label = "{} {}".format(match.group(1), match.group(2))
            prefix = segments[:index] + [label]
            return KIND_BY_PREFIX[match.group(1)], label, "; ".join(prefix)
        for pattern, fixed_kind in OTHER_LABELS:
            match = pattern.match(segment)
            if not match:
                continue
            label = match.group(0)
            kind = fixed_kind or KIND_BY_PREFIX[label.split()[0]]
            prefix = segments[:index] + [label]
            return kind, label, "; ".join(prefix)
    return "unlabeled", "NONE", locator


def slug_for_group(group):
    chapter_match = re.fullmatch(r"Chapter\s+([0-9]+)", group.strip(), re.IGNORECASE)
    if chapter_match:
        return "chapter-{:02d}".format(int(chapter_match.group(1)))
    value = group
    value = value.lower().replace("–", "-").replace("—", "-")
    value = re.sub(r"[^a-z0-9]+", "-", value).strip("-")
    if not value:
        raise CatalogError("public group has no safe slug: {!r}".format(group))
    return value


def public_group_for(page, locator):
    """Collapse fine sections to stable public chapter/front/back groups."""
    section = page["section"]
    section_match = re.match(r"^§([0-9]+|[A-Za-z]+)(?:\.|$)", section)
    if not section_match:
        section_match = re.search(r"(?:^|; )§([0-9]+|[A-Za-z]+)(?:\.|;|$)", locator)
    if section_match:
        top = section_match.group(1)
        if top.isdigit():
            return "Chapter {:02d}".format(int(top))
        return "Appendix " + top.upper()
    if section in {"Contents", "Preface", "Symbols"}:
        return "Front matter"
    if section in {"Index", "References", "Solutions"}:
        return section
    by_page_kind = {
        "front_matter": "Front matter",
        "back_matter": "Back matter",
        "index": "Index",
    }
    return by_page_kind.get(page["page_kind"], "Ungrouped")


def derive_source_items(claims, pages, sources, tracks):
    """Derive the exact reviewed seed rows from existing public fields."""
    page_by_id = {row["page_id"]: row for row in pages}
    if len(page_by_id) != len(pages):
        raise CatalogError("duplicate page ID")
    track_position = {
        row["track_id"]: int(row["position"]) for row in tracks
    }
    source_order = {}
    for row in sources:
        if row["track_id"] not in track_position:
            raise CatalogError("source refers to unknown track " + row["source_id"])
        source_order[row["source_id"]] = (
            track_position[row["track_id"]], int(row["source_position"])
        )
    for claim in claims:
        if claim["source_id"] not in source_order:
            raise CatalogError("claim refers to unknown source " + claim["claim_id"])
    ordered_claims = sorted(
        claims,
        key=lambda row: (
            source_order[row["source_id"]], row["order_key"], row["claim_id"]
        ),
    )
    groups = OrderedDict()
    for claim in ordered_claims:
        if claim["page_id"] not in page_by_id:
            raise CatalogError("claim refers to unknown page " + claim["claim_id"])
        grouping_locator = re.sub(
            r"; corpus correction successor [0-9]+/[0-9]+$", "",
            claim["locator"],
        )
        kind, label, canonical_locator = extract_source_label(grouping_locator)
        if label == "NONE":
            key = (
                claim["source_id"], claim["page_id"], "locator",
                grouping_locator,
            )
        else:
            key = (claim["source_id"], claim["page_id"], "label", label)
        if key not in groups:
            page = page_by_id[claim["page_id"]]
            public_group = public_group_for(page, claim["locator"])
            groups[key] = {
                "source_id": claim["source_id"],
                "order_key": claim["order_key"],
                "page_id": claim["page_id"],
                "item_kind": kind,
                "source_label": label,
                "title": "NONE",
                "locator": canonical_locator,
                "public_group": public_group,
                "public_slug": slug_for_group(public_group),
                "review_ref": SOURCE_ITEM_REVIEW,
                "claims": [],
            }
        item = groups[key]
        if item["item_kind"] != kind or item["locator"] != canonical_locator:
            raise CatalogError("inconsistent explicit source label " + label)
        item["claims"].append(claim["claim_id"])

    counters = defaultdict(int)
    item_rows = []
    relation_rows = []
    for item in groups.values():
        source_id = item["source_id"]
        counters[source_id] += 1
        item_id = "IT-{}-{:04d}".format(source_id, counters[source_id])
        item_rows.append({
            key: item[key] for key in HEADERS["source_items"] if key != "item_id"
        })
        item_rows[-1] = {"item_id": item_id, **item_rows[-1]}
        for position, claim_id in enumerate(item["claims"], start=1):
            relation_rows.append({
                "item_id": item_id,
                "position": str(position),
                "claim_id": claim_id,
            })
    return item_rows, relation_rows


def load_registry(root):
    registry = root / "registry"
    paths = {
        "tracks": registry / "tracks.tsv",
        "sources": registry / "sources.tsv",
        "source_progress": registry / "source-progress.tsv",
        "pages": registry / "pages.tsv",
        "claims": registry / "claims.tsv",
        "source_items": registry / "source-items.tsv",
        "item_claims": registry / "item-claims.tsv",
        "claim_vocabulary_review": registry / "claim-vocabulary-review.tsv",
        "vocabulary": registry / "vocabulary.tsv",
        "claim_vocabulary": registry / "claim-vocabulary.tsv",
        "bindings": registry / "bindings.tsv",
        "axioms": registry / "axioms.tsv",
        "claim_axioms": registry / "claim-axioms.tsv",
        "phase": registry / "phase.tsv",
    }
    return {
        name: read_tsv(path, HEADERS[name]) for name, path in paths.items()
    }


def validate_source_items(data):
    expected_items, expected_relations = derive_source_items(
        data["claims"], data["pages"], data["sources"], data["tracks"]
    )
    if data["source_items"] != expected_items:
        raise CatalogError(
            "source-items.tsv differs from deterministic locator-derived inventory"
        )
    if data["item_claims"] != expected_relations:
        raise CatalogError(
            "item-claims.tsv differs from deterministic active-claim coverage"
        )
    registered = {row["claim_id"] for row in data["claims"]}
    mapped = [row["claim_id"] for row in data["item_claims"]]
    if len(mapped) != len(set(mapped)) or set(mapped) != registered:
        raise CatalogError("registered claims are not covered exactly once")


def index_unique(rows, key, description):
    result = {}
    for row in rows:
        value = row[key]
        if value in result:
            raise CatalogError("duplicate {} {}".format(description, value))
        result[value] = row
    return result


def public_catalog(data):
    validate_source_items(data)
    phase_rows = data["phase"]
    if len(phase_rows) != 1:
        raise CatalogError("phase registry must contain exactly one value")
    phase = phase_rows[0]["phase"]
    claims = index_unique(data["claims"], "claim_id", "claim")
    vocabulary = index_unique(data["vocabulary"], "vocabulary_id", "vocabulary")
    review = index_unique(
        data["claim_vocabulary_review"], "claim_id", "vocabulary review"
    )
    source_progress = index_unique(
        data["source_progress"], "source_id", "source progress"
    )
    vocabulary_lifecycles = {
        "vocabulary_reviewed", "skeleton_frozen", "proof_active", "complete"
    }
    bindings = index_unique(data["bindings"], "claim_id", "binding")
    axioms = index_unique(data["axioms"], "axiom_id", "axiom")
    vocabulary_by_claim = defaultdict(list)
    for row in data["claim_vocabulary"]:
        vocabulary_by_claim[row["claim_id"]].append(row["vocabulary_id"])
    axioms_by_claim = defaultdict(list)
    for row in data["claim_axioms"]:
        axioms_by_claim[row["claim_id"]].append(row["axiom_id"])
    claims_by_item = defaultdict(list)
    for row in data["item_claims"]:
        claims_by_item[row["item_id"]].append((int(row["position"]), row["claim_id"]))

    public_items = []
    for item in data["source_items"]:
        public_claims = []
        for _, claim_id in sorted(claims_by_item[item["item_id"]]):
            claim = claims[claim_id]
            binding = bindings.get(claim_id)
            axiom_ids = axioms_by_claim.get(claim_id, [])
            required = [
                {
                    "vocabulary_id": vocabulary_id,
                    "declaration": vocabulary[vocabulary_id]["declaration"],
                }
                for vocabulary_id in vocabulary_by_claim.get(claim_id, [])
            ]
            if claim["tombstone"] == "true":
                lifecycle = "superseded" if claim["superseded_by"] != "NONE" else "tombstoned"
            else:
                lifecycle = "active"
            reviewed = claim_id in review
            vocabulary_ready = (
                reviewed
                and source_progress[claim["source_id"]]["lifecycle"]
                in vocabulary_lifecycles
            )
            public_claims.append({
                "claim_id": claim_id,
                "disposition": claim["disposition"],
                "subkind": claim["subkind"],
                "lifecycle": lifecycle,
                "successor_claim": claim["superseded_by"],
                "vocabulary_status": (
                    "vocabulary_ready" if vocabulary_ready
                    else "review_staged" if reviewed else "not_reviewed"
                ),
                "binding_status": "bound" if binding else "not_bound",
                "statement_declaration": binding["statement_decl"] if binding else "NONE",
                "statement_module": binding["module"] if binding else "NONE",
                "proof_status": (
                    "proof_declaration_registered"
                    if binding and binding["proof_decl"] != "NONE"
                    else "not_recorded"
                ),
                "proof_declaration": binding["proof_decl"] if binding else "NONE",
                "axiom_status": "registered_dependencies" if axiom_ids else "not_assessed",
                "registered_axioms": [
                    {
                        "axiom_id": axiom_id,
                        "declaration": axioms[axiom_id]["declaration"],
                        "category": axioms[axiom_id]["category"],
                    }
                    for axiom_id in axiom_ids
                ],
                "vocabulary_basis": review.get(claim_id, {}).get("basis", "not_reviewed"),
                "required_vocabulary": required,
            })
        public_items.append({
            key: item[key]
            for key in [
                "item_id", "source_id", "order_key", "page_id", "item_kind",
                "source_label", "title", "locator", "public_group", "public_slug",
            ]
        })
        public_items[-1]["claims"] = public_claims

    source_by_id = index_unique(data["sources"], "source_id", "source")
    groups = OrderedDict()
    for item in public_items:
        key = (item["source_id"], item["public_slug"])
        if key not in groups:
            groups[key] = {
                "source_id": item["source_id"],
                "source_public_slug": source_by_id[item["source_id"]]["public_slug"],
                "public_group": item["public_group"],
                "public_slug": item["public_slug"],
                "item_ids": [],
            }
        elif groups[key]["public_group"] != item["public_group"]:
            raise CatalogError("public group slug collision: " + item["public_slug"])
        groups[key]["item_ids"].append(item["item_id"])

    tracks = [
        {
            key: row[key]
            for key in ["track_id", "position", "title", "public_slug"]
        }
        for row in data["tracks"]
    ]
    sources = []
    for row in data["sources"]:
        sources.append({
            key: row[key]
            for key in [
                "source_id", "track_id", "source_position", "source_kind",
                "citation_key", "title", "authors", "year", "edition",
                "identifier_kind", "identifier", "public_url", "public_slug",
                "coverage",
            ]
        })
        sources[-1]["lifecycle"] = source_progress[row["source_id"]]["lifecycle"]
    active_claims = sum(
        1 for claim in claims.values() if claim["tombstone"] == "false"
    )
    formalization_targets = sum(
        1 for claim in claims.values()
        if claim["tombstone"] == "false"
        and claim["disposition"] != "out_of_scope"
    )
    tombstoned_claims = sum(
        1 for claim in claims.values() if claim["tombstone"] == "true"
    )
    mathlib_only = sum(
        1 for row in review.values() if row["basis"] == "mathlib_only"
    )
    project_vocabulary = sum(
        1 for row in review.values() if row["basis"] == "project_vocabulary"
    )
    public_vocabulary = [
        {
            key: row[key]
            for key in [
                "vocabulary_id", "declaration", "module", "declaration_kind",
                "origin", "design_role", "finiteness_scope",
            ]
        }
        for row in data["vocabulary"]
    ]
    return {
        "schema_version": 2,
        "phase": phase,
        "summary": {
            "active_claims": active_claims,
            "formalization_target_claims": formalization_targets,
            "tombstoned_claims": tombstoned_claims,
            "source_items": len(public_items),
            "mathlib_only_claims": mathlib_only,
            "project_vocabulary_claims": project_vocabulary,
            "vocabulary_declarations": len(public_vocabulary),
            "claim_vocabulary_links": len(data["claim_vocabulary"]),
        },
        "status_semantics": {
            "vocabulary_status": "vocabulary_ready requires both a review row and a vocabulary-reviewed-or-later source lifecycle; review_staged is not ready",
            "binding_status": "not_bound means no binding row is registered",
            "proof_status": "not_recorded does not assert that a proof is absent from the source",
            "axiom_status": "not_assessed is not an axiom-free claim",
        },
        "tracks": tracks,
        "sources": sources,
        "vocabulary": public_vocabulary,
        "groups": list(groups.values()),
        "items": public_items,
    }


def markdown_text(value):
    value = value.replace("\r", " ").replace("\n", " ")
    return html.escape(value, quote=False).replace("|", "&#124;")


def claim_line(claim):
    vocabulary = claim["required_vocabulary"]
    required = ", ".join(
        "`{}`".format(entry["declaration"]) for entry in vocabulary
    ) if vocabulary else "none"
    axioms = claim["axiom_status"]
    return (
        "- `{claim_id}` — {disposition} / {subkind}; lifecycle `{lifecycle}`"
        "{successor}; "
        "Vocabulary `{vocabulary_status}`; binding `{binding_status}`; Lean statement "
        "`{statement}` in `{module}`; proof `{proof_status}` as `{proof}`; "
        "axioms `{axioms}`; required vocabulary: {required}"
    ).format(
        claim_id=claim["claim_id"],
        disposition=markdown_text(claim["disposition"]),
        subkind=markdown_text(claim["subkind"]),
        lifecycle=claim["lifecycle"],
        successor=(
            "; successor `{}`".format(claim["successor_claim"])
            if claim["successor_claim"] != "NONE" else ""
        ),
        vocabulary_status=claim["vocabulary_status"],
        binding_status=claim["binding_status"],
        statement=claim["statement_declaration"],
        module=claim["statement_module"],
        proof_status=claim["proof_status"],
        proof=claim["proof_declaration"],
        axioms=axioms,
        required=required,
    )


def build_outputs(catalog):
    summary = catalog["summary"]
    outputs = {}
    outputs["docs/index.md"] = """# Formalization status

This public documentation is generated deterministically from the registered
source-item and claim metadata. It does not reproduce source claim text or
publish private source paths and object identifiers.

- Current phase: `{phase}`
- Active atomic claims: {active_claims}
- Formalization targets: {formalization_target_claims}
- Superseded claim records: {tombstoned_claims}
- Reviewed source items: {source_items}
- Mathlib-only claims: {mathlib_only_claims}
- Project-vocabulary claims: {project_vocabulary_claims}

See the [generated catalog](generated/index.md). Status values are deliberately
conservative: `not_bound`, `not_recorded`, and `not_assessed` do not mean
proved or axiom-free.
""".format(phase=catalog["phase"], **summary)

    group_links = [
        "- [{} / {}](groups/{}/{}.md) — {} items".format(
            group["source_id"],
            markdown_text(group["public_group"]),
            group["source_public_slug"],
            group["public_slug"],
            len(group["item_ids"]),
        )
        for group in catalog["groups"]
    ]
    source_links = [
        "- [{}](sources/{}.md)".format(
            source["source_id"], source["public_slug"]
        )
        for source in catalog["sources"]
    ]
    track_links = [
        "- [{}](tracks/{}.md)".format(
            markdown_text(track["title"]), track["public_slug"]
        )
        for track in catalog["tracks"]
    ]
    outputs["docs/generated/index.md"] = """# Generated registry catalog

Generated from the checked registries; do not edit by hand.

## Summary

- Phase: `{phase}`
- Source items: {source_items}
- Active claims: {active_claims}
- Formalization targets: {formalization_target_claims}
- Superseded claim records: {tombstoned_claims}
- Vocabulary declarations: {vocabulary_declarations}
- Claim-vocabulary links: {claim_vocabulary_links}

## Tracks

{tracks}

## Sources

{sources}

## Public groups

{groups}

Machine-readable data: [catalog.json](catalog.json).
""".format(
        phase=catalog["phase"],
        tracks="\n".join(track_links),
        sources="\n".join(source_links),
        groups="\n".join(group_links),
        **summary
    )

    items_by_source = defaultdict(list)
    items_by_group = defaultdict(list)
    for item in catalog["items"]:
        items_by_source[item["source_id"]].append(item)
        items_by_group[(item["source_id"], item["public_slug"])].append(item)
    sources_by_track = defaultdict(list)
    for source in catalog["sources"]:
        sources_by_track[source["track_id"]].append(source)
    for track in catalog["tracks"]:
        source_rows = sources_by_track[track["track_id"]]
        track_source_ids = {source["source_id"] for source in source_rows}
        track_items = [
            item for item in catalog["items"]
            if item["source_id"] in track_source_ids
        ]
        track_claims = [
            claim for item in track_items for claim in item["claims"]
        ]
        active_track_claims = [
            claim for claim in track_claims if claim["lifecycle"] == "active"
        ]
        target_track_claims = [
            claim for claim in active_track_claims
            if claim["disposition"] != "out_of_scope"
        ]
        track_vocabulary_ids = {
            row["vocabulary_id"]
            for claim in track_claims for row in claim["required_vocabulary"]
        }
        track_summary = {
            "active_claims": len(active_track_claims),
            "formalization_target_claims": len(target_track_claims),
            "tombstoned_claims": len(track_claims) - len(active_track_claims),
            "mathlib_only_claims": sum(
                claim["vocabulary_basis"] == "mathlib_only"
                for claim in active_track_claims
            ),
            "project_vocabulary_claims": sum(
                claim["vocabulary_basis"] == "project_vocabulary"
                for claim in active_track_claims
            ),
            "claim_vocabulary_links": sum(
                len(claim["required_vocabulary"]) for claim in track_claims
            ),
        }
        source_lines = [
            "- [`{}`](../sources/{}.md) — {}; lifecycle `{}`".format(
                source["source_id"], source["public_slug"],
                markdown_text(source["title"]), source["lifecycle"],
            )
            for source in source_rows
        ]
        vocabulary_lines = [
            "- `{}` — `{}`; kind `{}`; role `{}`; finiteness `{}`".format(
                row["vocabulary_id"], row["declaration"], row["declaration_kind"],
                row["design_role"], row["finiteness_scope"],
            )
            for row in catalog["vocabulary"]
            if row["vocabulary_id"] in track_vocabulary_ids
        ]
        outputs["docs/generated/tracks/{}.md".format(track["public_slug"])] = """# Track: {title}

- Phase: `{phase}`
- Active claims: {active_claims}
- Formalization targets: {formalization_target_claims}
- Superseded claim records: {tombstoned_claims}
- Mathlib-only: {mathlib_only_claims}
- Project vocabulary: {project_vocabulary_claims}
- Complete claim-vocabulary links: {claim_vocabulary_links}

## Sources

{sources}

## Registered vocabulary

{vocabulary}

`vocabulary_ready` records only vocabulary readiness to state future claims. It is not
a statement binding or proof status.
""".format(
            title=markdown_text(track["title"]),
            phase=catalog["phase"],
            sources="\n".join(source_lines),
            vocabulary="\n".join(vocabulary_lines) or "- none",
            **track_summary
        )

    for source in catalog["sources"]:
        source_id = source["source_id"]
        public_reference = (
            "`NONE`"
            if source["public_url"] == "NONE"
            else "[{0}]({0})".format(markdown_text(source["public_url"]))
        )
        groups = OrderedDict()
        for item in items_by_source[source_id]:
            groups[item["public_slug"]] = item["public_group"]
        links = [
            "- [{}](../groups/{}/{}.md) — {} items".format(
                markdown_text(group), source["public_slug"], slug,
                len(items_by_group[(source_id, slug)])
            )
            for slug, group in groups.items()
        ]
        outputs["docs/generated/sources/{}.md".format(source["public_slug"])] = """# {title}

- Source ID: `{source_id}`
- Authors: {authors}
- Year: `{year}`
- Edition: `{edition}`
- Identifier: `{identifier_kind}:{identifier}`
- Public reference: {public_reference}
- Registry lifecycle: `{coverage}`
- Formalization lifecycle: `{lifecycle}`
- Reviewed source items: {count}

Private source paths and object identifiers are intentionally omitted.

## Groups

{groups}
""".format(
            source_id=source_id,
            title=markdown_text(source["title"]),
            authors=markdown_text(source["authors"]),
            year=markdown_text(source["year"]),
            edition=markdown_text(source["edition"]),
            identifier_kind=markdown_text(source["identifier_kind"]),
            identifier=markdown_text(source["identifier"]),
            public_reference=public_reference,
            coverage=markdown_text(source["coverage"]),
            lifecycle=markdown_text(source["lifecycle"]),
            count=len(items_by_source[source_id]),
            groups="\n".join(links),
        )

    for group in catalog["groups"]:
        blocks = []
        group_key = (group["source_id"], group["public_slug"])
        for item in items_by_group[group_key]:
            heading = (
                item["source_label"]
                if item["source_label"] != "NONE"
                else "Unlabeled item " + item["item_id"]
            )
            title_line = (
                "- Title: {}\n".format(markdown_text(item["title"]))
                if item["title"] != "NONE" else "- Title: `NONE`\n"
            )
            display_item = dict(item)
            display_item.pop("claims")
            display_item["locator"] = markdown_text(item["locator"])
            blocks.append("""<a id="{item_id}"></a>

## {heading}

- Item ID: `{item_id}`
- Source: `{source_id}`
- Page ID: `{page_id}`
- Kind: `{item_kind}`
- Source label: `{source_label}`
{title_line}- Locator: {locator}

### Atomic claims

{claims}
""".format(
                heading=markdown_text(heading),
                title_line=title_line,
                claims="\n".join(claim_line(claim) for claim in item["claims"]),
                **display_item
            ))
        outputs[
            "docs/generated/groups/{}/{}.md".format(
                group["source_public_slug"], group["public_slug"]
            )
        ] = (
            "# Group {} / {}\n\n".format(
                group["source_id"], markdown_text(group["public_group"])
            )
            + "Generated from reviewed source-item metadata. Source claim text is not reproduced.\n\n"
            + "\n".join(blocks)
        )

    outputs["docs/generated/catalog.json"] = json.dumps(
        catalog, ensure_ascii=False, indent=2, sort_keys=True
    ) + "\n"
    return outputs


def managed_paths(root):
    docs_index = root / "docs" / "index.md"
    generated = root / "docs" / "generated"
    paths = set()
    if docs_index.is_file():
        paths.add("docs/index.md")
    if generated.is_dir():
        for path in generated.rglob("*"):
            if path.is_file():
                paths.add(path.relative_to(root).as_posix())
    return paths


def write_outputs(root, outputs):
    expected = set(outputs)
    for stale in sorted(managed_paths(root) - expected):
        (root / stale).unlink()
    for relative, content in sorted(outputs.items()):
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text(encoding="utf-8") != content:
            path.write_text(content, encoding="utf-8")
    generated = root / "docs" / "generated"
    if generated.is_dir():
        for directory in sorted(
            (path for path in generated.rglob("*") if path.is_dir()),
            key=lambda path: len(path.parts), reverse=True,
        ):
            try:
                directory.rmdir()
            except OSError:
                pass


def check_outputs(root, outputs, quiet=False):
    expected = set(outputs)
    actual = managed_paths(root)
    errors = []
    for missing in sorted(expected - actual):
        errors.append("missing generated file: " + missing)
    for stale in sorted(actual - expected):
        errors.append("stale generated file: " + stale)
    for relative in sorted(expected & actual):
        if (root / relative).read_text(encoding="utf-8") != outputs[relative]:
            errors.append("outdated generated file: " + relative)
    if errors and not quiet:
        for error in errors:
            print("generate-public-docs: " + error, file=sys.stderr)
    return not errors


class GeneratorTests(unittest.TestCase):
    def test_numeric_chapter_paths_follow_source_order_lexicographically(self):
        chapter_numbers = [1, 2, 9, 10, 11]
        groups = [
            public_group_for(
                {"section": "§{}.1".format(number), "page_kind": "body"},
                "PDF p. {}; §{}.1".format(number, number),
            )
            for number in chapter_numbers
        ]
        paths = [
            "docs/generated/groups/source/{}.md".format(slug_for_group(group))
            for group in groups
        ]
        self.assertEqual(
            groups,
            ["Chapter 01", "Chapter 02", "Chapter 09", "Chapter 10", "Chapter 11"],
        )
        self.assertEqual(paths, sorted(paths))
        self.assertEqual(slug_for_group("Chapter 1"), "chapter-01")
        self.assertEqual(slug_for_group("Appendix A"), "appendix-a")
        self.assertEqual(slug_for_group("Front matter"), "front-matter")

    def test_label_grouping_and_private_data_exclusion(self):
        tracks = [{
            "track_id": "TR-SRC", "position": "1", "title": "Test track",
            "public_slug": "test",
        }]
        sources = [{
            "source_id": "SRC", "track_id": "TR-SRC", "source_position": "1",
            "source_kind": "book", "citation_key": "SRC", "title": "Safe title",
            "authors": "Safe author", "year": "2020", "edition": "safe-edition",
            "identifier_kind": "doi", "identifier": "10.example/test",
            "public_url": "https://example.test", "public_slug": "source",
            "local_ref_key": "PRIVATE-PATH", "pdf_oid": "PRIVATE-PDF-OID",
            "text_oid": "PRIVATE-TEXT-OID", "coverage": "frozen",
        }]
        pages = [{
            "page_id": "PG-SRC-0001", "source_id": "SRC", "order_key": "000001",
            "printed_page": "1", "pdf_page": "1", "section": "§1.1",
            "page_kind": "body", "pass1": "complete", "pass2": "complete",
            "source_oid": "PRIVATE-PAGE-OID",
        }]
        base = {
            "source_id": "SRC", "page_id": "PG-SRC-0001", "disposition": "assertion",
            "subkind": "theorem", "normalized_content": "PRIVATE SOURCE TEXT",
            "content_oid": "PRIVATE-CONTENT-OID", "exclusion_rationale": "NONE",
            "exclusion_review_ref": "NONE", "tombstone": "false",
            "superseded_by": "NONE", "tombstone_rationale": "NONE",
            "tombstone_review_ref": "NONE",
        }
        claims = [
            dict(base, claim_id="CL-SRC-0001", order_key="000001.0001",
                 locator="PDF p. 1; §1.1; Theorem 1.1; atom 1"),
            dict(base, claim_id="CL-SRC-0002", order_key="000001.0002",
                 locator="PDF p. 1; §1.1; Theorem 1.1; atom 2"),
            dict(base, claim_id="CL-SRC-0003", order_key="000001.0003",
                 locator="PDF p. 1; §1.1; paragraph 2"),
        ]
        items, relations = derive_source_items(claims, pages, sources, tracks)
        self.assertEqual(len(items), 2)
        self.assertEqual(items[0]["source_label"], "Theorem 1.1")
        self.assertEqual([row["position"] for row in relations[:2]], ["1", "2"])
        self.assertEqual(items[1]["source_label"], "NONE")
        data = {
            "tracks": tracks,
            "sources": sources,
            "source_progress": [{
                "source_id": "SRC", "lifecycle": "vocabulary_reviewed",
                "review_ref": "REVIEW",
            }],
            "pages": pages,
            "claims": claims,
            "source_items": items,
            "item_claims": relations,
            "claim_vocabulary_review": [
                {"claim_id": claim["claim_id"], "basis": "mathlib_only",
                 "review_ref": "REVIEW"} for claim in claims
            ],
            "vocabulary": [],
            "claim_vocabulary": [],
            "bindings": [],
            "axioms": [],
            "claim_axioms": [],
            "phase": [{"phase": "vocabulary"}],
        }
        outputs = build_outputs(public_catalog(data))
        combined = "".join(outputs.values())
        for private in [
            "PRIVATE SOURCE TEXT", "PRIVATE-CONTENT-OID", "PRIVATE-PATH",
            "PRIVATE-PDF-OID", "PRIVATE-TEXT-OID", "normalized_content",
        ]:
            self.assertNotIn(private, combined)

    def test_two_sources_have_global_order_scoped_groups_and_lifecycle_status(self):
        tracks = [
            {"track_id": "TR-FIRST", "position": "1", "title": "First", "public_slug": "first-track"},
            {"track_id": "TR-SECOND", "position": "2", "title": "Second", "public_slug": "second-track"},
        ]
        source_template = {
            "source_kind": "paper", "authors": "Author", "year": "2026",
            "edition": "v1", "identifier_kind": "none", "identifier": "NONE",
            "public_url": "NONE", "local_ref_key": "PRIVATE", "pdf_oid": "PRIVATE",
            "text_oid": "PRIVATE", "coverage": "frozen",
        }
        sources = [
            dict(source_template, source_id="ZFIRST", track_id="TR-FIRST",
                 source_position="1", citation_key="FIRST", title="First source",
                 public_slug="first-source"),
            dict(source_template, source_id="ASECOND", track_id="TR-SECOND",
                 source_position="1", citation_key="SECOND", title="Second source",
                 public_slug="second-source"),
        ]
        pages = [
            {"page_id": "PG-ZFIRST-0001", "source_id": "ZFIRST", "order_key": "000001",
             "printed_page": "1", "pdf_page": "1", "section": "§1.1",
             "page_kind": "content", "pass1": "complete", "pass2": "complete", "source_oid": "PRIVATE"},
            {"page_id": "PG-ASECOND-0001", "source_id": "ASECOND", "order_key": "000001",
             "printed_page": "1", "pdf_page": "1", "section": "§1.1",
             "page_kind": "content", "pass1": "complete", "pass2": "complete", "source_oid": "PRIVATE"},
        ]
        claim_template = {
            "disposition": "assertion", "subkind": "theorem", "normalized_content": "PRIVATE",
            "content_oid": "PRIVATE", "exclusion_rationale": "NONE",
            "exclusion_review_ref": "NONE", "tombstone": "false", "superseded_by": "NONE",
            "tombstone_rationale": "NONE", "tombstone_review_ref": "NONE",
        }
        # Deliberately reverse input and lexical source-ID order.
        claims = [
            dict(claim_template, claim_id="CL-ASECOND-0001", source_id="ASECOND",
                 order_key="000001.0001", page_id="PG-ASECOND-0001",
                 locator="PDF p. 1; §1.1; Theorem 1.1"),
            dict(claim_template, claim_id="CL-ZFIRST-0001", source_id="ZFIRST",
                 order_key="000001.0001", page_id="PG-ZFIRST-0001",
                 locator="PDF p. 1; §1.1; Theorem 1.1"),
        ]
        items, relations = derive_source_items(claims, pages, sources, tracks)
        self.assertEqual([row["source_id"] for row in items], ["ZFIRST", "ASECOND"])
        data = {
            "tracks": tracks, "sources": sources, "pages": pages, "claims": claims,
            "source_items": items, "item_claims": relations,
            "source_progress": [
                {"source_id": "ZFIRST", "lifecycle": "vocabulary_reviewed", "review_ref": "R"},
                {"source_id": "ASECOND", "lifecycle": "registered", "review_ref": "R"},
            ],
            "claim_vocabulary_review": [
                {"claim_id": row["claim_id"], "basis": "project_vocabulary", "review_ref": "R"}
                for row in claims
            ],
            "vocabulary": [
                {"vocabulary_id": "VO-LS-0001", "declaration": "Fixture.FirstTerm",
                 "module": "Fixture.First", "declaration_kind": "definition",
                 "origin": "primary", "parent_vocabulary_id": "NONE", "type_oid": "PRIVATE",
                 "declaration_oid": "PRIVATE", "design_role": "fixture", "finiteness_scope": "none"},
                {"vocabulary_id": "VO-LS-0002", "declaration": "Fixture.SecondTerm",
                 "module": "Fixture.Second", "declaration_kind": "definition",
                 "origin": "primary", "parent_vocabulary_id": "NONE", "type_oid": "PRIVATE",
                 "declaration_oid": "PRIVATE", "design_role": "fixture", "finiteness_scope": "none"},
            ],
            "claim_vocabulary": [
                {"claim_id": "CL-ZFIRST-0001", "vocabulary_id": "VO-LS-0001"},
                {"claim_id": "CL-ASECOND-0001", "vocabulary_id": "VO-LS-0002"},
            ],
            "axioms": [], "claim_axioms": [],
            "bindings": [{
                "claim_id": "CL-ZFIRST-0001", "statement_decl": "Fixture.statement",
                "proof_decl": "Fixture.proof", "module": "Fixture.Module",
                "statement_oid": "PRIVATE", "nonvacuity_decl": "NONE",
            }],
            "phase": [{"phase": "vocabulary"}],
        }
        catalog = public_catalog(data)
        self.assertEqual(catalog["schema_version"], 2)
        self.assertEqual(catalog["items"][0]["source_id"], "ZFIRST")
        statuses = {
            claim["claim_id"]: claim["vocabulary_status"]
            for item in catalog["items"] for claim in item["claims"]
        }
        self.assertEqual(statuses["CL-ZFIRST-0001"], "vocabulary_ready")
        self.assertEqual(statuses["CL-ASECOND-0001"], "review_staged")
        outputs = build_outputs(catalog)
        first_path = "docs/generated/groups/first-source/chapter-01.md"
        second_path = "docs/generated/groups/second-source/chapter-01.md"
        self.assertIn(first_path, outputs)
        self.assertIn(second_path, outputs)
        self.assertIn("CL-ZFIRST-0001", outputs[first_path])
        self.assertNotIn("CL-ASECOND-0001", outputs[first_path])
        self.assertIn("Fixture.statement", outputs[first_path])
        self.assertIn("Fixture.Module", outputs[first_path])
        self.assertIn("Fixture.proof", outputs[first_path])
        self.assertIn("Reviewed source items: 1", outputs["docs/generated/sources/first-source.md"])
        self.assertIn("Reviewed source items: 1", outputs["docs/generated/sources/second-source.md"])
        first_track = outputs["docs/generated/tracks/first-track.md"]
        second_track = outputs["docs/generated/tracks/second-track.md"]
        self.assertIn("Active claims: 1", first_track)
        self.assertIn("Active claims: 1", second_track)
        self.assertIn("Fixture.FirstTerm", first_track)
        self.assertNotIn("Fixture.SecondTerm", first_track)
        self.assertIn("Fixture.SecondTerm", second_track)
        self.assertNotIn("Fixture.FirstTerm", second_track)
        self.assertIn("Public reference: `NONE`", outputs["docs/generated/sources/first-source.md"])
        self.assertNotIn("[NONE](NONE)", outputs["docs/generated/sources/first-source.md"])

    def test_write_and_check_use_tempfile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            outputs = {
                "docs/index.md": "# Public\n",
                "docs/generated/index.md": "# Generated\n",
                "docs/generated/catalog.json": '{"safe": true}\n',
            }
            write_outputs(root, outputs)
            self.assertTrue(check_outputs(root, outputs, quiet=True))
            (root / "docs/generated/index.md").write_text("drift\n", encoding="utf-8")
            self.assertFalse(check_outputs(root, outputs, quiet=True))


def main(argv=None):
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--test", action="store_true")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args(argv)
    if args.test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(GeneratorTests)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1
    root = args.root.resolve()
    try:
        data = load_registry(root)
        catalog = public_catalog(data)
        outputs = build_outputs(catalog)
        if args.write:
            write_outputs(root, outputs)
            print("generate-public-docs: wrote {} files".format(len(outputs)))
            return 0
        if not check_outputs(root, outputs):
            return 1
        print("generate-public-docs: ok ({} files)".format(len(outputs)))
        return 0
    except (CatalogError, OSError, csv.Error, ValueError, KeyError) as error:
        print("generate-public-docs: {}".format(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
