#!/usr/bin/env python3
"""Verify the deployed formalization-status Pages surface after publication."""

from __future__ import annotations

import argparse
import json
import re
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Callable
from urllib.parse import urljoin

from check_generated_site import (
    PageParser,
    assert_metadata,
    canonical_record_href,
    expected_marker_body,
    expected_overview_index_rows,
    expected_projection_rows,
    expected_source_index_rows,
    expected_status_index_rows,
    expected_topic_index_rows,
    parse_record_html,
    records_for_source,
    records_for_topic,
    reject_authority_contradictions,
    require_index_rows,
    require_generated_ownership,
    validate_record_blocks,
)
from validate_formalization_status import Validation, validate_schema_instance


PAGES_BASE = "https://phasetr.github.io/lattice-system/"
CORE_HUMAN_ENDPOINTS = (
    "formalization/",
    "formalization/status/",
    "formalization/sources/",
    "formalization/topics/",
)
JSON_ENDPOINTS = (
    "formalization-status/v1/catalog.json",
    "formalization-status/v1/schema.json",
    "formalization-status/v1/publication.json",
)
BOOTSTRAP_ENDPOINTS = (*CORE_HUMAN_ENDPOINTS, *JSON_ENDPOINTS)
COMPATIBILITY_RECORD_IDS = (
    "shastry-1992-staggered-susceptibility-bound",
    "tasaki-2020-section-2-1-pauli-x-involutive",
    "tasaki-2020-theorem-3-1-finite-dimensional-core",
    "tasaki-2020-theorem-4-2-shastry-no-ssb",
)
SHA256_RE = re.compile(r"[0-9a-f]{64}")
REVISION_RE = re.compile(r"[0-9a-f]{40}")
MAX_BODY_BYTES = 8 * 1024 * 1024
MAX_DEADLINE_SECONDS = 240
CATALOG_KEYS = {
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
PUBLICATION_KEYS = {
    "catalog_state",
    "generated_by",
    "generator_version",
    "input_sha256",
    "revision",
    "schema_version",
}


@dataclass(frozen=True)
class Response:
    """Represent one exact HTTP response needed by the live verifier."""

    status: int
    content_type: str
    body: bytes
    final_url: str


Fetcher = Callable[[str, float], Response]


class NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Reject redirects so every stable endpoint must itself return HTTP 200."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):  # type: ignore[no-untyped-def]
        """Disable urllib's default redirect following."""
        return None


def validate_base_url(base_url: str) -> str:
    """Accept only the repository's fixed HTTPS GitHub Pages base URL."""
    if base_url != PAGES_BASE:
        raise ValueError(f"base URL must be exactly {PAGES_BASE}")
    return base_url


def validate_declared_length(value: str, url: str) -> int:
    """Parse and bound an HTTP Content-Length value before reading the body."""
    try:
        declared_length = int(value)
    except ValueError as error:
        raise ValueError(f"{url}: invalid Content-Length") from error
    if declared_length < 0 or declared_length > MAX_BODY_BYTES:
        raise ValueError(f"{url}: Content-Length exceeds the byte limit")
    return declared_length


def fetch_url(url: str, timeout: float) -> Response:
    """Fetch one endpoint without credentials using a bounded request timeout."""
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "text/html, application/json",
            "User-Agent": "lattice-system-publication-check/1",
        },
    )
    opener = urllib.request.build_opener(NoRedirectHandler())
    with opener.open(request, timeout=timeout) as response:
        content_length = response.headers.get("Content-Length")
        if content_length is not None:
            validate_declared_length(content_length, url)
        body = response.read(MAX_BODY_BYTES + 1)
        if len(body) > MAX_BODY_BYTES:
            raise ValueError(f"{url}: response body exceeds the byte limit")
        return Response(
            status=response.status,
            content_type=response.headers.get_content_type(),
            body=body,
            final_url=response.geturl(),
        )


def parse_json(response: Response, endpoint: str) -> dict[str, object]:
    """Require an exact successful JSON response and decode an object."""
    if response.status != 200:
        raise ValueError(f"{endpoint}: expected HTTP 200, got {response.status}")
    if response.content_type != "application/json":
        raise ValueError(
            f"{endpoint}: expected application/json, got {response.content_type}"
        )
    try:
        value = json.loads(response.body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"{endpoint}: invalid UTF-8 JSON") from error
    if not isinstance(value, dict):
        raise ValueError(f"{endpoint}: top-level JSON value must be an object")
    return value


def parse_human(response: Response, endpoint: str) -> PageParser:
    """Require an exact successful HTML response and parse generated structures."""
    if response.status != 200:
        raise ValueError(f"{endpoint}: expected HTTP 200, got {response.status}")
    if response.content_type != "text/html":
        raise ValueError(f"{endpoint}: expected text/html, got {response.content_type}")
    try:
        source = response.body.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{endpoint}: invalid UTF-8 HTML") from error
    return parse_record_html(source, endpoint)


def require_metadata(
    parser: PageParser, endpoint: str, catalog: dict[str, object], revision: str
) -> None:
    """Require the exact ordered metadata grammar and generated notice."""
    assert_metadata(parser, catalog, revision, endpoint)
    visible = " ".join("".join(parser.text).split())
    if "Generated formalization-status view." not in visible:
        raise ValueError(f"{endpoint}: generated notice is missing")


def require_navigation(
    pages: dict[str, PageParser], catalog: dict[str, object]
) -> None:
    """Require exact ordered overview, source, topic, and status rows."""
    overview = pages["formalization/"]
    require_index_rows(
        overview,
        expected_overview_index_rows(catalog),
        "formalization/",
    )
    require_index_rows(
        pages["formalization/sources/"],
        expected_source_index_rows(catalog),
        "formalization/sources/",
    )
    require_index_rows(
        pages["formalization/topics/"],
        expected_topic_index_rows(catalog),
        "formalization/topics/",
    )
    require_index_rows(
        pages["formalization/status/"],
        expected_status_index_rows(catalog),
        "formalization/status/",
    )


def expected_human_endpoints(catalog: dict[str, object]) -> tuple[str, ...]:
    """Derive the bounded live surface: all projections plus pinned compatibility details."""
    sources = catalog.get("sources")
    topics = catalog.get("topics")
    records = catalog.get("records")
    if not isinstance(sources, list) or not isinstance(topics, list) or not isinstance(records, list):
        raise ValueError("catalogue human-route registries must be arrays")
    source_ids = [item.get("id") for item in sources if isinstance(item, dict)]
    topic_ids = [item.get("id") for item in topics if isinstance(item, dict)]
    record_ids = {item.get("id") for item in records if isinstance(item, dict)}
    if (
        len(source_ids) != len(sources)
        or len(topic_ids) != len(topics)
        or any(not isinstance(item, str) for item in [*source_ids, *topic_ids])
    ):
        raise ValueError("catalogue source/topic route IDs are invalid")
    missing_compatibility = set(COMPATIBILITY_RECORD_IDS) - record_ids
    if missing_compatibility:
        raise ValueError(
            f"catalogue removed pinned public record routes: {sorted(missing_compatibility)}"
        )
    return (
        *CORE_HUMAN_ENDPOINTS,
        *(f"formalization/sources/{identifier}/" for identifier in source_ids),
        "formalization/sources/foundations/",
        *(f"formalization/topics/{identifier}/" for identifier in topic_ids),
        *(f"formalization/records/{identifier}/" for identifier in COMPATIBILITY_RECORD_IDS),
    )


def endpoint_marker_specification(endpoint: str) -> str:
    """Map one fetched human endpoint to its exact generated marker owner."""
    fixed = {
        "formalization/": "overview",
        "formalization/status/": "status",
        "formalization/sources/": "source-index",
        "formalization/sources/foundations/": "project-original",
        "formalization/topics/": "topic-index",
    }
    if endpoint in fixed:
        return fixed[endpoint]
    match = re.fullmatch(r"formalization/(sources|topics|records)/([^/]+)/", endpoint)
    if match is None:
        raise ValueError(f"unknown human endpoint marker ownership: {endpoint}")
    kind = {"sources": "source", "topics": "topic", "records": "record"}[
        match.group(1)
    ]
    return f"{kind} {match.group(2)}"


def require_projection_surface(
    pages: dict[str, PageParser], catalog: dict[str, object]
) -> None:
    """Require exact live source/topic/status membership and pinned record details."""
    typed_catalog = catalog  # Runtime checks below consume the JSON object structurally.
    for source in typed_catalog["sources"]:  # type: ignore[index]
        source_id = source["id"]
        endpoint = f"formalization/sources/{source_id}/"
        parser = pages[endpoint]
        require_index_rows(
            parser,
            expected_projection_rows(
                records_for_source(typed_catalog, source_id), "source", source_id  # type: ignore[arg-type]
            ),
            endpoint,
        )
        if parser.record_fields:
            raise ValueError(f"{endpoint}: projection duplicates full record truth")
    foundation_endpoint = "formalization/sources/foundations/"
    project_records = [
        record
        for record in typed_catalog["records"]  # type: ignore[index]
        if record["origin"] == "project_original"
    ]
    require_index_rows(
        pages[foundation_endpoint],
        expected_projection_rows(project_records, "source", "foundations"),
        foundation_endpoint,
    )
    if pages[foundation_endpoint].record_fields:
        raise ValueError(f"{foundation_endpoint}: projection duplicates full record truth")
    for topic in typed_catalog["topics"]:  # type: ignore[index]
        topic_id = topic["id"]
        endpoint = f"formalization/topics/{topic_id}/"
        parser = pages[endpoint]
        require_index_rows(
            parser,
            expected_projection_rows(
                records_for_topic(typed_catalog, topic_id), "topic", topic_id  # type: ignore[arg-type]
            ),
            endpoint,
        )
        if parser.record_fields:
            raise ValueError(f"{endpoint}: projection duplicates full record truth")
    if pages["formalization/status/"].record_fields:
        raise ValueError("formalization/status/: projection duplicates full record truth")
    record_map = {
        record["id"]: record for record in typed_catalog["records"]  # type: ignore[index]
    }
    item_map = {
        item["id"]: item for item in typed_catalog["source_items"]  # type: ignore[index]
    }
    for record_id in COMPATIBILITY_RECORD_IDS:
        endpoint = f"formalization/records/{record_id}/"
        record = record_map[record_id]
        validate_record_blocks(pages[endpoint], [record], typed_catalog, endpoint)  # type: ignore[arg-type]
        href = canonical_record_href(record_id)
        anchor = f"record-{record_id}"
        related_sources = {
            item_map[relation["source_item_id"]]["source_id"]
            for relation in record["source_relations"]
        }
        compatibility_pages = [
            pages["formalization/status/"],
            *(pages[f"formalization/sources/{source_id}/"] for source_id in related_sources),
            *(pages[f"formalization/topics/{topic_id}/"] for topic_id in record["topic_ids"]),
        ]
        if record["origin"] == "project_original":
            compatibility_pages.append(pages[foundation_endpoint])
        if not all(anchor in parser.ids and href in parser.links for parser in compatibility_pages):
            raise ValueError(f"{endpoint}: a pinned legacy projection anchor/link is missing")


def verify_responses(
    responses: dict[str, Response],
    base_url: str,
    revision: str,
    canonical_schema_bytes: bytes,
) -> None:
    """Validate one coherent machine surface and scalable human projection snapshot."""
    validate_base_url(base_url)
    missing_bootstrap = set(BOOTSTRAP_ENDPOINTS) - set(responses)
    if missing_bootstrap:
        raise ValueError(f"live response set lacks bootstrap endpoints: {sorted(missing_bootstrap)}")
    for endpoint, response in responses.items():
        if len(response.body) > MAX_BODY_BYTES:
            raise ValueError(f"{endpoint}: response body exceeds the byte limit")
        expected_url = urljoin(base_url, endpoint)
        if response.final_url != expected_url:
            raise ValueError(f"{endpoint}: unexpected redirect to {response.final_url}")

    catalog = parse_json(responses[JSON_ENDPOINTS[0]], JSON_ENDPOINTS[0])
    expected_endpoints = {*JSON_ENDPOINTS, *expected_human_endpoints(catalog)}
    if set(responses) != expected_endpoints:
        raise ValueError("live response set does not match the catalogue-derived route surface")
    schema_response = responses[JSON_ENDPOINTS[1]]
    schema = parse_json(schema_response, JSON_ENDPOINTS[1])
    publication = parse_json(responses[JSON_ENDPOINTS[2]], JSON_ENDPOINTS[2])
    if set(catalog) != CATALOG_KEYS:
        raise ValueError("published catalogue has missing or additional top-level keys")
    if set(publication) != PUBLICATION_KEYS:
        raise ValueError("publication sidecar has missing or additional top-level keys")
    if (
        catalog.get("generated_by") != "scripts/validate_formalization_status.py"
        or catalog.get("generator_version") != 2
    ):
        raise ValueError("published catalogue has the wrong generator identity or version")
    if (
        publication.get("generated_by") != "scripts/generate_formalization_site.py"
        or publication.get("generator_version") != 2
    ):
        raise ValueError("publication sidecar has the wrong generator identity or version")
    digest = catalog.get("input_sha256")
    if catalog.get("schema_version") != 1 or publication.get("schema_version") != 1:
        raise ValueError("catalog/publication schema_version must both equal 1")
    if (
        catalog.get("catalog_state") not in {"prototype", "authoritative"}
        or publication.get("catalog_state") != catalog.get("catalog_state")
    ):
        raise ValueError(
            "catalog/publication catalog_state must match a supported catalogue state"
        )
    if not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None:
        raise ValueError("catalog input_sha256 is invalid")
    if publication.get("input_sha256") != digest:
        raise ValueError("catalog/publication input_sha256 values differ")
    if publication.get("revision") != revision:
        raise ValueError("publication revision does not equal the required main SHA")
    try:
        canonical_schema = json.loads(canonical_schema_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError("checkout canonical schema is invalid UTF-8 JSON") from error
    if schema != canonical_schema:
        raise ValueError("published schema differs from the checkout canonical schema")
    aggregate_schema = canonical_schema.get("$defs", {}).get("aggregate")
    if not isinstance(aggregate_schema, dict):
        raise ValueError("checkout canonical schema lacks the aggregate contract")
    schema_validation = Validation()
    validate_schema_instance(
        catalog,
        aggregate_schema,
        canonical_schema,
        "published catalogue",
        schema_validation,
    )
    if schema_validation.errors:
        raise ValueError(
            "published catalogue violates the canonical schema: "
            + "; ".join(schema_validation.errors)
        )

    pages = {
        endpoint: parse_human(responses[endpoint], endpoint)
        for endpoint in expected_human_endpoints(catalog)
    }
    for endpoint, parser in pages.items():
        specification = endpoint_marker_specification(endpoint)
        require_generated_ownership(parser, endpoint, specification)
        rendered_marker = (
            f"<!-- formalization-status-generated:start {specification} -->\n"
            + expected_marker_body(specification, catalog, revision)
            + "<!-- formalization-status-generated:end -->"
        ).encode()
        if responses[endpoint].body.count(rendered_marker) != 1:
            raise ValueError(f"{endpoint}: generated owned region is not exact")
    reject_authority_contradictions(
        catalog,
        [(endpoint, " ".join(parser.text)) for endpoint, parser in pages.items()],
    )
    for endpoint, parser in pages.items():
        require_metadata(parser, endpoint, catalog, revision)
    require_navigation(pages, catalog)
    require_projection_surface(pages, catalog)


def fetch_publication(
    base_url: str,
    timeout: float,
    fetcher: Fetcher,
    deadline_at: float,
    monotonic: Callable[[], float],
) -> dict[str, Response]:
    """Fetch one coherent catalogue-derived snapshot within the absolute deadline."""
    responses = {}
    for endpoint in BOOTSTRAP_ENDPOINTS:
        remaining = deadline_at - monotonic()
        if remaining <= 0:
            raise ValueError("live publication deadline expired during a snapshot")
        responses[endpoint] = fetcher(
            urljoin(base_url, endpoint), min(timeout, remaining)
        )
    catalog = parse_json(responses[JSON_ENDPOINTS[0]], JSON_ENDPOINTS[0])
    additional = [
        endpoint
        for endpoint in expected_human_endpoints(catalog)
        if endpoint not in responses
    ]
    for endpoint in additional:
        remaining = deadline_at - monotonic()
        if remaining <= 0:
            raise ValueError("live publication deadline expired during a snapshot")
        responses[endpoint] = fetcher(
            urljoin(base_url, endpoint), min(timeout, remaining)
        )
    return responses


def verify_with_retry(
    base_url: str,
    revision: str,
    attempts: int,
    initial_delay: float,
    timeout: float,
    deadline: float,
    canonical_schema_bytes: bytes,
    fetcher: Fetcher = fetch_url,
    sleep: Callable[[float], None] = time.sleep,
    monotonic: Callable[[], float] = time.monotonic,
) -> None:
    """Retry coherent verification within one workflow-safe absolute deadline."""
    validate_base_url(base_url)
    if REVISION_RE.fullmatch(revision) is None:
        raise ValueError("revision must be a 40-character lowercase hexadecimal SHA")
    if not 1 <= attempts <= 10:
        raise ValueError("attempts must be between 1 and 10")
    if not 0 <= initial_delay <= 30 or not 1 <= timeout <= 30:
        raise ValueError("retry delay/timeout is outside the safe bound")
    if not 1 <= deadline <= MAX_DEADLINE_SECONDS:
        raise ValueError(f"deadline must be between 1 and {MAX_DEADLINE_SECONDS} seconds")
    deadline_at = monotonic() + deadline
    last_error: Exception | None = None
    for attempt in range(attempts):
        try:
            verify_responses(
                fetch_publication(
                    base_url, timeout, fetcher, deadline_at, monotonic
                ),
                base_url,
                revision,
                canonical_schema_bytes,
            )
            return
        except (ValueError, OSError, urllib.error.URLError) as error:
            last_error = error
            if attempt + 1 < attempts:
                remaining = deadline_at - monotonic()
                delay = min(initial_delay * (2**attempt), 30, remaining)
                if delay <= 0:
                    break
                sleep(delay)
    raise ValueError(f"live publication check failed after {attempts} attempt(s): {last_error}")


def fixture_responses(
    revision: str, catalog_state: str = "prototype", record_count: int = 4
) -> dict[str, Response]:
    """Build a complete scalable-route fixture for dependency-free self-tests."""
    if record_count < len(COMPATIBILITY_RECORD_IDS):
        raise ValueError("live fixture must retain every pinned compatibility record")
    digest = "a" * 64
    records = []
    for index, record_id in enumerate(COMPATIBILITY_RECORD_IDS):
        records.append(
            {
                "axiom_dependencies": [],
                "capstone": bool(index % 2),
                "declaration_kind": "theorem",
                "id": record_id,
                "implementation_state": "implemented",
                "lean_name": f"LatticeSystem.Fixture.result{index}",
                "module": "LatticeSystem.Fixture",
                "origin": "literature",
                "proof_guide_anchor": None,
                "source_coverage": "complete",
                "source_path": "LatticeSystem/Fixture.lean",
                "source_relations": [
                    {"source_item_id": "book-item", "relation": "formalizes"}
                ],
                "summary": f"Fixture result {index}",
                "topic_ids": ["spin"],
                "trust_state": "axiom_free",
            }
        )
    for index in range(record_count - len(COMPATIBILITY_RECORD_IDS)):
        records.append(
            {
                **records[0],
                "id": f"zz-fixture-record-{index:04d}",
                "lean_name": f"LatticeSystem.Fixture.scaledResult{index}",
                "summary": f"Scaled fixture result {index}",
            }
        )
    catalog: dict[str, object] = {
        "schema_version": 1,
        "catalog_state": catalog_state,
        "generated_by": "scripts/validate_formalization_status.py",
        "generator_version": 2,
        "input_sha256": digest,
        "sources": [
            {"authors": ["Fixture Author"], "id": "book", "title": "Book", "year": 2026}
        ],
        "source_items": [
            {
                "equations": [],
                "id": "book-item",
                "item_kind": "theorem",
                "item_number": "1",
                "pages": "1",
                "section": "1",
                "source_id": "book",
                "title": "Book result",
            }
        ],
        "topics": [{"description": "Spin fixture", "id": "spin", "label": "Spin"}],
        "records": records,
    }

    from generate_formalization_site import render_marker

    specifications = {
        "formalization/": "overview",
        "formalization/status/": "status",
        "formalization/sources/": "source-index",
        "formalization/topics/": "topic-index",
        "formalization/sources/book/": "source book",
        "formalization/sources/foundations/": "project-original",
        "formalization/topics/spin/": "topic spin",
        **{
            f"formalization/records/{record_id}/": f"record {record_id}"
            for record_id in COMPATIBILITY_RECORD_IDS
        },
    }
    human = {
        endpoint: render_marker(specification, catalog, revision)
        for endpoint, specification in specifications.items()
    }
    publication = {
        "schema_version": 1,
        "catalog_state": catalog_state,
        "generated_by": "scripts/generate_formalization_site.py",
        "generator_version": 2,
        "input_sha256": digest,
        "revision": revision,
    }
    payloads: dict[str, tuple[str, bytes]] = {
        **{key: ("text/html", value.encode()) for key, value in human.items()},
        JSON_ENDPOINTS[0]: ("application/json", json.dumps(catalog).encode()),
        JSON_ENDPOINTS[1]: (
            "application/json",
            (
                Path(__file__).resolve().parents[1]
                / "formalization-status/v1/schema.json"
            ).read_bytes(),
        ),
        JSON_ENDPOINTS[2]: ("application/json", json.dumps(publication).encode()),
    }
    return {
        endpoint: Response(200, content_type, body, urljoin(PAGES_BASE, endpoint))
        for endpoint, (content_type, body) in payloads.items()
    }


def run_self_tests() -> None:
    """Exercise positive, retry, and representative semantic failure paths."""
    revision = "1" * 40
    fixture = fixture_responses(revision)
    canonical_schema = fixture[JSON_ENDPOINTS[1]].body
    verify_responses(fixture, PAGES_BASE, revision, canonical_schema)
    scaled_fixture = fixture_responses(revision, record_count=1000)
    verify_responses(scaled_fixture, PAGES_BASE, revision, canonical_schema)
    if len(scaled_fixture) != 14:
        raise AssertionError("1000-record live fixture exceeded the bounded endpoint policy")
    authoritative_fixture = fixture_responses(revision, "authoritative")
    verify_responses(
        authoritative_fixture,
        PAGES_BASE,
        revision,
        authoritative_fixture[JSON_ENDPOINTS[1]].body,
    )
    stale_authoritative = dict(authoritative_fixture)
    stale_overview = stale_authoritative["formalization/"]
    stale_authoritative["formalization/"] = Response(
        stale_overview.status,
        stale_overview.content_type,
        stale_overview.body + b"<p>The interim legacy catalogue remains authoritative.</p>",
        stale_overview.final_url,
    )
    try:
        verify_responses(
            stale_authoritative,
            PAGES_BASE,
            revision,
            authoritative_fixture[JSON_ENDPOINTS[1]].body,
        )
    except ValueError:
        pass
    else:
        raise AssertionError("authoritative live page accepted stale legacy-authority prose")

    def changed_response(endpoint: str, old: bytes, new: bytes) -> dict[str, Response]:
        """Replace one unique byte sequence in a coherent live fixture."""
        changed = dict(fixture)
        original = changed[endpoint]
        if original.body.count(old) != 1:
            raise AssertionError(f"A2 live mutation target is not unique: {old!r}")
        changed[endpoint] = Response(
            original.status,
            original.content_type,
            original.body.replace(old, new, 1),
            original.final_url,
        )
        return changed

    first_id = COMPATIBILITY_RECORD_IDS[0]
    first_detail = f"formalization/records/{first_id}/"
    negative_fixtures = [
        (
            "wrong canonical detail field",
            changed_response(
                first_detail,
                b'<dd data-field="implementation-state">implemented</dd>',
                b'<dd data-field="implementation-state">in_progress</dd>',
            ),
        ),
        (
            "wrong compact projection link",
            changed_response(
                "formalization/sources/book/",
                f'data-href="{canonical_record_href(first_id)}"'.encode(),
                b'data-href="/lattice-system/formalization/records/wrong/"',
            ),
        ),
        (
            "missing compatibility anchor",
            changed_response(
                "formalization/topics/spin/",
                f'id="record-{first_id}"'.encode(),
                b'id="record-wrong"',
            ),
        ),
    ]
    projection_end = b'</div>\n<!-- formalization-status-generated:end -->'
    negative_fixtures.extend(
        [
            (
                "stripped-identity full record projection leak",
                changed_response(
                    "formalization/sources/book/",
                    projection_end,
                    b"<article><h3>Stripped identity</h3><dl><dt>Implementation state</dt>"
                    b"<dd>implemented</dd></dl></article>\n" + projection_end,
                ),
            ),
            (
                "unowned paragraph in generated projection",
                changed_response(
                    "formalization/sources/book/",
                    projection_end,
                    b"<p>poison</p>\n" + projection_end,
                ),
            ),
        ]
    )

    def changed_json(
        endpoint: str, key: str, value: object | None, remove: bool = False
    ) -> dict[str, Response]:
        """Mutate one machine-object key while retaining a coherent HTTP fixture."""
        changed = dict(fixture)
        response = changed[endpoint]
        payload = json.loads(response.body)
        if remove:
            payload.pop(key)
        else:
            payload[key] = value
        changed[endpoint] = Response(
            response.status,
            response.content_type,
            json.dumps(payload).encode(),
            response.final_url,
        )
        return changed

    negative_fixtures.extend(
        [
            (
                "missing catalogue generator identity",
                changed_json(JSON_ENDPOINTS[0], "generated_by", None, remove=True),
            ),
            (
                "wrong catalogue generator version",
                changed_json(JSON_ENDPOINTS[0], "generator_version", 1),
            ),
            (
                "additional catalogue key",
                changed_json(JSON_ENDPOINTS[0], "unexpected", True),
            ),
            (
                "missing publication generator identity",
                changed_json(JSON_ENDPOINTS[2], "generated_by", None, remove=True),
            ),
            (
                "wrong publication generator version",
                changed_json(JSON_ENDPOINTS[2], "generator_version", 1),
            ),
            (
                "additional publication key",
                changed_json(JSON_ENDPOINTS[2], "unexpected", True),
            ),
        ]
    )

    def changed_nested_catalog(
        collection: str, field: str, value: object | None, remove: bool = False
    ) -> dict[str, Response]:
        """Mutate one nested catalogue object without changing route identities."""
        changed = dict(fixture)
        response = changed[JSON_ENDPOINTS[0]]
        payload = json.loads(response.body)
        target = payload[collection][0]
        if remove:
            target.pop(field)
        else:
            target[field] = value
        changed[JSON_ENDPOINTS[0]] = Response(
            response.status,
            response.content_type,
            json.dumps(payload).encode(),
            response.final_url,
        )
        return changed

    nested_schema_mutations = []
    for collection, required_field, typed_field, wrong_value in (
        ("records", "summary", "capstone", "false"),
        ("sources", "authors", "title", []),
        ("source_items", "pages", "equations", "none"),
        ("topics", "label", "label", []),
    ):
        nested_schema_mutations.extend(
            [
                (
                    f"additional nested {collection} field",
                    changed_nested_catalog(collection, "unexpected", True),
                ),
                (
                    f"missing nested {collection} field",
                    changed_nested_catalog(
                        collection, required_field, None, remove=True
                    ),
                ),
                (
                    f"wrong nested {collection} field type",
                    changed_nested_catalog(collection, typed_field, wrong_value),
                ),
            ]
        )
    for label, changed in nested_schema_mutations:
        try:
            verify_responses(changed, PAGES_BASE, revision, canonical_schema)
        except ValueError as error:
            if "violates the canonical schema" not in str(error):
                raise AssertionError(
                    f"nested schema mutation failed for an unrelated reason: {label}: {error}"
                ) from error
        else:
            raise AssertionError(f"nested schema mutation was accepted: {label}")
    wrong_revision = dict(json.loads(fixture[JSON_ENDPOINTS[2]].body))
    wrong_revision["revision"] = "2" * 40
    revision_fixture = dict(fixture)
    publication_response = revision_fixture[JSON_ENDPOINTS[2]]
    revision_fixture[JSON_ENDPOINTS[2]] = Response(
        publication_response.status,
        publication_response.content_type,
        json.dumps(wrong_revision).encode(),
        publication_response.final_url,
    )
    negative_fixtures.append(("wrong revision", revision_fixture))
    missing_detail = dict(fixture)
    missing_detail.pop(first_detail)
    negative_fixtures.append(("missing pinned record route", missing_detail))
    removed_record = dict(fixture)
    removed_catalog = dict(json.loads(removed_record[JSON_ENDPOINTS[0]].body))
    removed_catalog["records"] = [
        record for record in removed_catalog["records"] if record["id"] != first_id
    ]
    catalog_response = removed_record[JSON_ENDPOINTS[0]]
    removed_record[JSON_ENDPOINTS[0]] = Response(
        catalog_response.status,
        catalog_response.content_type,
        json.dumps(removed_catalog).encode(),
        catalog_response.final_url,
    )
    negative_fixtures.append(("removed pinned record identity", removed_record))
    for label, changed in negative_fixtures:
        try:
            verify_responses(changed, PAGES_BASE, revision, canonical_schema)
        except ValueError:
            pass
        else:
            raise AssertionError(f"live A2 semantic mutation was accepted: {label}")

    calls = 0
    clock = [0.0]
    sleeps: list[float] = []

    def flaky_fetcher(url: str, timeout: float) -> Response:
        """Fail once, then serve the complete catalogue-derived fixture."""
        nonlocal calls
        calls += 1
        if calls == 1:
            raise urllib.error.URLError("not propagated")
        return fixture[url.removeprefix(PAGES_BASE)]

    verify_with_retry(
        PAGES_BASE,
        revision,
        attempts=2,
        initial_delay=1,
        timeout=1,
        deadline=30,
        canonical_schema_bytes=canonical_schema,
        fetcher=flaky_fetcher,
        sleep=lambda delay: (sleeps.append(delay), clock.__setitem__(0, clock[0] + delay)),
        monotonic=lambda: clock[0],
    )
    if sleeps != [1]:
        raise AssertionError("bounded A2 retry self-test used an unexpected delay")
    mutations: list[tuple[str, dict[str, Response]]] = []

    def mutate(endpoint: str, old: bytes, new: bytes) -> dict[str, Response]:
        """Replace one exact byte sequence in one fixture response."""
        changed = dict(fixture)
        original = changed[endpoint]
        if original.body.count(old) != 1:
            raise AssertionError(f"self-test mutation target is not unique: {old!r}")
        changed[endpoint] = Response(
            original.status,
            original.content_type,
            original.body.replace(old, new, 1),
            original.final_url,
        )
        return changed

    wrong_revision = dict(json.loads(fixture[JSON_ENDPOINTS[2]].body))
    wrong_revision["revision"] = "2" * 40
    source_row_start = b'<li data-row-kind="source"'
    source_body = fixture["formalization/sources/"].body
    source_row = source_row_start + source_body.split(source_row_start, 1)[1].split(
        b"</li>", 1
    )[0] + b"</li>"
    status_row_start = b'<li data-row-kind="status-count"'
    status_body = fixture["formalization/status/"].body
    status_row = status_row_start + status_body.split(status_row_start, 1)[1].split(
        b"</li>", 1
    )[0] + b"</li>"
    catalog_meta_start = b'<li data-meta="catalog-link"'
    overview_body = fixture["formalization/"].body
    catalog_meta = catalog_meta_start + overview_body.split(
        catalog_meta_start, 1
    )[1].split(b"</li>", 1)[0] + b"</li>"
    schema_poison = dict(json.loads(canonical_schema))
    schema_poison["poison"] = True
    wrong_source_anchor = mutate(
        "formalization/sources/",
        b'<a href="/lattice-system/formalization/sources/book/">',
        b'<a href="/lattice-system/formalization/sources/wrong/">',
    )
    unrelated_anchor = dict(wrong_source_anchor)
    unrelated_original = unrelated_anchor["formalization/sources/"]
    unrelated_anchor["formalization/sources/"] = Response(
        200,
        unrelated_original.content_type,
        unrelated_original.body
        + b'<a href="/lattice-system/formalization/sources/book/">unrelated</a>',
        unrelated_original.final_url,
    )

    semantic_mutations = (
        (
            "missing navigation",
            mutate(
                "formalization/",
                b'<a href="/lattice-system/formalization/topics/">',
                b'<a href="/lattice-system/formalization/missing/">',
            ),
        ),
        (
            "wrong count",
            mutate(
                "formalization/sources/",
                b'data-record-count="4"',
                b'data-record-count="5"',
            ),
        ),
        (
            "wrong label",
            mutate(
                "formalization/topics/",
                b'data-topic-label="Spin"',
                b'data-topic-label="Wrong"',
            ),
        ),
        (
            "wrong visible label",
            mutate(
                "formalization/topics/",
                b">Spin: 4 record(s)</a>",
                b">Wrong: 4 record(s)</a>",
            ),
        ),
        (
            "wrong kind",
            mutate(
                "formalization/sources/",
                b'data-row-kind="source"',
                b'data-row-kind="topic"',
            ),
        ),
        (
            "duplicate source row",
            mutate("formalization/sources/", source_row, source_row + source_row),
        ),
        (
            "duplicate status row",
            mutate("formalization/status/", status_row, status_row + status_row),
        ),
        (
            "extra status row",
            mutate(
                "formalization/status/",
                status_row,
                status_row
                + b'<li data-row-kind="status-count" data-status-label="extra" '
                + b'data-record-count="1">extra: 1</li>',
            ),
        ),
        (
            "wrong clickable href",
            wrong_source_anchor,
        ),
        (
            "unrelated anchor satisfaction",
            unrelated_anchor,
        ),
        (
            "duplicate metadata",
            mutate("formalization/", catalog_meta, catalog_meta + catalog_meta),
        ),
        (
            "additive metadata",
            mutate(
                "formalization/",
                b"legacy catalogue</a></li>\n</ul>",
                b'legacy catalogue</a></li>\n<li data-meta="poison">Poison: true</li>\n</ul>',
            ),
        ),
    )
    mutations.extend(semantic_mutations)

    changed_revision = dict(fixture)
    original_publication = changed_revision[JSON_ENDPOINTS[2]]
    changed_revision[JSON_ENDPOINTS[2]] = Response(
        200,
        original_publication.content_type,
        json.dumps(wrong_revision).encode(),
        original_publication.final_url,
    )
    mutations.append(("wrong revision", changed_revision))
    wrong_type = dict(fixture)
    original_catalog = wrong_type[JSON_ENDPOINTS[0]]
    wrong_type[JSON_ENDPOINTS[0]] = Response(
        200, "text/plain", original_catalog.body, original_catalog.final_url
    )
    mutations.append(("wrong content type", wrong_type))
    poisoned_schema = dict(fixture)
    original_schema = poisoned_schema[JSON_ENDPOINTS[1]]
    poisoned_schema[JSON_ENDPOINTS[1]] = Response(
        200,
        original_schema.content_type,
        json.dumps(schema_poison).encode(),
        original_schema.final_url,
    )
    mutations.append(("schema poisoning", poisoned_schema))
    oversized = dict(fixture)
    original_overview = oversized["formalization/"]
    oversized["formalization/"] = Response(
        200,
        original_overview.content_type,
        b"x" * (MAX_BODY_BYTES + 1),
        original_overview.final_url,
    )
    mutations.append(("oversized body", oversized))

    for label, changed in mutations:
        try:
            verify_responses(changed, PAGES_BASE, revision, canonical_schema)
        except ValueError:
            pass
        else:
            raise AssertionError(f"live publication mutation was accepted: {label}")
    missing = dict(fixture)
    missing.pop(JSON_ENDPOINTS[2])
    try:
        verify_responses(missing, PAGES_BASE, revision, canonical_schema)
    except ValueError:
        pass
    else:
        raise AssertionError("publication with fewer than seven endpoints was accepted")

    if NoRedirectHandler().redirect_request(None, None, 302, "", {}, PAGES_BASE) is not None:
        raise AssertionError("redirect handler unexpectedly followed a redirect")
    for declared in (str(MAX_BODY_BYTES + 1), "-1", "invalid"):
        try:
            validate_declared_length(declared, PAGES_BASE)
        except ValueError:
            pass
        else:
            raise AssertionError(f"unsafe Content-Length was accepted: {declared}")

    calls = 0
    sleeps: list[float] = []
    clock = [0.0]

    def flaky_fetcher(url: str, timeout: float) -> Response:
        """Fail one complete attempt before serving the coherent fixture."""
        nonlocal calls
        calls += 1
        if calls == 1:
            raise urllib.error.URLError("not propagated")
        endpoint = url.removeprefix(PAGES_BASE)
        return fixture[endpoint]

    verify_with_retry(
        PAGES_BASE,
        revision,
        attempts=2,
        initial_delay=1,
        timeout=1,
        deadline=10,
        canonical_schema_bytes=canonical_schema,
        fetcher=flaky_fetcher,
        sleep=lambda delay: (sleeps.append(delay), clock.__setitem__(0, clock[0] + delay)),
        monotonic=lambda: clock[0],
    )
    if sleeps != [1]:
        raise AssertionError("bounded retry self-test used an unexpected delay")

    persistent_calls = 0

    def persistent_failure(url: str, timeout: float) -> Response:
        """Always fail to prove retry exhaustion is bounded and rejected."""
        nonlocal persistent_calls
        persistent_calls += 1
        raise urllib.error.URLError("persistent failure")

    exhaustion_clock = [0.0]
    try:
        verify_with_retry(
            PAGES_BASE,
            revision,
            attempts=3,
            initial_delay=1,
            timeout=1,
            deadline=10,
            canonical_schema_bytes=canonical_schema,
            fetcher=persistent_failure,
            sleep=lambda delay: exhaustion_clock.__setitem__(
                0, exhaustion_clock[0] + delay
            ),
            monotonic=lambda: exhaustion_clock[0],
        )
    except ValueError:
        pass
    else:
        raise AssertionError("persistent live publication failure was accepted")
    if persistent_calls != 3 or exhaustion_clock[0] != 3:
        raise AssertionError("persistent failure did not use bounded retry exhaustion")

    deadline_clock = [0.0]

    def deadline_fetcher(url: str, timeout: float) -> Response:
        """Advance time so one coherent snapshot exceeds its deadline."""
        endpoint = url.removeprefix(PAGES_BASE)
        deadline_clock[0] += 1
        return fixture[endpoint]

    try:
        verify_with_retry(
            PAGES_BASE,
            revision,
            attempts=1,
            initial_delay=0,
            timeout=1,
            deadline=2,
            canonical_schema_bytes=canonical_schema,
            fetcher=deadline_fetcher,
            sleep=lambda delay: None,
            monotonic=lambda: deadline_clock[0],
        )
    except ValueError:
        pass
    else:
        raise AssertionError("snapshot exceeding the absolute deadline was accepted")
    if deadline_clock[0] != 2:
        raise AssertionError("deadline did not stop the coherent snapshot promptly")
    try:
        verify_with_retry(
            PAGES_BASE,
            revision,
            attempts=1,
            initial_delay=0,
            timeout=1,
            deadline=MAX_DEADLINE_SECONDS + 1,
            canonical_schema_bytes=canonical_schema,
            fetcher=deadline_fetcher,
        )
    except ValueError:
        pass
    else:
        raise AssertionError("workflow-unsafe retry deadline was accepted")


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments for live verification or self-tests."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-url", default=PAGES_BASE)
    parser.add_argument("--revision")
    parser.add_argument("--attempts", type=int, default=7)
    parser.add_argument("--initial-delay", type=float, default=5)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--deadline", type=float, default=240)
    parser.add_argument("--canonical-schema", type=Path)
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    """Run dependency-free tests and optionally verify the live publication."""
    args = parse_args()
    try:
        if args.self_test:
            run_self_tests()
        if args.revision is not None:
            if args.canonical_schema is None:
                raise ValueError("--revision requires --canonical-schema")
            canonical_schema_bytes = args.canonical_schema.read_bytes()
            verify_with_retry(
                args.base_url,
                args.revision,
                args.attempts,
                args.initial_delay,
                args.timeout,
                args.deadline,
                canonical_schema_bytes,
            )
        elif not args.self_test:
            raise ValueError("--revision is required unless --self-test is used")
    except ValueError as error:
        raise SystemExit(f"error: {error}") from error
    print("live formalization publication: checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
