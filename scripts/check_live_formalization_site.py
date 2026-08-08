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
    expected_overview_index_rows,
    expected_source_index_rows,
    expected_status_index_rows,
    expected_topic_index_rows,
    parse_record_html,
    reject_authority_contradictions,
    require_index_rows,
)


PAGES_BASE = "https://phasetr.github.io/lattice-system/"
HUMAN_ENDPOINTS = (
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
ENDPOINTS = (*HUMAN_ENDPOINTS, *JSON_ENDPOINTS)
SHA256_RE = re.compile(r"[0-9a-f]{64}")
REVISION_RE = re.compile(r"[0-9a-f]{40}")
MAX_BODY_BYTES = 2 * 1024 * 1024
MAX_DEADLINE_SECONDS = 240


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


def verify_responses(
    responses: dict[str, Response],
    base_url: str,
    revision: str,
    canonical_schema_bytes: bytes,
) -> None:
    """Validate all seven endpoint responses as one coherent publication."""
    validate_base_url(base_url)
    if set(responses) != set(ENDPOINTS):
        raise ValueError("live response set does not match the seven required endpoints")
    for endpoint, response in responses.items():
        if len(response.body) > MAX_BODY_BYTES:
            raise ValueError(f"{endpoint}: response body exceeds the byte limit")
        expected_url = urljoin(base_url, endpoint)
        if response.final_url != expected_url:
            raise ValueError(f"{endpoint}: unexpected redirect to {response.final_url}")

    catalog = parse_json(responses[JSON_ENDPOINTS[0]], JSON_ENDPOINTS[0])
    schema_response = responses[JSON_ENDPOINTS[1]]
    schema = parse_json(schema_response, JSON_ENDPOINTS[1])
    publication = parse_json(responses[JSON_ENDPOINTS[2]], JSON_ENDPOINTS[2])
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

    pages = {
        endpoint: parse_human(responses[endpoint], endpoint)
        for endpoint in HUMAN_ENDPOINTS
    }
    reject_authority_contradictions(
        catalog,
        [(endpoint, " ".join(parser.text)) for endpoint, parser in pages.items()],
    )
    for endpoint, parser in pages.items():
        require_metadata(parser, endpoint, catalog, revision)
    require_navigation(pages, catalog)


def fetch_publication(
    base_url: str,
    timeout: float,
    fetcher: Fetcher,
    deadline_at: float,
    monotonic: Callable[[], float],
) -> dict[str, Response]:
    """Fetch one coherent seven-endpoint snapshot within the absolute deadline."""
    responses = {}
    for endpoint in ENDPOINTS:
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
    revision: str, catalog_state: str = "prototype"
) -> dict[str, Response]:
    """Build a coherent in-memory publication for dependency-free self-tests."""
    digest = "a" * 64
    catalog_href = "/lattice-system/formalization-status/v1/catalog.json"
    schema_href = "/lattice-system/formalization-status/v1/schema.json"
    publication_href = "/lattice-system/formalization-status/v1/publication.json"
    authoritative = catalog_state == "authoritative"
    authority_href = (
        catalog_href if authoritative else "/lattice-system/formalization/legacy/"
    )
    authority_label = (
        "Current authority: validated version 1 catalogue"
        if authoritative
        else "Current authority: complete interim legacy catalogue"
    )
    book_href = "/lattice-system/formalization/sources/book/"
    foundations_href = "/lattice-system/formalization/sources/foundations/"
    topic_href = "/lattice-system/formalization/topics/spin/"
    metadata = (
        '<p>Generated formalization-status view.</p><ul data-generated-metadata="true">'
        f'<li data-meta="catalog-state">Catalogue state: {catalog_state}</li>'
        '<li data-meta="schema-version">Schema version: 1</li>'
        f'<li data-meta="input-sha256">Input SHA-256: {digest}</li>'
        f'<li data-meta="revision">Deploy revision: {revision}</li>'
        f'<li data-meta="catalog-link" data-href="{catalog_href}">'
        f'<a href="{catalog_href}">Machine data: version 1 catalogue</a></li>'
        f'<li data-meta="schema-link" data-href="{schema_href}">'
        f'<a href="{schema_href}">Schema: version 1 schema</a></li>'
        f'<li data-meta="publication-link" data-href="{publication_href}">'
        f'<a href="{publication_href}">Build metadata: publication sidecar</a></li>'
        f'<li data-meta="authority-link" data-href="{authority_href}">'
        f'<a href="{authority_href}">{authority_label}</a></li></ul>'
    )
    human = {
        "formalization/": metadata
        + '<ul><li data-row-kind="overview-counts" data-record-count="1" '
        + f'data-source-count="1" data-topic-count="1">This {catalog_state} snapshot '
        + "contains 1 records, 1 sources, and 1 topics.</li></ul>"
        + '<ul><li data-row-kind="overview-navigation" data-navigation-id="sources" '
        + 'data-href="/lattice-system/formalization/sources/"><a '
        + 'href="/lattice-system/formalization/sources/">Browse generated source '
        + "projections</a></li>"
        + '<li data-row-kind="overview-navigation" data-navigation-id="topics" '
        + 'data-href="/lattice-system/formalization/topics/"><a '
        + 'href="/lattice-system/formalization/topics/">Browse generated topic '
        + "projections</a></li>"
        + '<li data-row-kind="overview-navigation" data-navigation-id="status" '
        + 'data-href="/lattice-system/formalization/status/"><a '
        + 'href="/lattice-system/formalization/status/">Browse generated status '
        + "summary</a></li></ul>",
        "formalization/status/": metadata
        + '<ul data-index="status"><li data-row-kind="status" '
        + 'data-status-label="proved" data-record-count="1">proved: 1</li></ul>',
        "formalization/sources/": metadata
        + '<ul data-index="sources"><li data-row-kind="source" '
        + 'data-source-id="book" data-source-title="Book" data-record-count="1" '
        + f'data-href="{book_href}"><a href="{book_href}">'
        + "Book: 1 related record(s)</a></li>"
        + '<li data-row-kind="project-original" '
        + 'data-source-id="foundations" data-record-count="0" '
        + f'data-href="{foundations_href}"><a href="{foundations_href}">'
        + "Project-original foundations: 0 record(s)</a></li></ul>",
        "formalization/topics/": metadata
        + '<ul data-index="topics"><li data-row-kind="topic" '
        + 'data-topic-id="spin" data-topic-label="Spin" data-record-count="1" '
        + f'data-href="{topic_href}"><a href="{topic_href}">'
        + "Spin: 1 record(s)</a></li></ul>",
    }
    catalog = {
        "schema_version": 1,
        "catalog_state": catalog_state,
        "input_sha256": digest,
        "sources": [{"id": "book", "title": "Book"}],
        "source_items": [{"id": "book-item", "source_id": "book"}],
        "topics": [{"id": "spin", "label": "Spin"}],
        "records": [
            {
                "id": "record",
                "origin": "literature",
                "implementation_state": "complete",
                "declaration_kind": "theorem",
                "trust_state": "proved",
                "source_relations": [
                    {"source_item_id": "book-item", "relation": "formalizes"}
                ],
                "topic_ids": ["spin"],
            }
        ],
    }
    publication = {
        "schema_version": 1,
        "catalog_state": catalog_state,
        "input_sha256": digest,
        "revision": revision,
    }
    payloads: dict[str, tuple[str, bytes]] = {
        **{key: ("text/html", value.encode()) for key, value in human.items()},
        JSON_ENDPOINTS[0]: ("application/json", json.dumps(catalog).encode()),
        JSON_ENDPOINTS[1]: (
            "application/json",
            json.dumps({"$id": PAGES_BASE + JSON_ENDPOINTS[1]}).encode(),
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
    status_row_start = b'<li data-row-kind="status"'
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
                b'data-record-count="1"',
                b'data-record-count="2"',
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
                b">Spin: 1 record(s)</a>",
                b">Wrong: 1 record(s)</a>",
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
                + b'<li data-row-kind="status" data-status-label="extra" '
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
                b"catalogue</a></li></ul>",
                b'catalogue</a></li><li data-meta="poison">Poison: true</li></ul>',
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
