#!/usr/bin/env python3
"""Verify the deployed formalization-status Pages surface after publication."""

from __future__ import annotations

import argparse
import html.parser
import json
import re
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Callable
from urllib.parse import urljoin


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


@dataclass(frozen=True)
class Response:
    """Represent one exact HTTP response needed by the live verifier."""

    status: int
    content_type: str
    body: bytes
    final_url: str


class HumanPageParser(html.parser.HTMLParser):
    """Collect generated metadata and structured navigation from one human page."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.metadata: dict[str, str] = {}
        self.metadata_links: dict[str, str] = {}
        self.indexes: dict[str, list[tuple[str, dict[str, str], str | None]]] = {}
        self.links: list[str] = []
        self.text: list[str] = []
        self.current_meta: tuple[str, str | None, list[str]] | None = None
        self.current_index: str | None = None
        self.current_row: tuple[str, dict[str, str], list[str]] | None = None

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        """Track metadata, index rows, and links from start tags."""
        values = {key: value or "" for key, value in attrs}
        if tag == "ul" and "data-index" in values:
            self.current_index = values["data-index"]
            self.indexes.setdefault(self.current_index, [])
        elif tag == "li" and "data-meta" in values:
            self.current_meta = (
                values["data-meta"],
                values.get("data-href"),
                [],
            )
        elif tag == "li" and self.current_index and "data-row-kind" in values:
            data = {
                key[5:]: value
                for key, value in values.items()
                if key.startswith("data-") and key != "data-row-kind"
            }
            self.current_row = (values["data-row-kind"], data, [])
        elif tag == "a" and "href" in values:
            self.links.append(values["href"])

    def handle_data(self, data: str) -> None:
        """Collect visible text for generated-notice and metadata checks."""
        self.text.append(data)
        if self.current_meta is not None:
            self.current_meta[2].append(data)
        if self.current_row is not None:
            self.current_row[2].append(data)

    def handle_endtag(self, tag: str) -> None:
        """Finish structured metadata and index rows at their closing tags."""
        if tag == "li" and self.current_meta is not None:
            key, href, text = self.current_meta
            if key in self.metadata:
                raise ValueError(f"duplicate generated metadata field: {key}")
            self.metadata[key] = " ".join("".join(text).split())
            if href is not None:
                self.metadata_links[key] = href
            self.current_meta = None
        elif tag == "li" and self.current_row is not None:
            if self.current_index is None:
                raise ValueError("structured index row closed outside an index")
            kind, data, _ = self.current_row
            self.indexes[self.current_index].append((kind, data, data.get("href")))
            self.current_row = None
        elif tag == "ul" and self.current_index is not None:
            self.current_index = None


Fetcher = Callable[[str, float], Response]


def validate_base_url(base_url: str) -> str:
    """Accept only the repository's fixed HTTPS GitHub Pages base URL."""
    if base_url != PAGES_BASE:
        raise ValueError(f"base URL must be exactly {PAGES_BASE}")
    return base_url


def fetch_url(url: str, timeout: float) -> Response:
    """Fetch one endpoint without credentials using a bounded request timeout."""
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "text/html, application/json",
            "User-Agent": "lattice-system-publication-check/1",
        },
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return Response(
            status=response.status,
            content_type=response.headers.get_content_type(),
            body=response.read(),
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


def parse_human(response: Response, endpoint: str) -> HumanPageParser:
    """Require an exact successful HTML response and parse generated structures."""
    if response.status != 200:
        raise ValueError(f"{endpoint}: expected HTTP 200, got {response.status}")
    if response.content_type != "text/html":
        raise ValueError(f"{endpoint}: expected text/html, got {response.content_type}")
    try:
        source = response.body.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{endpoint}: invalid UTF-8 HTML") from error
    parser = HumanPageParser()
    parser.feed(source)
    parser.close()
    return parser


def require_metadata(
    parser: HumanPageParser, endpoint: str, digest: str, revision: str
) -> None:
    """Require exact generated state, schema, digest, revision, and machine links."""
    expected = {
        "catalog-state": "Catalogue state: prototype",
        "schema-version": "Schema version: 1",
        "input-sha256": f"Input SHA-256: {digest}",
        "revision": f"Deploy revision: {revision}",
    }
    for key, value in expected.items():
        if parser.metadata.get(key) != value:
            raise ValueError(f"{endpoint}: wrong generated metadata {key}")
    expected_links = {
        "catalog-link": "/lattice-system/formalization-status/v1/catalog.json",
        "schema-link": "/lattice-system/formalization-status/v1/schema.json",
        "publication-link": "/lattice-system/formalization-status/v1/publication.json",
        "authority-link": "/lattice-system/formalization/legacy/",
    }
    for key, href in expected_links.items():
        if parser.metadata_links.get(key) != href or href not in parser.links:
            raise ValueError(f"{endpoint}: wrong or missing generated link {key}")
    visible = " ".join("".join(parser.text).split())
    if "Generated formalization-status view." not in visible:
        raise ValueError(f"{endpoint}: generated notice is missing")


def require_navigation(
    pages: dict[str, HumanPageParser], catalog: dict[str, object]
) -> None:
    """Require exact overview, source, topic, and status navigation structures."""
    overview_links = {
        "/lattice-system/formalization/status/",
        "/lattice-system/formalization/sources/",
        "/lattice-system/formalization/topics/",
    }
    if not overview_links.issubset(set(pages["formalization/"].links)):
        raise ValueError("formalization/: generated overview navigation is incomplete")

    sources = catalog.get("sources")
    topics = catalog.get("topics")
    if not isinstance(sources, list) or not isinstance(topics, list):
        raise ValueError("catalog: sources and topics must be arrays")
    source_ids = {item.get("id") for item in sources if isinstance(item, dict)}
    topic_ids = {item.get("id") for item in topics if isinstance(item, dict)}
    if None in source_ids or None in topic_ids:
        raise ValueError("catalog: source/topic IDs must be present")
    expected_source_links = {
        f"/lattice-system/formalization/sources/{source_id}/"
        for source_id in source_ids
    } | {"/lattice-system/formalization/sources/foundations/"}
    source_rows = pages["formalization/sources/"].indexes.get("sources")
    if source_rows is None:
        raise ValueError("formalization/sources/: generated source index is missing")
    actual_source_links = {href for _, _, href in source_rows}
    if actual_source_links != expected_source_links:
        raise ValueError("formalization/sources/: source navigation does not match catalog")

    expected_topic_links = {
        f"/lattice-system/formalization/topics/{topic_id}/" for topic_id in topic_ids
    }
    topic_rows = pages["formalization/topics/"].indexes.get("topics")
    if topic_rows is None:
        raise ValueError("formalization/topics/: generated topic index is missing")
    actual_topic_links = {href for _, _, href in topic_rows}
    if actual_topic_links != expected_topic_links:
        raise ValueError("formalization/topics/: topic navigation does not match catalog")

    status_rows = pages["formalization/status/"].indexes.get("status")
    if not status_rows or any(href is not None for _, _, href in status_rows):
        raise ValueError("formalization/status/: generated status summary is invalid")


def verify_responses(
    responses: dict[str, Response], base_url: str, revision: str
) -> None:
    """Validate all seven endpoint responses as one coherent publication."""
    validate_base_url(base_url)
    if set(responses) != set(ENDPOINTS):
        raise ValueError("live response set does not match the seven required endpoints")
    for endpoint, response in responses.items():
        expected_url = urljoin(base_url, endpoint)
        if response.final_url != expected_url:
            raise ValueError(f"{endpoint}: unexpected redirect to {response.final_url}")

    catalog = parse_json(responses[JSON_ENDPOINTS[0]], JSON_ENDPOINTS[0])
    schema = parse_json(responses[JSON_ENDPOINTS[1]], JSON_ENDPOINTS[1])
    publication = parse_json(responses[JSON_ENDPOINTS[2]], JSON_ENDPOINTS[2])
    digest = catalog.get("input_sha256")
    if catalog.get("schema_version") != 1 or publication.get("schema_version") != 1:
        raise ValueError("catalog/publication schema_version must both equal 1")
    if (
        catalog.get("catalog_state") != "prototype"
        or publication.get("catalog_state") != "prototype"
    ):
        raise ValueError("catalog/publication catalog_state must both equal prototype")
    if not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None:
        raise ValueError("catalog input_sha256 is invalid")
    if publication.get("input_sha256") != digest:
        raise ValueError("catalog/publication input_sha256 values differ")
    if publication.get("revision") != revision:
        raise ValueError("publication revision does not equal the required main SHA")
    if schema.get("$id") != PAGES_BASE + "formalization-status/v1/schema.json":
        raise ValueError("published schema $id does not match its stable URL")

    pages = {
        endpoint: parse_human(responses[endpoint], endpoint)
        for endpoint in HUMAN_ENDPOINTS
    }
    for endpoint, parser in pages.items():
        require_metadata(parser, endpoint, digest, revision)
    require_navigation(pages, catalog)


def fetch_publication(base_url: str, timeout: float, fetcher: Fetcher) -> dict[str, Response]:
    """Fetch each required endpoint exactly once for one verification attempt."""
    return {
        endpoint: fetcher(urljoin(base_url, endpoint), timeout)
        for endpoint in ENDPOINTS
    }


def verify_with_retry(
    base_url: str,
    revision: str,
    attempts: int,
    initial_delay: float,
    timeout: float,
    fetcher: Fetcher = fetch_url,
    sleep: Callable[[float], None] = time.sleep,
) -> None:
    """Retry a complete live verification with bounded exponential backoff."""
    validate_base_url(base_url)
    if REVISION_RE.fullmatch(revision) is None:
        raise ValueError("revision must be a 40-character lowercase hexadecimal SHA")
    if not 1 <= attempts <= 10:
        raise ValueError("attempts must be between 1 and 10")
    if not 0 <= initial_delay <= 30 or not 1 <= timeout <= 30:
        raise ValueError("retry delay/timeout is outside the safe bound")
    last_error: Exception | None = None
    for attempt in range(attempts):
        try:
            verify_responses(
                fetch_publication(base_url, timeout, fetcher), base_url, revision
            )
            return
        except (ValueError, OSError, urllib.error.URLError) as error:
            last_error = error
            if attempt + 1 < attempts:
                sleep(min(initial_delay * (2**attempt), 30))
    raise ValueError(f"live publication check failed after {attempts} attempt(s): {last_error}")


def fixture_responses(revision: str) -> dict[str, Response]:
    """Build a coherent in-memory publication for dependency-free self-tests."""
    digest = "a" * 64
    catalog_href = "/lattice-system/formalization-status/v1/catalog.json"
    schema_href = "/lattice-system/formalization-status/v1/schema.json"
    publication_href = "/lattice-system/formalization-status/v1/publication.json"
    authority_href = "/lattice-system/formalization/legacy/"
    book_href = "/lattice-system/formalization/sources/book/"
    foundations_href = "/lattice-system/formalization/sources/foundations/"
    topic_href = "/lattice-system/formalization/topics/spin/"
    metadata = (
        '<p>Generated formalization-status view.</p><ul data-generated-metadata="true">'
        '<li data-meta="catalog-state">Catalogue state: prototype</li>'
        '<li data-meta="schema-version">Schema version: 1</li>'
        f'<li data-meta="input-sha256">Input SHA-256: {digest}</li>'
        f'<li data-meta="revision">Deploy revision: {revision}</li>'
        f'<li data-meta="catalog-link" data-href="{catalog_href}">'
        f'<a href="{catalog_href}">catalog</a></li>'
        f'<li data-meta="schema-link" data-href="{schema_href}">'
        f'<a href="{schema_href}">schema</a></li>'
        f'<li data-meta="publication-link" data-href="{publication_href}">'
        f'<a href="{publication_href}">publication</a></li>'
        f'<li data-meta="authority-link" data-href="{authority_href}">'
        f'<a href="{authority_href}">authority</a></li></ul>'
    )
    human = {
        "formalization/": metadata
        + '<a href="/lattice-system/formalization/status/">status</a>'
        + '<a href="/lattice-system/formalization/sources/">sources</a>'
        + '<a href="/lattice-system/formalization/topics/">topics</a>',
        "formalization/status/": metadata
        + '<ul data-index="status"><li data-row-kind="status" '
        + 'data-status-label="proved" data-record-count="1">proved</li></ul>',
        "formalization/sources/": metadata
        + '<ul data-index="sources"><li data-row-kind="source" '
        + f'data-href="{book_href}"><a href="{book_href}">book</a></li>'
        + '<li data-row-kind="project-original" '
        + f'data-href="{foundations_href}"><a href="{foundations_href}">'
        + "foundations</a></li></ul>",
        "formalization/topics/": metadata
        + '<ul data-index="topics"><li data-row-kind="topic" '
        + f'data-href="{topic_href}"><a href="{topic_href}">spin</a></li></ul>',
    }
    catalog = {
        "schema_version": 1,
        "catalog_state": "prototype",
        "input_sha256": digest,
        "sources": [{"id": "book"}],
        "topics": [{"id": "spin"}],
    }
    publication = {
        "schema_version": 1,
        "catalog_state": "prototype",
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
    verify_responses(fixture, PAGES_BASE, revision)
    mutations: list[tuple[str, dict[str, Response]]] = []
    wrong_revision = dict(json.loads(fixture[JSON_ENDPOINTS[2]].body))
    wrong_revision["revision"] = "2" * 40
    for label, endpoint, replacement in (
        ("wrong revision", JSON_ENDPOINTS[2], json.dumps(wrong_revision).encode()),
        ("wrong content type", JSON_ENDPOINTS[0], fixture[JSON_ENDPOINTS[0]].body),
        (
            "missing navigation",
            "formalization/",
            fixture["formalization/"].body.replace(
                b"/formalization/topics/", b"/formalization/missing/"
            ),
        ),
    ):
        changed = dict(fixture)
        original = changed[endpoint]
        content_type = "text/plain" if label == "wrong content type" else original.content_type
        changed[endpoint] = Response(200, content_type, replacement, original.final_url)
        mutations.append((label, changed))
    for label, changed in mutations:
        try:
            verify_responses(changed, PAGES_BASE, revision)
        except ValueError:
            pass
        else:
            raise AssertionError(f"live publication mutation was accepted: {label}")
    missing = dict(fixture)
    missing.pop(JSON_ENDPOINTS[2])
    try:
        verify_responses(missing, PAGES_BASE, revision)
    except ValueError:
        pass
    else:
        raise AssertionError("publication with fewer than seven endpoints was accepted")

    calls = 0
    sleeps: list[float] = []

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
        fetcher=flaky_fetcher,
        sleep=sleeps.append,
    )
    if sleeps != [1]:
        raise AssertionError("bounded retry self-test used an unexpected delay")


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments for live verification or self-tests."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-url", default=PAGES_BASE)
    parser.add_argument("--revision")
    parser.add_argument("--attempts", type=int, default=7)
    parser.add_argument("--initial-delay", type=float, default=5)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    """Run dependency-free tests and optionally verify the live publication."""
    args = parse_args()
    try:
        if args.self_test:
            run_self_tests()
        if args.revision is not None:
            verify_with_retry(
                args.base_url,
                args.revision,
                args.attempts,
                args.initial_delay,
                args.timeout,
            )
        elif not args.self_test:
            raise ValueError("--revision is required unless --self-test is used")
    except ValueError as error:
        raise SystemExit(f"error: {error}") from error
    print("live formalization publication: checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
