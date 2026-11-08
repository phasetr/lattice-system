#!/usr/bin/env python3
"""Validate content-amendment ownership and its exact source-registry transition."""

import argparse
import csv
from pathlib import Path
import re
import subprocess
import sys


HEADER = ['amendment_id', 'event_id', 'correction_id', 'claim_id',
          'old_content_oid', 'new_content_oid', 'page_source_oid', 'review_ref']
LEDGER = 'claim-content-amendments.tsv'


def fail(message):
    raise ValueError(message)


def rows(root, name, optional=False):
    path = root / 'registry' / name
    if optional and not path.exists():
        return []
    with path.open(newline='', encoding='utf-8') as stream:
        data = list(csv.reader(stream, delimiter='\t', quoting=csv.QUOTE_NONE))
    if name == LEDGER and (not data or data[0] != HEADER):
        fail('bad claim-content-amendments.tsv header')
    return data[1:]


def keyed(root, name):
    data = rows(root, name)
    result = {row[0]: row for row in data}
    if len(result) != len(data):
        fail('duplicate ID in ' + name)
    return result


def valid_oid(value):
    return re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})', value) is not None


def blob(content):
    return subprocess.check_output(['git', 'hash-object', '--stdin'],
                                   input=content.encode('utf-8')).decode().strip()


def validate_static(root):
    amendments = rows(root, LEDGER)
    events = keyed(root, 'correction-events.tsv')
    corrections = keyed(root, 'claim-corrections.tsv')
    reviews = keyed(root, 'claim-normalization-reviews.tsv')
    claims = keyed(root, 'claims.tsv')
    pages = keyed(root, 'pages.tsv')
    seen_ids, owned, history = set(), set(), {}
    for row in amendments:
        if len(row) != len(HEADER):
            fail('bad content amendment row')
        identifier, event_id, correction_id, claim_id, old_oid, new_oid, page_oid, review = row
        if not re.fullmatch(r'CA-[A-Za-z0-9][A-Za-z0-9._:#@+-]*-[0-9]{4,}', identifier):
            fail('bad content amendment ID')
        if identifier in seen_ids or correction_id in owned:
            fail('duplicate content amendment')
        seen_ids.add(identifier)
        owned.add(correction_id)
        correction, event, claim = corrections.get(correction_id), events.get(event_id), claims.get(claim_id)
        if (correction is None or event is None or claim is None or
                correction[1] != event_id or correction[4] != claim_id or
                correction[5] != 'amend_content'):
            fail('content amendment event or correction ownership mismatch')
        owning_review = reviews.get(correction[3])
        if (owning_review is None or owning_review[1] != event_id or
                owning_review[3] != claim_id or owning_review[5] != 'amend_content' or
                owning_review[4] != 'exact_statement_readiness' or owning_review[6] != 'closed' or
                review != event[4] or owning_review[8] != review or
                re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._:#@+-]*', review) is None):
            fail('content amendment review ownership mismatch')
        if claim[1] != event[2]:
            fail('content amendment source mismatch')
        if correction[6:8] != correction[8:10]:
            fail('content amendment changes classification')
        page = pages.get(claim[3])
        if page is None or page[1] != event[2] or page[9] != page_oid or not valid_oid(page_oid):
            fail('content amendment page source mismatch')
        if not valid_oid(old_oid) or not valid_oid(new_oid) or len(old_oid) != len(new_oid):
            fail('content amendment requires frozen old and new content OIDs')
        if old_oid == new_oid:
            fail('content amendment is a no-op')
        history.setdefault(claim_id, []).append((int(event[1]), old_oid, new_oid))
    for correction in corrections.values():
        if correction[5] == 'amend_content' and correction[0] not in owned:
            fail('content amendment is missing its provenance row')
    for name, column in [('claim-successors.tsv', 2), ('source-item-additions.tsv', 2)]:
        for row in rows(root, name):
            if row[column] in owned:
                fail('content amendment cannot introduce successors or source items')
    for entries in history.values():
        entries.sort()
        for previous, current in zip(entries, entries[1:]):
            if previous[0] == current[0] or previous[2] != current[1]:
                fail('content amendment history chain is stale')
    return amendments


def validate_transition(base, current, event_id):
    amendments = validate_static(current)
    old_amendments = rows(base, LEDGER, optional=True)
    old_by_id = {row[0]: row for row in old_amendments}
    current_by_id = {row[0]: row for row in amendments}
    if any(current_by_id.get(identifier) != row for identifier, row in old_by_id.items()):
        fail('historical content amendment drift')
    new = [row for row in amendments if row[0] not in old_by_id]
    if any(row[1] != event_id for row in new):
        fail('content amendment belongs to another event')
    events = keyed(current, 'correction-events.tsv')
    event = events[event_id]
    expected = {row[0] for row in rows(current, 'claim-corrections.tsv')
                if row[1] == event_id and row[5] == 'amend_content'}
    if {row[2] for row in new} != expected:
        fail('content amendment provenance is not new for this event')
    if not new:
        return
    old_claims, claims = keyed(base, 'claims.tsv'), keyed(current, 'claims.tsv')
    old_pages, pages = keyed(base, 'pages.tsv'), keyed(current, 'pages.tsv')
    allowed_lifecycle = {'registered', 'source_frozen', 'census_pass1', 'census_pass2',
                         'census_reconciled', 'vocabulary_reviewed'}
    for root, known_claims in [(base, old_claims), (current, claims)]:
        progress = keyed(root, 'source-progress.tsv').get(event[2])
        if progress is None or progress[1] not in allowed_lifecycle:
            fail('content amendment requires a pre-R4 source')
        for binding in rows(root, 'bindings.tsv'):
            if binding[0] in known_claims and known_claims[binding[0]][1] == event[2]:
                fail('content amendment source already has bindings')
    for row in new:
        _, _, _, claim_id, old_oid, new_oid, page_oid, _ = row
        old, claim = old_claims.get(claim_id), claims.get(claim_id)
        if old is None or claim is None or old[1] != event[2]:
            fail('content amendment does not target a frozen source claim')
        if old[11] != 'false' or old[5] == 'out_of_scope':
            fail('content amendment requires an active formalization target')
        if any(left != right for index, (left, right) in enumerate(zip(old, claim))
               if index not in (7, 8)) or len(old) != len(claim):
            fail('content amendment changed frozen claim identity or metadata')
        if not claim[7].strip() or re.fullmatch(r'\s*(?:True|False)\.?\s*', claim[7]):
            fail('contentless content amendment surrogate')
        if old[7] == claim[7]:
            fail('content amendment is a no-op')
        if blob(old[7]) != old_oid or (old[8] != 'PENDING' and old[8] != old_oid):
            fail('content amendment old content OID is stale')
        if blob(claim[7]) != new_oid or claim[8] != new_oid:
            fail('content amendment new content OID is stale')
        if old_pages[old[3]][9] != page_oid or pages[claim[3]][9] != page_oid:
            fail('content amendment page source mismatch')
        for root in (base, current):
            for name, columns in [('slices.tsv', (2,)), ('dependencies.tsv', (0, 2)),
                                  ('claim-axioms.tsv', (0,))]:
                if any(any(record[column] == claim_id for column in columns)
                       for record in rows(root, name)):
                    fail('content amendment target already has skeleton or axiom relations')
        old_uses = sorted(record for record in rows(base, 'claim-vocabulary.tsv') if record[0] == claim_id)
        new_uses = sorted(record for record in rows(current, 'claim-vocabulary.tsv') if record[0] == claim_id)
        if old_uses != new_uses:
            fail('content amendment changed vocabulary use')
        old_reviews = [record for record in rows(base, 'claim-vocabulary-review.tsv') if record[0] == claim_id]
        new_reviews = [record for record in rows(current, 'claim-vocabulary-review.tsv') if record[0] == claim_id]
        if (len(old_reviews) != 1 or len(new_reviews) != 1 or
                old_reviews[0][:2] != new_reviews[0][:2] or new_reviews[0][2] != event[4]):
            fail('content amendment lacks its refreshed vocabulary review')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--static', type=Path, metavar='ROOT')
    group.add_argument('--transition', nargs=3, metavar=('BASE', 'CURRENT', 'EVENT'))
    args = parser.parse_args()
    try:
        if args.static is not None:
            validate_static(args.static)
        else:
            base, current, event = args.transition
            validate_transition(Path(base), Path(current), event)
    except (ValueError, OSError, IndexError, KeyError, subprocess.CalledProcessError) as error:
        print('check-content-amendments: ' + str(error), file=sys.stderr)
        return 1
    print('check-content-amendments: ok')
    return 0


if __name__ == '__main__':
    sys.exit(main())
