#!/usr/bin/env python3
"""Validate reviewed content amendments and omitted-claim creation provenance."""

import argparse
import csv
from pathlib import Path
import re
import subprocess
import sys


HEADER = ['amendment_id', 'event_id', 'correction_id', 'claim_id',
          'old_content_oid', 'new_content_oid', 'page_source_oid', 'review_ref']
LEDGER = 'claim-content-amendments.tsv'
CONTENT_ACTIONS = {'amend_content', 'amend_and_reclassify'}
TARGET_DISPOSITIONS = {'assertion', 'definition', 'notation', 'hypothesis', 'domain', 'conjecture'}
SUBKINDS = {'theorem', 'lemma', 'proposition', 'corollary', 'equation', 'definition',
            'notation', 'problem', 'remark', 'subclaim', 'unnumbered_obligation',
            'hypothesis', 'domain', 'conjecture'}


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


def validate_additions_static(root):
    events = keyed(root, 'correction-events.tsv')
    reviews = keyed(root, 'claim-normalization-reviews.tsv')
    claims = keyed(root, 'claims.tsv')
    pages = keyed(root, 'pages.tsv')
    items = keyed(root, 'source-items.tsv')
    corrections = keyed(root, 'claim-corrections.tsv')
    additions = []
    created_claims = set()
    for correction in corrections.values():
        if correction[5] != 'add_omitted_claim':
            if 'NONE' in correction[6:8]:
                fail('NONE old classification requires add_omitted_claim')
            continue
        event = events.get(correction[1])
        review = reviews.get(correction[3])
        claim = claims.get(correction[4])
        if (event is None or review is None or claim is None or
                review[1] != event[0] or review[3] != claim[0] or
                review[4:7] != ['exact_statement_readiness', 'add_omitted_claim', 'closed'] or
                review[8] != event[4] or claim[1] != event[2]):
            fail('omitted claim review or source ownership mismatch')
        if (sum(row[1] == event[0] and row[3] == claim[0] for row in reviews.values()) != 1 or
                sum(row[1] == event[0] and row[4] == claim[0] for row in corrections.values()) != 1):
            fail('omitted claim lacks exactly one owning review and correction')
        if (correction[6:8] != ['NONE', 'NONE'] or
                correction[8] not in {'assertion', 'definition', 'notation', 'hypothesis', 'domain', 'conjecture'} or
                correction[9] not in {'theorem', 'lemma', 'proposition', 'corollary', 'equation',
                                      'definition', 'notation', 'problem', 'remark', 'subclaim',
                                      'unnumbered_obligation', 'hypothesis', 'domain', 'conjecture'}):
            fail('invalid omitted claim classification')
        if claim[0] in created_claims:
            fail('omitted claim has more than one creation owner')
        created_claims.add(claim[0])
        page = pages.get(claim[3])
        if page is None or page[1] != event[2]:
            fail('omitted claim source page mismatch')
        if any(row[1] == event[0] and (row[2] == correction[0] or row[3] == claim[0] or row[6] == claim[0])
               for row in rows(root, 'claim-successors.tsv')):
            fail('omitted claim cannot have successor provenance')
        relations = [row for row in rows(root, 'item-claims.tsv') if row[2] == claim[0]]
        if len(relations) != 1:
            fail('omitted claim lacks exactly one source item')
        item = items.get(relations[0][0])
        if item is None or item[1] != event[2] or item[3] != claim[3]:
            fail('omitted claim source item mismatch')
        # A later reviewed correction may change this claim. Creation-time
        # classification and content are checked against its own event base.
        additions.append(correction)
    return additions


def validate_additions_transition(base, current, event):
    additions = [row for row in validate_additions_static(current) if row[1] == event[0]]
    if not additions:
        return
    old_claims, claims = keyed(base, 'claims.tsv'), keyed(current, 'claims.tsv')
    old_pages, pages = keyed(base, 'pages.tsv'), keyed(current, 'pages.tsv')
    old_source = keyed(base, 'sources.tsv').get(event[2])
    source = keyed(current, 'sources.tsv').get(event[2])
    if (source is None or old_source != source or not valid_oid(source[14]) or
            not valid_oid(source[15]) or len(source[14]) != len(source[15])):
        fail('omitted claim source fingerprints changed or are not frozen')
    for root, known_claims in [(base, old_claims), (current, claims)]:
        progress = keyed(root, 'source-progress.tsv').get(event[2])
        if progress is None or progress[1] not in {'registered', 'source_frozen', 'census_pass1',
                                                 'census_pass2', 'census_reconciled', 'vocabulary_reviewed'}:
            fail('omitted claim requires a pre-R4 source')
        if any(row[0] in known_claims and known_claims[row[0]][1] == event[2]
               for row in rows(root, 'bindings.tsv')):
            fail('omitted claim source already has bindings')
    vocabulary = keyed(current, 'vocabulary.tsv')
    invariant = keyed(current, 'source-invariants.tsv').get(event[2])
    if invariant is None or invariant[7] != event[4]:
        fail('omitted claim lacks its event invariant review')
    if int(invariant[1]) != sum(row[1] == event[2] for row in pages.values()):
        fail('omitted claim physical page count is stale')
    for correction in additions:
        claim_id = correction[4]
        if claim_id in old_claims:
            fail('omitted claim reuses a frozen claim ID')
        claim = claims[claim_id]
        if claim[5:7] != correction[8:10]:
            fail('omitted claim classification does not match its correction')
        if claim[5] == 'out_of_scope' or claim[9:] != ['NONE', 'NONE', 'false', 'NONE', 'NONE', 'NONE']:
            fail('omitted claim is not an active formalization target')
        if not claim[7].strip() or re.fullmatch(r'\s*(?:True|False)\.?\s*', claim[7]):
            fail('contentless omitted claim surrogate')
        if not valid_oid(claim[8]) or blob(claim[7]) != claim[8]:
            fail('omitted claim content OID is not frozen or is stale')
        old_page, page = old_pages.get(claim[3]), pages.get(claim[3])
        if (old_page is None or page != old_page or page[1] != event[2] or
                not valid_oid(page[9])):
            fail('omitted claim must use an unchanged frozen source page')
        for root in (base, current):
            for name, columns in [('slices.tsv', (2,)), ('dependencies.tsv', (0, 2)),
                                  ('claim-axioms.tsv', (0,))]:
                if any(any(record[column] == claim_id for column in columns)
                       for record in rows(root, name)):
                    fail('omitted claim has skeleton or axiom relations')
        review_rows = [row for row in rows(current, 'claim-vocabulary-review.tsv') if row[0] == claim_id]
        uses = [row for row in rows(current, 'claim-vocabulary.tsv') if row[0] == claim_id]
        if (len(review_rows) != 1 or review_rows[0][2] != event[4] or
                review_rows[0][1] not in {'mathlib_only', 'project_vocabulary'} or
                (review_rows[0][1] == 'mathlib_only' and uses) or
                (review_rows[0][1] == 'project_vocabulary' and not uses) or
                len({row[1] for row in uses}) != len(uses) or
                any(row[1] not in vocabulary for row in uses)):
            fail('omitted claim lacks its reviewed vocabulary basis and use')


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
                correction[5] not in CONTENT_ACTIONS):
            fail('content amendment event or correction ownership mismatch')
        owning_review = reviews.get(correction[3])
        if (owning_review is None or owning_review[1] != event_id or
                owning_review[3] != claim_id or owning_review[5] != correction[5] or
                owning_review[4] != 'exact_statement_readiness' or owning_review[6] != 'closed' or
                review != event[4] or owning_review[8] != review or
                re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._:#@+-]*', review) is None):
            fail('content amendment review ownership mismatch')
        if claim[1] != event[2]:
            fail('content amendment source mismatch')
        if correction[5] == 'amend_and_reclassify':
            if (sum(record[1] == event_id and record[3] == claim_id for record in reviews.values()) != 1 or
                    sum(record[1] == event_id and record[4] == claim_id for record in corrections.values()) != 1):
                fail('combined correction lacks exactly one owning review and correction')
            if (len(correction) != 10 or correction[6] not in TARGET_DISPOSITIONS or
                    correction[8] not in TARGET_DISPOSITIONS or
                    correction[7] not in SUBKINDS or correction[9] not in SUBKINDS):
                fail('combined correction has invalid classification')
            if correction[6:8] == correction[8:10]:
                fail('combined correction requires changed classification')
        elif correction[6:8] != correction[8:10]:
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
        if correction[5] in CONTENT_ACTIONS and correction[0] not in owned:
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
    validate_additions_static(root)
    return amendments


def validate_transition(base, current, event_id):
    amendments = validate_static(current)
    old_amendments = rows(base, LEDGER, optional=True)
    old_by_id = {row[0]: row for row in old_amendments}
    current_by_id = {row[0]: row for row in amendments}
    old_path = base / 'registry' / LEDGER
    if ((old_path.exists() and not (current / 'registry' / LEDGER).read_bytes().startswith(old_path.read_bytes())) or
            any(current_by_id.get(identifier) != row for identifier, row in old_by_id.items())):
        fail('historical content amendment drift')
    new = [row for row in amendments if row[0] not in old_by_id]
    if any(row[1] != event_id for row in new):
        fail('content amendment belongs to another event')
    events = keyed(current, 'correction-events.tsv')
    event = events[event_id]
    expected = {row[0] for row in rows(current, 'claim-corrections.tsv')
                if row[1] == event_id and row[5] in CONTENT_ACTIONS}
    if {row[2] for row in new} != expected:
        fail('content amendment provenance is not new for this event')
    validate_additions_transition(base, current, event)
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
        correction = keyed(current, 'claim-corrections.tsv')[row[2]]
        combined = correction[5] == 'amend_and_reclassify'
        if combined:
            for record in (old, claim):
                if (len(record) != 15 or record[5] not in TARGET_DISPOSITIONS or
                        record[9:] != ['NONE', 'NONE', 'false', 'NONE', 'NONE', 'NONE']):
                    fail('combined correction requires an active formalization target')
            if correction[6:8] != old[5:7] or correction[8:10] != claim[5:7]:
                fail('combined correction classification does not match claim transition')
        elif old[11] != 'false' or old[5] == 'out_of_scope':
            fail('content amendment requires an active formalization target')
        allowed = (5, 6, 7, 8) if combined else (7, 8)
        if any(left != right for index, (left, right) in enumerate(zip(old, claim))
               if index not in allowed) or len(old) != len(claim):
            fail(('combined correction' if combined else 'content amendment') +
                 ' changed frozen claim identity or metadata')
        if combined:
            old_source = keyed(base, 'sources.tsv').get(event[2])
            source = keyed(current, 'sources.tsv').get(event[2])
            if (source is None or old_source != source or not valid_oid(source[14]) or
                    not valid_oid(source[15]) or len(source[14]) != len(source[15])):
                fail('combined correction source record changed or is not frozen')
            if old_pages[old[3]][9] != page_oid or pages[claim[3]][9] != page_oid:
                fail('content amendment page source mismatch')
            if old_pages[old[3]] != pages[claim[3]]:
                fail('combined correction page record changed')
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
        if combined:
            invariant = keyed(current, 'source-invariants.tsv').get(event[2])
            if invariant is None or invariant[7] != event[4]:
                fail('combined correction lacks its event invariant review')


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
