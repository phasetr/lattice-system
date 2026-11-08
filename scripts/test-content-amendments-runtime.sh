#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
python3 - "$PROJECT_ROOT" <<'PY'
import csv
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

project = Path(sys.argv[1]).resolve()
header = ['amendment_id', 'event_id', 'correction_id', 'claim_id',
          'old_content_oid', 'new_content_oid', 'page_source_oid', 'review_ref']
claim = 'CL-TASAKI2020-0001'

def table(root, name):
    with (root / 'registry' / name).open(newline='', encoding='utf-8') as stream:
        return list(csv.reader(stream, delimiter='\t', quoting=csv.QUOTE_NONE))

def write(root, name, rows):
    with (root / 'registry' / name).open('w', newline='', encoding='utf-8') as stream:
        csv.writer(stream, delimiter='\t', lineterminator='\n',
                   quoting=csv.QUOTE_NONE, quotechar=None).writerows(rows)

def mutate(root, name, identifier, column, value):
    rows = table(root, name)
    for row in rows[1:]:
        if row[0] == identifier:
            row[column] = value
    write(root, name, rows)

def blob(text):
    return subprocess.check_output(['git', 'hash-object', '--stdin'],
                                   input=text.encode('utf-8'), cwd=project).decode().strip()

def refresh(root):
    pages, claims = table(root, 'pages.tsv'), table(root, 'claims.tsv')
    rows = table(root, 'source-invariants.tsv')
    for row in rows[1:]:
        active = [r for r in claims[1:] if r[1] == row[0] and r[11] == 'false']
        row[2] = str(len(active))
        row[3] = str(sum(r[5] != 'out_of_scope' for r in active))
        row[4] = str(sum(r[6] == 'equation' for r in active))
        used = {r[3] for r in active}
        row[5] = str(sum(p[1] == row[0] and p[0] not in used for p in pages[1:]))
        content = ''.join('\t'.join(r) + '\n' for r in pages[1:] + claims[1:]
                          if r[1] == row[0])
        row[6] = blob(content)
    write(root, 'source-invariants.tsv', rows)

def unused_id(root, name, prefix):
    path = root / 'registry' / name
    existing = {row[0] for row in table(root, name)[1:]} if path.exists() else set()
    number = 1
    while prefix + '-' + format(number, '04d') in existing:
        number += 1
    return prefix + '-' + format(number, '04d')

def clone_commit_registry(commit, target):
    paths = subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', commit, 'registry'], cwd=project).decode().splitlines()
    for relative in paths:
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(subprocess.check_output(['git', 'show', commit + ':' + relative], cwd=project))
    if not (target / 'registry/claim-content-amendments.tsv').exists():
        write(target, 'claim-content-amendments.tsv', [header])

def prepare_amendment(before, after, content):
    shutil.copytree(before, after)
    if not (after / 'registry/claim-content-amendments.tsv').exists():
        write(after, 'claim-content-amendments.tsv', [header])
    event_id = unused_id(after, 'correction-events.tsv', 'RUNTIME-CONTENT-EVENT')
    review_ref = event_id + '-REVIEW'
    review_id = unused_id(after, 'claim-normalization-reviews.tsv', 'NR-RUNTIME')
    correction_id = unused_id(after, 'claim-corrections.tsv', 'CC-RUNTIME')
    amendment_id = unused_id(after, 'claim-content-amendments.tsv', 'CA-RUNTIME')
    old = next(row for row in table(before, 'claims.tsv')[1:] if row[0] == claim)
    page = next(row for row in table(before, 'pages.tsv')[1:] if row[0] == old[3])
    events = table(after, 'correction-events.tsv')
    events.append([event_id, str(len(events)), old[1],
                   subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project).decode().strip(), review_ref])
    write(after, 'correction-events.tsv', events)
    write(after, 'claim-normalization-reviews.tsv', table(after, 'claim-normalization-reviews.tsv') + [
        [review_id, event_id, '1', claim, 'exact_statement_readiness', 'amend_content',
         'closed', 'restore-source-condition', review_ref]])
    write(after, 'claim-corrections.tsv', table(after, 'claim-corrections.tsv') + [
        [correction_id, event_id, '1', review_id, claim, 'amend_content',
         old[5], old[6], old[5], old[6]]])
    write(after, 'claim-content-amendments.tsv', table(after, 'claim-content-amendments.tsv') + [
        [amendment_id, event_id, correction_id, claim, blob(old[7]), blob(content), page[9], review_ref]])
    mutate(after, 'claims.tsv', claim, 7, content)
    mutate(after, 'claims.tsv', claim, 8, blob(content))
    mutate(after, 'claim-vocabulary-review.tsv', claim, 2, review_ref)
    refresh(after)
    return event_id, review_ref, correction_id, amendment_id, old, page


def prepare_omission(before, after, new_item=True):
    shutil.copytree(before, after)
    event_id = unused_id(after, 'correction-events.tsv', 'RUNTIME-OMISSION-EVENT')
    review_ref = event_id + '-REVIEW'
    review_id = unused_id(after, 'claim-normalization-reviews.tsv', 'NR-RUNTIME')
    correction_id = unused_id(after, 'claim-corrections.tsv', 'CC-RUNTIME')
    claim_id = unused_id(after, 'claims.tsv', 'CL-TASAKI2020')
    claims = table(after, 'claims.tsv')
    anchor = claims[1]
    content = 'The two finite parity classes have equal cardinality.'
    suffix = 1
    order = anchor[2] + '.' + format(suffix, '04d')
    while any(r[2] == order and r[1] == anchor[1] for r in claims[1:]):
        suffix += 1
        order = anchor[2] + '.' + format(suffix, '04d')
    locator = anchor[4] + '; independently reviewed omitted assertion'
    index = next((i for i, r in enumerate(claims[1:], 1)
                  if r[1] == anchor[1] and r[2] > order), len(claims))
    claims.insert(index, [claim_id, anchor[1], order, anchor[3], locator,
                      'assertion', 'unnumbered_obligation', content, blob(content),
                      'NONE', 'NONE', 'false', 'NONE', 'NONE', 'NONE'])
    write(after, 'claims.tsv', claims)
    events = table(after, 'correction-events.tsv')
    events.append([event_id, str(len(events)), anchor[1],
                   subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project).decode().strip(), review_ref])
    write(after, 'correction-events.tsv', events)
    write(after, 'claim-normalization-reviews.tsv', table(after, 'claim-normalization-reviews.tsv') + [
        [review_id, event_id, '1', claim_id, 'exact_statement_readiness', 'add_omitted_claim',
         'closed', 'omitted-source-assertion', review_ref]])
    write(after, 'claim-corrections.tsv', table(after, 'claim-corrections.tsv') + [
        [correction_id, event_id, '1', review_id, claim_id, 'add_omitted_claim',
         'NONE', 'NONE', 'assertion', 'unnumbered_obligation']])
    write(after, 'claim-vocabulary-review.tsv', table(after, 'claim-vocabulary-review.tsv') + [
        [claim_id, 'mathlib_only', review_ref]])
    relations = table(after, 'item-claims.tsv')
    existing = next(r for r in relations[1:] if r[2] == anchor[0])
    if new_item:
        item_id = unused_id(after, 'source-items.tsv', 'IT-TASAKI2020')
        items = table(after, 'source-items.tsv')
        source_item = next(r for r in items[1:] if r[0] == existing[0])
        index = next((i for i, r in enumerate(items[1:], 1)
                      if r[1] == anchor[1] and r[2] > order), len(items))
        items.insert(index,
                     [item_id, anchor[1], order, anchor[3], 'unlabeled', 'NONE',
                      'NONE', locator, source_item[8], source_item[9], review_ref])
        write(after, 'source-items.tsv', items)
        addition_id = unused_id(after, 'source-item-additions.tsv', 'IA-RUNTIME')
        write(after, 'source-item-additions.tsv', table(after, 'source-item-additions.tsv') + [
            [addition_id, event_id, correction_id, '1', item_id, review_ref]])
        relations.insert(relations.index(existing) + 1, [item_id, '1', claim_id])
    else:
        item_id = existing[0]
        position = 1 + max(int(r[1]) for r in relations[1:] if r[0] == item_id)
        index = max(i for i, r in enumerate(relations) if r[0] == item_id) + 1
        relations.insert(index, [item_id, str(position), claim_id])
    write(after, 'item-claims.tsv', relations)
    mutate(after, 'source-invariants.tsv', anchor[1], 7, review_ref)
    refresh(after)
    return event_id, review_ref, review_id, correction_id, claim_id, item_id

count = 0
accepted = 0
rejected = 0
def expect(label, expected, command, diagnostic=''):
    global count, accepted, rejected
    result = subprocess.run(command, cwd=project, env=os.environ,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if (result.returncode == 0) != expected or (diagnostic and diagnostic not in result.stdout):
        print('test-content-amendments-runtime: unexpected result:', label, file=sys.stderr)
        print(result.stdout, file=sys.stderr)
        raise SystemExit(1)
    count += 1
    accepted += expected
    rejected += not expected

with tempfile.TemporaryDirectory(prefix='lattice-content-amendments.') as temporary:
    root = Path(temporary)
    os.environ['LATTICE_TEST_ROOT'] = temporary
    base = root / 'base'
    shutil.copytree(project / 'registry', base / 'registry')
    mutate(base, 'claims.tsv', claim, 8, 'PENDING')
    refresh(base)
    current = root / 'current'
    new_content = 'For every admissible x, F(x) = G(x).'
    event, review, correction_id, amendment_id, old, page = prepare_amendment(base, current, new_content)
    corrections_checker = str(project / 'scripts/check-claim-corrections.sh')
    base_checker = str(project / 'scripts/check-base-diff.sh')
    command = [corrections_checker, '--fixture-dirs', str(base), str(current)]
    expect('pending-old-content-event', True, command)
    helper = str(project / 'scripts/check-content-amendments.py')

    def transition(label, before, after, expected=True, diagnostic=''):
        expect(label, expected, [corrections_checker, '--fixture-dirs', str(before), str(after)], diagnostic)

    def static(label, after, expected=True, diagnostic=''):
        expect(label, expected, ['python3', helper, '--static', str(after)], diagnostic)

    def base_diff(label, before, after, expected=True, event_id=None, diagnostic=''):
        options = ['--correction-event', event_id] if event_id else []
        expect(label, expected, [base_checker] + options + ['--fixture-dirs', str(before), str(after)], diagnostic)

    def case(name, source=current):
        target = root / name
        shutil.copytree(source, target)
        return target

    def amendment_change(target, column, value):
        mutate(target, 'claim-content-amendments.tsv', amendment_id, column, value)

    omitted = root / 'omitted-claim'
    omission_event, omission_review, omission_nr, omission_cc, omitted_claim, omitted_item = prepare_omission(base, omitted)
    transition('omitted-claim-new-item', base, omitted)

    static('pending-old-static', current)
    expect('pending-old-registry', True, [str(project / 'scripts/check-registry.sh'), str(current)])
    base_diff('pending-old-dedicated-diff', base, current, event_id=event)
    base_diff('ordinary-content-change-rejected', base, current, False)
    base_diff('later-ordinary-after-event', current, current)
    base_diff('historical-event-cannot-reopen-exception', current, current, event_id=event)

    frozen_base = case('frozen-base', base)
    mutate(frozen_base, 'claims.tsv', claim, 8, blob(old[7]))
    refresh(frozen_base)
    transition('frozen-old-content-event', frozen_base, current)
    base_diff('frozen-old-dedicated-diff', frozen_base, current, event_id=event)

    existing_amendments = table(base, 'claim-content-amendments.tsv')[1:]
    snapshot_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project).decode().strip()
    if existing_amendments:
        event_rows = {row[0]: row for row in table(base, 'correction-events.tsv')[1:]}
        earliest = min(existing_amendments, key=lambda row: int(event_rows[row[1]][1]))
        snapshot_commit = event_rows[earliest[1]][3]
    historical_header = root / 'pre-amendment-header'
    clone_commit_registry(snapshot_commit, historical_header)
    assert len(table(historical_header, 'claim-content-amendments.tsv')) == 1
    assert not any(row[5] == 'amend_content' for row in table(historical_header, 'claim-corrections.tsv')[1:])
    legacy_base = case('historical-no-ledger', historical_header)
    (legacy_base / 'registry/claim-content-amendments.tsv').unlink()
    legacy_current = root / 'historical-content-event'
    legacy_event, _, _, _, _, _ = prepare_amendment(legacy_base, legacy_current, new_content)
    transition('historical-no-ledger-content-event', legacy_base, legacy_current)
    base_diff('historical-no-ledger-dedicated-diff', legacy_base, legacy_current, event_id=legacy_event)
    base_diff('ordinary-header-only-migration', legacy_base, historical_header)
    base_diff('ordinary-data-without-event', legacy_base, legacy_current, False)

    missing = case('missing-ledger')
    (missing / 'registry/claim-content-amendments.tsv').unlink()
    transition('missing-current-ledger', base, missing, False, 'missing registry/claim-content-amendments.tsv')
    missing_row = case('missing-row')
    write(missing_row, 'claim-content-amendments.tsv',
          [row for row in table(missing_row, 'claim-content-amendments.tsv') if row[0] != amendment_id])
    transition('missing-amendment-row', base, missing_row, False, 'missing its provenance row')
    duplicate = case('duplicate-amendment')
    amendment_rows = table(duplicate, 'claim-content-amendments.tsv')
    write(duplicate, 'claim-content-amendments.tsv', amendment_rows + [amendment_rows[-1]])
    static('duplicate-amendment-rejected', duplicate, False, 'duplicate content amendment')
    for name, column, value, diagnostic in [
            ('invalid-id', 0, 'CA-invalid-1', 'bad content amendment ID'),
            ('unknown-event', 1, 'UNKNOWN-EVENT', 'ownership mismatch'),
            ('unknown-correction', 2, 'CC-UNKNOWN-0001', 'ownership mismatch'),
            ('wrong-claim', 3, 'CL-TASAKI2020-0002', 'ownership mismatch'),
            ('pending-old-ledger', 4, 'PENDING', 'requires frozen'),
            ('pending-new-ledger', 5, 'PENDING', 'requires frozen'),
            ('wrong-page-source', 6, 'a' * 40, 'page source mismatch'),
            ('pending-page-source', 6, 'PENDING', 'page source mismatch'),
            ('wrong-review', 7, 'WRONG-REVIEW', 'review ownership mismatch')]:
        target = case(name)
        amendment_change(target, column, value)
        static(name, target, False, diagnostic)

    wrong_action = case('wrong-action')
    mutate(wrong_action, 'claim-corrections.tsv', correction_id, 5, 'reclassify')
    static('amendment-owned-by-wrong-action', wrong_action, False, 'ownership mismatch')
    wrong_source = case('wrong-source')
    mutate(wrong_source, 'correction-events.tsv', event, 2, 'OTHER')
    static('cross-source-event', wrong_source, False, 'source mismatch')

    stale_old = case('stale-old')
    amendment_change(stale_old, 4, '1' * 40)
    transition('stale-old-content-hash', base, stale_old, False, 'old content OID is stale')
    stale_base = case('stale-recorded-old', frozen_base)
    mutate(stale_base, 'claims.tsv', claim, 8, '2' * 40)
    refresh(stale_base)
    transition('stale-frozen-old-record', stale_base, current, False, 'old content OID is stale')
    stale_new = case('stale-new')
    amendment_change(stale_new, 5, '3' * 40)
    transition('stale-new-content-hash', base, stale_new, False, 'new content OID is stale')
    pending_new = case('pending-new-record')
    mutate(pending_new, 'claims.tsv', claim, 8, 'PENDING')
    transition('pending-new-claim-record', base, pending_new, False, 'new content OID is stale')

    for name, content, diagnostic in [('no-op', old[7], 'no-op'),
                                      ('surrogate-true', 'True.', 'contentless'),
                                      ('surrogate-false', 'False', 'contentless'),
                                      ('surrogate-empty', '', 'contentless')]:
        target = case(name)
        mutate(target, 'claims.tsv', claim, 7, content)
        mutate(target, 'claims.tsv', claim, 8, blob(content))
        amendment_change(target, 5, blob(content))
        refresh(target)
        transition(name, base, target, False, diagnostic)

    for name, column, value in [('id', 0, 'CL-TASAKI2020-9999'),
                                 ('order', 2, '000015.0099'),
                                 ('page', 3, 'PG-TASAKI2020-0016'),
                                 ('locator', 4, 'unreviewed-locator'),
                                 ('classification', 5, 'assertion'),
                                 ('subkind', 6, 'theorem'),
                                 ('exclusion', 9, 'new-exclusion'),
                                 ('tombstone', 11, 'true')]:
        target = case('metadata-' + name)
        mutate(target, 'claims.tsv', claim, column, value)
        refresh(target)
        transition('frozen-' + name, base, target, False)

    unowned = case('unowned-other-claim')
    mutate(unowned, 'claims.tsv', 'CL-TASAKI2020-0002', 7, 'An unrelated unreviewed assertion.')
    refresh(unowned)
    transition('unowned-other-content-change', base, unowned, False, 'unmanifested claim drift')
    for name, record in [
            ('claim-successors.tsv', ['SE-RUNTIME-0001', event, correction_id, claim, '1', 'new_successor', 'CL-TASAKI2020-0002']),
            ('source-item-additions.tsv', ['IA-RUNTIME-0001', event, correction_id, '1', 'IT-RUNTIME-0001', review])]:
        target = case('extra-' + name)
        write(target, name, table(target, name) + [record])
        static('amendment-cannot-add-' + name, target, False, 'cannot introduce successors or source items')

    late_base, late_current = case('late-base', base), case('late-current')
    for target in (late_base, late_current):
        mutate(target, 'source-progress.tsv', 'TASAKI2020', 1, 'skeleton_frozen')
    transition('late-stage-source', late_base, late_current, False, 'requires a pre-R4 source')
    bound_base, bound_current = case('bound-base', base), case('bound-current')
    binding = ['CL-TASAKI2020-0002', 'statement', 'NONE', 'LatticeSystem.Claims.Runtime', 'PENDING', 'NONE']
    for target in (bound_base, bound_current):
        write(target, 'bindings.tsv', table(target, 'bindings.tsv') + [binding])
    transition('already-bound-other-claim-in-source', bound_base, bound_current, False, 'source already has bindings')
    for name, record in [('slices.tsv', ['SL-RUNTIME-0001', '1', claim]),
                         ('dependencies.tsv', [claim, 'requires', 'CL-TASAKI2020-0002', 'NONE']),
                         ('dependencies.tsv', ['CL-TASAKI2020-0002', 'consequence_of', claim, 'NONE']),
                         ('claim-axioms.tsv', [claim, 'AX-PROJECT-0001'])]:
        suffix = name + str(count)
        before, after = case('scope-base-' + suffix, base), case('scope-current-' + suffix)
        for target in (before, after):
            write(target, name, table(target, name) + [record])
        transition('existing-target-' + suffix, before, after, False, 'skeleton or axiom relations')

    stale_review = case('unrefreshed-vocab-review')
    mutate(stale_review, 'claim-vocabulary-review.tsv', claim, 2,
           next(row[2] for row in table(base, 'claim-vocabulary-review.tsv')[1:] if row[0] == claim))
    transition('unrefreshed-vocabulary-review', base, stale_review, False, 'refreshed vocabulary review')
    vocab_basis = case('vocab-basis')
    mutate(vocab_basis, 'claim-vocabulary-review.tsv', claim, 1, 'project_vocabulary')
    transition('vocabulary-review-basis-drift', base, vocab_basis, False, 'refreshed vocabulary review')
    vocab_use = case('vocab-use')
    write(vocab_use, 'claim-vocabulary.tsv', table(vocab_use, 'claim-vocabulary.tsv') + [[claim, 'VO-TASAKI2020-0001']])
    transition('vocabulary-use-drift', base, vocab_use, False, 'changed vocabulary use')
    wrong_counts = case('wrong-census-count')
    current_count = next(r[2] for r in table(wrong_counts, 'source-invariants.tsv')[1:] if r[0] == 'TASAKI2020')
    mutate(wrong_counts, 'source-invariants.tsv', 'TASAKI2020', 2, str(int(current_count) + 1))
    transition('stale-census-count', base, wrong_counts, False, 'census invariant count is stale')

    later = root / 'later-event'
    final_content = 'For every admissible x, F(x) = conjugate("G(x)") + ε.'
    second_event, _, _, second_amendment, _, _ = prepare_amendment(current, later, final_content)
    static('later-event-history-static', later)
    transition('repeat-amendment-exact-new-base', current, later)
    base_diff('repeat-amendment-dedicated-route', current, later, event_id=second_event)
    base_diff('repeat-amendment-ordinary-route-rejects', current, later, False)
    base_diff('later-ordinary-freezes-both-events', later, later)
    historical = case('historical-amendment-drift', later)
    amendment_change(historical, 7, 'HISTORICAL-DRIFT')
    transition('historical-row-mutation', current, historical, False, 'historical correction ledger drift')
    stale_chain = case('history-chain-stale', later)
    mutate(stale_chain, 'claim-content-amendments.tsv', second_amendment, 4, blob(old[7]))
    static('stale-history-chain', stale_chain, False, 'history chain is stale')

    multi_base, multi_current = case('multi-base', base), case('multi-current')
    for target in (multi_base, multi_current):
        sources = table(target, 'sources.tsv')
        extra = sources[1].copy()
        extra[0], extra[2], extra[4], extra[12], extra[13] = 'SRB', '2', 'SRB2026', 'source-b', 'runtime-source-b.pdf'
        write(target, 'sources.tsv', sources + [extra])
        write(target, 'source-progress.tsv', table(target, 'source-progress.tsv') + [['SRB', 'registered', 'RUNTIME-SOURCE-B-REVIEW']])
    transition('unrelated-source-preserved', multi_base, multi_current)
    foreign_drift = case('foreign-source-drift', multi_current)
    mutate(foreign_drift, 'sources.tsv', 'SRB', 5, 'unreviewed-source-title')
    transition('unrelated-source-drift-rejected', multi_base, foreign_drift, False, 'unrelated frozen registry drift')

    historical_ordinary = case('historical-ledger-piggyback', later)
    records = table(historical_ordinary, 'claim-content-amendments.tsv')
    records[-1][0] = unused_id(later, 'claim-content-amendments.tsv', 'CA-PIGGYBACK')
    write(historical_ordinary, 'claim-content-amendments.tsv', records)
    base_diff('historical-event-no-ordinary-bypass', later, historical_ordinary, False, event_id=second_event,
              diagnostic='historical correction ledger drift')

    # Omitted assertions have no predecessor. Their creation still goes through
    # the same reviewed event and immutable-history boundaries as amendments.
    omission_start = count - 1
    static('omitted-claim-static', omitted)
    expect('omitted-claim-registry', True, [str(project / 'scripts/check-registry.sh'), str(omitted)])
    expect('omitted-claim-item-contract', True, [str(project / 'scripts/check-source-items.sh'), str(omitted)])
    base_diff('omitted-claim-dedicated-route', base, omitted, event_id=omission_event)
    base_diff('omitted-claim-ordinary-rejected', base, omitted, False, diagnostic='frozen invariants regression')
    base_diff('omitted-claim-later-ordinary-freeze', omitted, omitted)
    base_diff('omitted-claim-no-historical-exception', omitted, omitted, event_id=omission_event)
    existing_item = root / 'omitted-existing-item'
    prepare_omission(base, existing_item, new_item=False)
    transition('omitted-claim-existing-item', base, existing_item)
    expect('omitted-existing-item-contract', True,
           [str(project / 'scripts/check-source-items.sh'), str(existing_item)])

    mixed = case('mixed-addition-amendment', omitted)
    nr = unused_id(mixed, 'claim-normalization-reviews.tsv', 'NR-RUNTIME')
    cc = unused_id(mixed, 'claim-corrections.tsv', 'CC-RUNTIME')
    ca = unused_id(mixed, 'claim-content-amendments.tsv', 'CA-RUNTIME')
    write(mixed, 'claim-normalization-reviews.tsv', table(mixed, 'claim-normalization-reviews.tsv') + [
        [nr, omission_event, '2', claim, 'exact_statement_readiness', 'amend_content',
         'closed', 'restore-source-condition', omission_review]])
    write(mixed, 'claim-corrections.tsv', table(mixed, 'claim-corrections.tsv') + [
        [cc, omission_event, '2', nr, claim, 'amend_content', old[5], old[6], old[5], old[6]]])
    write(mixed, 'claim-content-amendments.tsv', table(mixed, 'claim-content-amendments.tsv') + [
        [ca, omission_event, cc, claim, blob(old[7]), blob(new_content), page[9], omission_review]])
    mutate(mixed, 'claims.tsv', claim, 7, new_content)
    mutate(mixed, 'claims.tsv', claim, 8, blob(new_content))
    mutate(mixed, 'claim-vocabulary-review.tsv', claim, 2, omission_review)
    refresh(mixed)
    transition('mixed-addition-and-amendment', base, mixed)
    base_diff('mixed-addition-and-amendment-route', base, mixed, event_id=omission_event)

    added_later = root / 'added-claim-later-amendment'
    original_claim = claim
    claim = omitted_claim
    added_event, _, _, _, _, _ = prepare_amendment(omitted, added_later, 'The two finite classes have a common size.')
    claim = original_claim
    transition('historical-added-claim-later-amended', omitted, added_later)
    static('historical-addition-static-after-amendment', added_later)
    base_diff('historical-addition-amendment-route', omitted, added_later, event_id=added_event)

    added_reclassified = case('added-claim-later-reclassified', omitted)
    event_rows = table(added_reclassified, 'correction-events.tsv')
    reclass_event = 'RUNTIME-ADDED-RECLASSIFY'
    reclass_review = reclass_event + '-REVIEW'
    event_rows.append([reclass_event, str(len(event_rows)), 'TASAKI2020',
                       subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project).decode().strip(), reclass_review])
    write(added_reclassified, 'correction-events.tsv', event_rows)
    nr = unused_id(added_reclassified, 'claim-normalization-reviews.tsv', 'NR-RUNTIME')
    cc = unused_id(added_reclassified, 'claim-corrections.tsv', 'CC-RUNTIME')
    write(added_reclassified, 'claim-normalization-reviews.tsv', table(added_reclassified, 'claim-normalization-reviews.tsv') + [
        [nr, reclass_event, '1', omitted_claim, 'exact_statement_readiness', 'reclassify', 'closed',
         'refine-source-classification', reclass_review]])
    write(added_reclassified, 'claim-corrections.tsv', table(added_reclassified, 'claim-corrections.tsv') + [
        [cc, reclass_event, '1', nr, omitted_claim, 'reclassify', 'assertion', 'unnumbered_obligation',
         'definition', 'definition']])
    mutate(added_reclassified, 'claims.tsv', omitted_claim, 5, 'definition')
    mutate(added_reclassified, 'claims.tsv', omitted_claim, 6, 'definition')
    mutate(added_reclassified, 'claim-vocabulary-review.tsv', omitted_claim, 2, reclass_review)
    refresh(added_reclassified)
    transition('historical-added-claim-later-reclassified', omitted, added_reclassified)
    static('historical-addition-static-after-reclassification', added_reclassified)
    added_bound = case('historical-addition-after-r4', omitted)
    mutate(added_bound, 'source-progress.tsv', 'TASAKI2020', 1, 'skeleton_frozen')
    write(added_bound, 'bindings.tsv', table(added_bound, 'bindings.tsv') + [
        [omitted_claim, 'LatticeSystem.Claims.statement', 'NONE', 'LatticeSystem.Claims.Front', 'PENDING', 'NONE']])
    static('historical-addition-static-after-r4', added_bound)
    project_vocab = case('addition-project-vocabulary', omitted)
    mutate(project_vocab, 'claim-vocabulary-review.tsv', omitted_claim, 1, 'project_vocabulary')
    write(project_vocab, 'claim-vocabulary.tsv', table(project_vocab, 'claim-vocabulary.tsv') + [
        [omitted_claim, 'VO-TASAKI2020-0001']])
    transition('addition-reviewed-existing-project-vocabulary', base, project_vocab)

    two_additions = root / 'two-additions'
    event2, _, nr2, cc2, claim2, _ = prepare_omission(omitted, two_additions)
    write(two_additions, 'correction-events.tsv', [r for r in table(two_additions, 'correction-events.tsv') if r[0] != event2])
    for name, identifier in [('claim-normalization-reviews.tsv', nr2), ('claim-corrections.tsv', cc2)]:
        mutate(two_additions, name, identifier, 1, omission_event)
        mutate(two_additions, name, identifier, 2, '2')
    mutate(two_additions, 'claim-normalization-reviews.tsv', nr2, 8, omission_review)
    ia2 = table(two_additions, 'source-item-additions.tsv')[-1][0]
    mutate(two_additions, 'source-item-additions.tsv', ia2, 1, omission_event)
    mutate(two_additions, 'source-item-additions.tsv', ia2, 5, omission_review)
    mutate(two_additions, 'claim-vocabulary-review.tsv', claim2, 2, omission_review)
    mutate(two_additions, 'source-invariants.tsv', 'TASAKI2020', 7, omission_review)
    transition('two-owned-omitted-claims', base, two_additions)
    foreign_item_owner = case('addition-valid-foreign-item-owner', two_additions)
    ia1 = table(omitted, 'source-item-additions.tsv')[-1][0]
    mutate(foreign_item_owner, 'source-item-additions.tsv', ia1, 2, cc2)
    mutate(foreign_item_owner, 'source-item-additions.tsv', ia2, 3, '2')
    transition('addition-valid-foreign-item-owner', base, foreign_item_owner, False,
               'new source item contains a successor from a different correction')

    def reject_omission(label, name, identifier, column, value, diagnostic):
        target = case('omission-' + label, omitted)
        mutate(target, name, identifier, column, value)
        if label == 'addition-claim-order':
            refresh(target)
        transition(label, base, target, False, diagnostic)

    for label, name, identifier, column, value, diagnostic in [
            ('addition-existing-id', 'claim-normalization-reviews.tsv', omission_nr, 3, claim,
             'invalid claim correction ledger'),
            ('addition-wrong-old-kind', 'claim-corrections.tsv', omission_cc, 6, 'assertion',
             'invalid omitted claim classification'),
            ('addition-wrong-old-subkind', 'claim-corrections.tsv', omission_cc, 7, 'equation',
             'invalid omitted claim classification'),
            ('addition-wrong-new-kind', 'claim-corrections.tsv', omission_cc, 8, 'definition',
             'classification does not match'),
            ('addition-out-of-scope', 'claim-corrections.tsv', omission_cc, 8, 'out_of_scope',
             'invalid omitted claim classification'),
            ('addition-review-open', 'claim-normalization-reviews.tsv', omission_nr, 6, 'open',
             'invalid claim normalization review ledger'),
            ('addition-review-scope', 'claim-normalization-reviews.tsv', omission_nr, 4, 'proof_readiness',
             'invalid claim normalization review ledger'),
            ('addition-review-token', 'claim-normalization-reviews.tsv', omission_nr, 8, 'WRONG-REVIEW',
             'invalid claim normalization review ledger'),
            ('addition-review-source', 'claims.tsv', omitted_claim, 1, 'SRB',
             'normalization review source mismatch'),
            ('addition-page-unknown', 'claims.tsv', omitted_claim, 3, 'PG-TASAKI2020-9999',
             'source page mismatch'),
            ('addition-page-hash-drift', 'pages.tsv', page[0], 9, '0' * 40,
             'unchanged frozen source page'),
            ('addition-pending-hash', 'claims.tsv', omitted_claim, 8, 'PENDING',
             'content OID is not frozen or is stale'),
            ('addition-stale-hash', 'claims.tsv', omitted_claim, 8, '0' * 40,
             'content OID is not frozen or is stale'),
            ('addition-content-surrogate', 'claims.tsv', omitted_claim, 7, 'True',
             'contentless omitted claim surrogate'),
            ('addition-tombstone', 'claims.tsv', omitted_claim, 11, 'true',
             'active formalization target'),
            ('addition-exclusion', 'claims.tsv', omitted_claim, 9, 'UNREVIEWED',
             'active formalization target'),
            ('addition-vocab-token', 'claim-vocabulary-review.tsv', omitted_claim, 2, 'WRONG-REVIEW',
             'reviewed vocabulary basis and use'),
            ('addition-vocab-basis', 'claim-vocabulary-review.tsv', omitted_claim, 1, 'project_vocabulary',
             'reviewed vocabulary basis and use'),
            ('addition-late-source', 'source-progress.tsv', 'TASAKI2020', 1, 'skeleton_frozen',
             'requires a pre-R4 source'),
            ('addition-item-foreign-owner', 'source-item-additions.tsv',
             table(omitted, 'source-item-additions.tsv')[-1][0], 2, 'CC-UNOWNED-0001',
             'source item addition event or correction mismatch'),
            ('addition-item-token', 'source-item-additions.tsv',
             table(omitted, 'source-item-additions.tsv')[-1][0], 5, 'WRONG-REVIEW',
             'source item addition event or correction mismatch'),
            ('addition-unrelated-claim-drift', 'claims.tsv', 'CL-TASAKI2020-0003', 4, 'unreviewed locator',
             'unmanifested claim drift'),
            ('addition-old-ledger-drift', 'claim-corrections.tsv',
             table(base, 'claim-corrections.tsv')[1][0], 9, 'definition',
             'historical correction ledger drift'),
            ('addition-invariant-review', 'source-invariants.tsv', 'TASAKI2020', 7, 'WRONG-REVIEW',
             'event invariant review'),
            ('addition-physical-page-count', 'source-invariants.tsv', 'TASAKI2020', 1, '535',
             'physical page count is stale'),
            ('addition-source-fingerprint', 'sources.tsv', 'TASAKI2020', 14, 'PENDING',
             'source fingerprints changed or are not frozen'),
            ('addition-claim-order', 'claims.tsv', omitted_claim, 2, 'invalid-order',
             'bad claim order key'),
            ('addition-item-position', 'item-claims.tsv', omitted_item, 1, '2',
             'item relation positions are not contiguous')]:
        reject_omission(label, name, identifier, column, value, diagnostic)

    for label, name, column, diagnostic in [
            ('addition-missing-item', 'item-claims.tsv', 2, 'exactly one source item'),
            ('addition-missing-vocab', 'claim-vocabulary-review.tsv', 0, 'reviewed vocabulary basis and use'),
            ('addition-missing-item-manifest', 'source-item-additions.tsv', 2, 'unmanifested source item addition'),
            ('addition-missing-correction', 'claim-corrections.tsv', 0, 'invalid claim correction ledger')]:
        target = case(label, omitted)
        key = omission_cc if name in {'claim-corrections.tsv', 'source-item-additions.tsv'} else omitted_claim
        write(target, name, [r for i, r in enumerate(table(target, name)) if i == 0 or r[column] != key])
        transition(label, base, target, False, diagnostic)

    duplicate_relation = case('addition-duplicate-item-relation', omitted)
    relation = next(r for r in table(duplicate_relation, 'item-claims.tsv')[1:] if r[2] == omitted_claim)
    write(duplicate_relation, 'item-claims.tsv', table(duplicate_relation, 'item-claims.tsv') + [relation])
    transition('addition-duplicate-item-relation', base, duplicate_relation, False, 'exactly one source item')
    overlap = case('addition-successor-overlap', omitted)
    write(overlap, 'claim-successors.tsv', table(overlap, 'claim-successors.tsv') + [
        ['SE-RUNTIME-OMISSION-0001', omission_event, omission_cc, claim, '1', 'new_successor', omitted_claim]])
    transition('addition-successor-overlap', base, overlap, False, 'cannot have successor provenance')

    for label, name, row, diagnostic in [
            ('addition-r4-binding', 'bindings.tsv', [omitted_claim, 'LatticeSystem.Claims.statement', 'NONE',
                                                   'LatticeSystem.Claims.Front', 'PENDING', 'NONE'],
             'source already has bindings'),
            ('addition-slice', 'slices.tsv', ['SL-RUNTIME-0001', '1', omitted_claim],
             'skeleton or axiom relations'),
            ('addition-dependency', 'dependencies.tsv', [omitted_claim, 'requires', claim, 'NONE'],
             'skeleton or axiom relations'),
            ('addition-reverse-dependency', 'dependencies.tsv', [claim, 'required_by', omitted_claim, 'REVIEW'],
             'skeleton or axiom relations'),
            ('addition-axiom', 'claim-axioms.tsv', [omitted_claim, 'AX-RUNTIME-0001'],
             'skeleton or axiom relations'),
            ('addition-vocab-use', 'claim-vocabulary.tsv', [omitted_claim, 'VO-TASAKI2020-0001'],
             'reviewed vocabulary basis and use')]:
        target = case(label, omitted)
        write(target, name, table(target, name) + [row])
        transition(label, base, target, False, diagnostic)

    for action in ('reclassify', 'exclude_nonclaim', 'split', 'amend_content'):
        target = case('none-old-' + action, omitted)
        mutate(target, 'claim-normalization-reviews.tsv', omission_nr, 5, action)
        mutate(target, 'claim-corrections.tsv', omission_cc, 5, action)
        transition('none-old-invalid-for-' + action, base, target, False,
                   'correction predecessor source mismatch')
        if action != 'amend_content':
            static('none-old-static-invalid-for-' + action, target, False,
                   'NONE old classification requires add_omitted_claim')
    reused = case('addition-reuses-existing-id', omitted)
    mutate(reused, 'claim-normalization-reviews.tsv', omission_nr, 3, claim)
    mutate(reused, 'claim-corrections.tsv', omission_cc, 4, claim)
    transition('addition-reuses-existing-id', base, reused, False, 'must introduce a fresh claim ID')
    missing_claim = case('addition-missing-claim', omitted)
    write(missing_claim, 'claims.tsv', [r for r in table(missing_claim, 'claims.tsv') if r[0] != omitted_claim])
    transition('addition-missing-claim', base, missing_claim, False, 'must introduce a fresh claim ID')
    unowned = case('addition-unowned-claim', omitted)
    rows = table(unowned, 'claims.tsv')
    extra = next(r[:] for r in rows[1:] if r[0] == omitted_claim)
    extra[0] = unused_id(unowned, 'claims.tsv', 'CL-TASAKI2020')
    extra[2] += '.0001'
    rows.insert(rows.index(next(r for r in rows if r[0] == omitted_claim)) + 1, extra)
    write(unowned, 'claims.tsv', rows)
    transition('addition-unowned-new-claim', base, unowned, False, 'split successor provenance is incomplete')
    for column, diagnostic in [(2, 'census invariant count is stale'),
                               (3, 'formalization target count is stale'), (6, 'census OID is stale')]:
        target = case('addition-stale-invariant-' + str(column), omitted)
        invariant = next(r for r in table(target, 'source-invariants.tsv')[1:] if r[0] == 'TASAKI2020')
        value = '0' * 40 if column == 6 else str(int(invariant[column]) + 1)
        mutate(target, 'source-invariants.tsv', 'TASAKI2020', column, value)
        transition('addition-stale-invariant-' + str(column), base, target, False, diagnostic)
    print('test-content-amendments-runtime: omitted-claim cases ' + str(count - omission_start))
    print('test-content-amendments-runtime: ok (' + str(count) + ' cases; ' +
          str(accepted) + ' positive, ' + str(rejected) + ' rejection cases)')
PY
