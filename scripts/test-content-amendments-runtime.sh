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

count = 0
def expect(label, expected, command, diagnostic=''):
    global count
    result = subprocess.run(command, cwd=project, env=os.environ,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if (result.returncode == 0) != expected or (diagnostic and diagnostic not in result.stdout):
        print('test-content-amendments-runtime: unexpected result:', label, file=sys.stderr)
        print(result.stdout, file=sys.stderr)
        raise SystemExit(1)
    count += 1

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
    mutate(wrong_counts, 'source-invariants.tsv', 'TASAKI2020', 2, '3183')
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
    print('test-content-amendments-runtime: ok (' + str(count) + ' cases)')
PY
