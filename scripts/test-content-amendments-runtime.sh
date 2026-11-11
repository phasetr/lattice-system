#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
[[ $# -eq 0 ]] || shift
# Full-suite assertions are mandatory even under an optimized caller. The
# adapter-only child retains its caller's mode for the explicit optimized oracles.
if [[ "${1:-}" != --adapt-empty-r4-only ]]; then
  export PYTHONOPTIMIZE=0
fi
python3 - "$PROJECT_ROOT" "$@" <<'PY'
import csv
import importlib.util
import json
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

def binding_row(root, claim_id):
    # Invalid R4-state cases still use the actual expanded binding schema.
    record = next(row for row in table(root, 'claims.tsv')[1:] if row[0] == claim_id)
    proof = record[5] in {'assertion', 'conjecture'}
    shapes = {'assertion': 'proof_proposition', 'conjecture': 'proof_proposition',
              'definition': 'definition_value', 'notation': 'notation_expansion',
              'hypothesis': 'hypothesis_prop', 'domain': 'domain_type'}
    return [claim_id, 'LatticeSystem.Claims.Runtime.statement',
            'LatticeSystem.Claims.Runtime.proof' if proof else 'NONE',
            'LatticeSystem.Claims.Runtime', 'definition', shapes[record[5]],
            'PENDING', 'PENDING', 'proof_stub' if proof else 'definitional',
            'theorem' if proof else 'NONE', 'PENDING' if proof else 'NONE',
            'NONE', 'NONE', 'NONE', 'RUNTIME-BINDING-REVIEW']

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

def adapt_empty_r4_schemas(target):
    # Historical source-data fixtures still need today's empty infrastructure
    # schemas. Never reinterpret populated artifact rows during this adapter.
    for name in ('bindings.tsv', 'axioms.tsv', 'claim-context.tsv',
                 'statement-modules.tsv', 'statement-imports.tsv'):
        expected = table(project, name)[0]
        path = target / 'registry' / name
        if not path.exists():
            write(target, name, [expected])
            continue
        recorded = table(target, name)
        if recorded and recorded[0] == expected:
            continue  # Preserve current files byte-for-byte, including final LF.
        if len(recorded) != 1:
            raise RuntimeError('cannot migrate populated historical R4 fixture: ' + name)
        write(target, name, [expected])

def clone_commit_registry(commit, target):
    paths = subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', commit, 'registry'], cwd=project).decode().splitlines()
    for relative in paths:
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(subprocess.check_output(['git', 'show', commit + ':' + relative], cwd=project))
    if not (target / 'registry/claim-content-amendments.tsv').exists():
        write(target, 'claim-content-amendments.tsv', [header])
    adapt_empty_r4_schemas(target)

# Exercise the same helper under optimization without recursively running the
# transition suite. Only explicit, repository-external owned fixtures qualify.
if len(sys.argv) > 2:
    if len(sys.argv) != 4 or sys.argv[2] != '--adapt-empty-r4-only':
        raise SystemExit('invalid adapter-only arguments')
    test_root = Path(os.environ.get('LATTICE_TEST_ROOT', '/')).resolve()
    target = Path(sys.argv[3]).resolve()
    if (test_root == project or test_root in project.parents or project in test_root.parents
            or test_root not in target.parents):
        raise SystemExit('adapter-only target must be below an external LATTICE_TEST_ROOT')
    adapt_empty_r4_schemas(target)
    raise SystemExit(0)

# Adapter-only children exit above and retain their explicit optimized mode.
# The full suite must never silently discard its assertion oracles.
if not __debug__:
    raise SystemExit('test-content-amendments-runtime: full mode requires Python assertions')

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


def prepare_grouped_omissions(before, after):
    first = after.with_name(after.name + '-first')
    event, review, nr1, cc1, claim1, item = prepare_omission(before, first)
    event2, _, nr2, cc2, claim2, item2 = prepare_omission(first, after)
    write(after, 'correction-events.tsv', [r for r in table(after, 'correction-events.tsv') if r[0] != event2])
    for name, identifier in [('claim-normalization-reviews.tsv', nr2), ('claim-corrections.tsv', cc2)]:
        mutate(after, name, identifier, 1, event)
        mutate(after, name, identifier, 2, '2')
    mutate(after, 'claim-normalization-reviews.tsv', nr2, 8, review)
    mutate(after, 'claim-vocabulary-review.tsv', claim2, 2, review)
    write(after, 'source-items.tsv', [r for r in table(after, 'source-items.tsv') if r[0] != item2])
    write(after, 'source-item-additions.tsv',
          [r for r in table(after, 'source-item-additions.tsv') if r[4] != item2])
    relations = [r for r in table(after, 'item-claims.tsv') if r[0] != item2]
    index = next(i for i, r in enumerate(relations) if r[0] == item)
    relations.insert(index + 1, [item, '2', claim2])
    write(after, 'item-claims.tsv', relations)
    page = next(r[3] for r in table(after, 'claims.tsv')[1:] if r[0] == claim1)
    page_order = next(r[2] for r in table(after, 'pages.tsv')[1:] if r[0] == page)
    locator = 'PDF p. ' + str(int(page_order)) + '; Footnote 999'
    for column, value in [(4, 'footnote'), (5, 'Footnote 999'), (7, locator),
                          (10, 'PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1')]:
        mutate(after, 'source-items.tsv', item, column, value)
    for position, identifier in enumerate((claim1, claim2), 1):
        content = 'Synthetic private assertion ' + str(position) + ' for a finite test family.'
        mutate(after, 'claims.tsv', identifier, 4, locator + '; assertion ' + str(position))
        mutate(after, 'claims.tsv', identifier, 7, content)
        mutate(after, 'claims.tsv', identifier, 8, blob(content))
    mutate(after, 'source-invariants.tsv', 'TASAKI2020', 7, review)
    refresh(after)
    return event, review, (nr1, nr2), (cc1, cc2), (claim1, claim2), item

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
    if label.startswith('adapter-old-populated-'):
        print(next(line for line in result.stdout.splitlines() if diagnostic in line))
    return result.stdout

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

    # Empty schema changes and new empty R4 tables do not create artifacts.
    old_schema = case('empty-r4-schema-migration-base', base)
    write(old_schema, 'bindings.tsv', [['claim_id', 'statement_decl', 'proof_decl',
                                      'module', 'statement_oid', 'nonvacuity_decl']])
    write(old_schema, 'axioms.tsv', [['axiom_id', 'declaration', 'module', 'category',
                                    'source_locator', 'rationale', 'reopen_condition']])
    for name in ('claim-context.tsv', 'statement-modules.tsv', 'statement-imports.tsv'):
        (old_schema / 'registry' / name).unlink()
    transition('empty-r4-schema-migration', old_schema, current)
    adapter_command = [str(project / 'scripts/test-content-amendments-runtime.sh'),
                       str(project), '--adapt-empty-r4-only']
    adapter_empty = case('adapter-historical-empty', old_schema)
    expect('adapter-historical-empty', True, adapter_command + [str(adapter_empty)])
    artifact_names = ('bindings.tsv', 'axioms.tsv', 'claim-context.tsv',
                      'statement-modules.tsv', 'statement-imports.tsv')
    if any(table(adapter_empty, name) != [table(project, name)[0]] for name in artifact_names):
        raise SystemExit('adapter did not produce current empty R4 schemas')
    adapter_current = case('adapter-current-populated', base)
    adapter_rows = {
        'bindings.tsv': binding_row(base, claim),
        'axioms.tsv': ['AX-PROJECT-9001', 'LatticeSystem.Axioms.State.fixture',
                       'LatticeSystem.Axioms.State', 'state', 'fixture', 'fixture', 'remove', 'PENDING'],
        'claim-context.tsv': ['CL-TASAKI2020-0002', '1', claim, 'term_reference', 'inherited', 'FIXTURE'],
        'statement-modules.tsv': ['LatticeSystem.Claims.Front', 'LatticeSystem/Claims/Front.lean', 'leaf'],
        'statement-imports.tsv': ['LatticeSystem.Claims.Front', '1', 'Mathlib.Init', 'true', 'false', 'false']}
    for name, row in adapter_rows.items():
        (adapter_current / 'registry' / name).write_bytes(
            ('\t'.join(table(project, name)[0]) + '\n' + '\t'.join(row)).encode())
    adapter_bytes = {name: (adapter_current / 'registry' / name).read_bytes() for name in artifact_names}
    expect('adapter-current-populated', True, adapter_command + [str(adapter_current)])
    if any((adapter_current / 'registry' / name).read_bytes() != adapter_bytes[name] for name in artifact_names):
        raise SystemExit('adapter rewrote a current-schema artifact file')
    for name in ('bindings.tsv', 'axioms.tsv'):
        adapter_old = case('adapter-old-populated-' + name, old_schema)
        with (adapter_old / 'registry' / name).open('ab') as stream:
            stream.write(b'populated\thistorical\tartifact\trows\tmust\tbe\tpreserved\n')
        expect('adapter-old-populated-' + name, False,
               ['env', 'PYTHONOPTIMIZE=1'] + adapter_command + [str(adapter_old)],
               'cannot migrate populated historical R4 fixture: ' + name)
    # The same relaxation must not reinterpret already populated artifact data.
    for name, row, diagnostic in [
            ('statement-modules.tsv', ['LatticeSystem.Claims.Front',
                                       'LatticeSystem/Claims/Front.lean', 'leaf'], 'R4 artifact'),
            ('axioms.tsv', ['AX-RUNTIME-0001', 'LatticeSystem.Axioms.State.fixture',
                            'LatticeSystem.Axioms.State', 'state', 'fixture',
                            'fixture', 'reopen', 'PENDING'], 'axiom artifact')]:
        before = case('populated-' + name + '-base', base)
        after = case('populated-' + name + '-current')
        for target in (before, after):
            write(target, name, table(target, name) + [row])
        changed = table(after, name)
        changed[0][-1] += '_drift'
        write(after, name, changed)
        transition('populated-artifact-header-drift-' + name,
                   before, after, False, diagnostic)

    omitted = root / 'omitted-claim'
    omission_event, omission_review, omission_nr, omission_cc, omitted_claim, omitted_item = prepare_omission(base, omitted)
    transition('omitted-claim-new-item', base, omitted)

    grouped = root / 'grouped-omissions'
    grouped_event, grouped_review, grouped_nrs, grouped_ccs, grouped_claims, grouped_item = prepare_grouped_omissions(base, grouped)
    transition('two-omissions-one-named-item', base, grouped)

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
    binding = binding_row(bound_base, 'CL-TASAKI2020-0002')
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
        binding_row(added_bound, omitted_claim)])
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

    grouped_start = count - 1
    nr1, nr2 = grouped_nrs
    cc1, cc2 = grouped_ccs
    first_claim, second_claim = grouped_claims
    grouped_ia = table(grouped, 'source-item-additions.tsv')[-1][0]
    static('grouped-omissions-static', grouped)
    base_diff('grouped-omissions-dedicated-route', base, grouped, event_id=grouped_event)
    base_diff('grouped-omissions-ordinary-rejected', base, grouped, False,
              diagnostic='frozen invariants regression')
    base_diff('grouped-omissions-later-ordinary-freeze', grouped, grouped)
    base_diff('grouped-omissions-historical-event-is-ordinary', grouped, grouped, event_id=grouped_event)

    # Exercise the unchanged public grouping and renderer with the same fixture,
    # rather than a separately constructed approximation of the new item.
    spec = importlib.util.spec_from_file_location('public_docs', project / 'scripts/generate-public-docs.py')
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    data = generator.load_registry(grouped)
    catalog = generator.public_catalog(data)
    named = [item for item in catalog['items'] if item['item_id'] == grouped_item]
    assert len(named) == 1
    assert named[0]['item_kind'] == 'footnote' and named[0]['source_label'] == 'Footnote 999'
    assert [c['claim_id'] for c in named[0]['claims']] == list(grouped_claims)
    anchor_item = next(r for r in table(grouped, 'source-items.tsv')[1:] if r[0] == grouped_item)
    assert named[0]['public_group'] == anchor_item[8] and named[0]['public_slug'] == anchor_item[9]
    assert len(data['source_items']) == len(table(base, 'source-items.tsv'))
    outputs = generator.build_outputs(catalog)
    public_text = json.dumps(catalog) + ''.join(outputs.values())
    for row in table(grouped, 'claims.tsv')[1:]:
        if row[0] in grouped_claims:
            assert row[7] not in public_text and row[8] not in public_text
    assert grouped_review not in public_text and 'normalized_content' not in public_text
    generator.write_outputs(grouped, outputs)
    assert generator.check_outputs(grouped, outputs, quiet=True)
    count += 1
    accepted += 1

    reversed_creators = case('grouped-correction-position-independent', grouped)
    records = table(reversed_creators, 'claim-corrections.tsv')
    earlier, later = records[-2:]
    earlier[2], later[2] = '2', '1'
    write(reversed_creators, 'claim-corrections.tsv', records[:-2] + [later, earlier])
    transition('grouped-owner-is-first-relation-not-correction-position', base, reversed_creators)

    for label, name, identifier, column, value, diagnostic in [
            ('noncanonical-owner', 'source-item-additions.tsv', grouped_ia, 2, cc2,
             'new source item contains a successor from a different correction'),
            ('secondary-open-review', 'claim-normalization-reviews.tsv', nr2, 6, 'open',
             'invalid claim normalization review ledger'),
            ('secondary-source', 'claims.tsv', second_claim, 1, 'SRB',
             'normalization review source mismatch'),
            ('secondary-page', 'claims.tsv', second_claim, 3,
             next(r[0] for r in table(base, 'pages.tsv')[1:] if r[0] != page[0]),
             'source item mismatch'),
            ('secondary-review-token', 'claim-vocabulary-review.tsv', second_claim, 2, 'WRONG-REVIEW',
             'reviewed vocabulary basis and use'),
            ('relation-position', 'item-claims.tsv', grouped_item, 1, '3',
             'item relation positions are not contiguous'),
            ('first-claim-order', 'source-items.tsv', grouped_item, 2, anchor_item[2] + '.0001',
             'item order does not match first claim'),
            ('reused-item', 'source-item-additions.tsv', grouped_ia, 4,
             table(base, 'source-items.tsv')[1][0], 'source item addition reuses a frozen item ID')]:
        target = case('grouped-' + label, grouped)
        mutate(target, name, identifier, column, value)
        transition('grouped-' + label, base, target, False, diagnostic)

    for missing, records_to_remove in [
            ('creator', [('claim-corrections.tsv', cc2)]),
            ('review', [('claim-normalization-reviews.tsv', nr2)]),
            ('both', [('claim-corrections.tsv', cc2), ('claim-normalization-reviews.tsv', nr2)])]:
        target = case('grouped-secondary-missing-' + missing, grouped)
        for name, identifier in records_to_remove:
            write(target, name, [r for r in table(target, name) if r[0] != identifier])
        diagnostic = 'split successor provenance is incomplete' if missing == 'both' else 'invalid claim correction ledger'
        transition('grouped-secondary-missing-' + missing, base, target, False, diagnostic)

    foreign_event = case('grouped-foreign-event', grouped)
    events = table(foreign_event, 'correction-events.tsv')
    other_event = 'RUNTIME-FOREIGN-OMISSION'
    other_review = other_event + '-REVIEW'
    events.append([other_event, str(len(events)), 'TASAKI2020', events[-1][3], other_review])
    write(foreign_event, 'correction-events.tsv', events)
    for name, identifier in [('claim-normalization-reviews.tsv', nr2), ('claim-corrections.tsv', cc2)]:
        mutate(foreign_event, name, identifier, 1, other_event)
        mutate(foreign_event, name, identifier, 2, '1')
    mutate(foreign_event, 'claim-normalization-reviews.tsv', nr2, 8, other_review)
    mutate(foreign_event, 'claim-vocabulary-review.tsv', second_claim, 2, other_review)
    transition('grouped-secondary-foreign-event', base, foreign_event, False, 'correction event is not reviewed')

    reordered = case('grouped-reordered-relation-rows', grouped)
    relations = table(reordered, 'item-claims.tsv')
    first_index = next(i for i, r in enumerate(relations) if r[0] == grouped_item)
    relations[first_index:first_index + 2] = relations[first_index:first_index + 2][::-1]
    write(reordered, 'item-claims.tsv', relations)
    # Even matching the first encountered row cannot bypass the canonical
    # relation-position order enforced by the transition's source-item gate.
    mutate(reordered, 'source-item-additions.tsv', grouped_ia, 2, cc2)
    transition('grouped-reordered-relation-rows', base, reordered, False,
               'item relation positions are not contiguous')

    frozen_member = case('grouped-frozen-member', grouped)
    relations = table(frozen_member, 'item-claims.tsv')
    index = max(i for i, r in enumerate(relations) if r[0] == grouped_item)
    relations.insert(index + 1, [grouped_item, '3', claim])
    write(frozen_member, 'item-claims.tsv', relations)
    transition('grouped-frozen-member', base, frozen_member, False, 'new source item contains a frozen predecessor claim')
    duplicate_member = case('grouped-secondary-duplicate-use', grouped)
    relations = table(duplicate_member, 'item-claims.tsv')
    old_item = table(base, 'source-items.tsv')[1][0]
    index = max(i for i, r in enumerate(relations) if r[0] == old_item)
    position = 1 + max(int(r[1]) for r in relations[1:] if r[0] == old_item)
    relations.insert(index + 1, [old_item, str(position), second_claim])
    write(duplicate_member, 'item-claims.tsv', relations)
    transition('grouped-secondary-duplicate-use', base, duplicate_member, False, 'exactly one source item')
    duplicate_ia = case('grouped-duplicate-manifest', grouped)
    manifest = table(duplicate_ia, 'source-item-additions.tsv')
    extra = manifest[-1].copy()
    extra[0] = unused_id(duplicate_ia, 'source-item-additions.tsv', 'IA-RUNTIME')
    extra[3] = '2'
    write(duplicate_ia, 'source-item-additions.tsv', manifest + [extra])
    transition('grouped-duplicate-manifest', base, duplicate_ia, False, 'source item is manifested more than once')

    # A fully owned split successor is still ineligible for an omission-owned
    # item, and an omission cannot join an item owned by a split correction.
    split_items = case('independent-split-and-omission-items', two_additions)
    predecessor = next(r for r in table(base, 'claims.tsv')[1:] if r[0] == claim)
    mutate(split_items, 'claim-normalization-reviews.tsv', nr2, 3, claim)
    mutate(split_items, 'claim-normalization-reviews.tsv', nr2, 5, 'split')
    mutate(split_items, 'claim-corrections.tsv', cc2, 4, claim)
    mutate(split_items, 'claim-corrections.tsv', cc2, 5, 'split')
    mutate(split_items, 'claim-corrections.tsv', cc2, 6, predecessor[5])
    mutate(split_items, 'claim-corrections.tsv', cc2, 7, predecessor[6])
    mutate(split_items, 'claim-corrections.tsv', cc2, 8, predecessor[5])
    mutate(split_items, 'claim-corrections.tsv', cc2, 9, predecessor[6])
    for column, value in [(11, 'true'), (12, claim2), (13, 'omitted-source-assertion'), (14, omission_review)]:
        mutate(split_items, 'claims.tsv', claim, column, value)
    write(split_items, 'claim-vocabulary-review.tsv',
          [r for r in table(split_items, 'claim-vocabulary-review.tsv') if r[0] != claim])
    write(split_items, 'claim-successors.tsv', table(split_items, 'claim-successors.tsv') + [[
        unused_id(split_items, 'claim-successors.tsv', 'CS-RUNTIME'), omission_event, cc2, claim, '1', 'new_successor', claim2]])
    refresh(split_items)
    transition('independently-owned-split-and-omission-items', base, split_items)
    mixed_group = case('split-member-in-omission-item', split_items)
    second_item = next(r[0] for r in table(mixed_group, 'item-claims.tsv')[1:] if r[2] == claim2)
    write(mixed_group, 'source-items.tsv', [r for r in table(mixed_group, 'source-items.tsv') if r[0] != second_item])
    write(mixed_group, 'source-item-additions.tsv',
          [r for r in table(mixed_group, 'source-item-additions.tsv') if r[4] != second_item])
    mutate(mixed_group, 'item-claims.tsv', second_item, 0, omitted_item)
    records = table(mixed_group, 'item-claims.tsv')
    for row in records[1:]:
        if row[2] == claim2:
            row[1] = '2'
    write(mixed_group, 'item-claims.tsv', records)
    transition('split-member-in-omission-item', base, mixed_group, False,
               'new source item contains a successor from a different correction')
    split_owner = case('omission-member-in-split-item', mixed_group)
    mutate(split_owner, 'source-item-additions.tsv', ia1, 2, cc2)
    transition('omission-member-in-split-item', base, split_owner, False,
               'new source item contains a successor from a different correction')

    for label, name, identifier, column, value, diagnostic in [
            ('IA-owner', 'source-item-additions.tsv', grouped_ia, 2, cc2, 'historical correction ledger drift'),
            ('metadata', 'source-items.tsv', grouped_item, 6, 'Changed title', 'source item identity/order/label regression')]:
        target = case('grouped-later-frozen-' + label, grouped)
        mutate(target, name, identifier, column, value)
        base_diff('grouped-later-frozen-' + label, grouped, target, False, diagnostic=diagnostic)
    for member in grouped_claims:
        target = case('grouped-later-relation-' + member, grouped)
        write(target, 'item-claims.tsv', [r for r in table(target, 'item-claims.tsv') if r[2] != member])
        base_diff('grouped-later-relation-' + member, grouped, target, False, diagnostic='item-claim regression')
    grouped_later = root / 'grouped-later-amendment'
    claim = second_claim
    try:
        later_event, _, _, _, _, _ = prepare_amendment(grouped, grouped_later, 'The second synthetic test family has positive size.')
    finally:
        claim = original_claim
    assert table(grouped_later, 'source-items.tsv') == table(grouped, 'source-items.tsv')
    assert table(grouped_later, 'item-claims.tsv') == table(grouped, 'item-claims.tsv')
    assert table(grouped_later, 'source-item-additions.tsv') == table(grouped, 'source-item-additions.tsv')
    assert next(r for r in table(grouped_later, 'claims.tsv') if r[0] == first_claim) == next(
        r for r in table(grouped, 'claims.tsv') if r[0] == first_claim)
    transition('grouped-historical-member-amendment', grouped, grouped_later)
    static('grouped-historical-member-amendment-static', grouped_later)
    base_diff('grouped-historical-member-amendment-route', grouped, grouped_later, event_id=later_event)
    print('test-content-amendments-runtime: shared-item cases ' + str(count - grouped_start))

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
            ('addition-r4-binding', 'bindings.tsv', binding_row(omitted, omitted_claim),
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
    # Combined corrections use the real static, transition, ordinary and CI
    # entrypoints. Every named case below has one independently checked oracle.
    combined_start = (count, accepted, rejected)
    assert combined_start == (181, 49, 132)
    content_actions = {'amend_content', 'amend_and_reclassify'}
    history_tables = ('correction-events.tsv', 'claim-normalization-reviews.tsv',
                      'claim-corrections.tsv', 'claim-successors.tsv',
                      'source-item-additions.tsv', 'claim-content-amendments.tsv')
    fixture_cache = {}

    def record(target, name, identifier):
        return next(r for r in table(target, name)[1:] if r[0] == identifier)

    def append(target, name, row):
        write(target, name, table(target, name) + [row])

    def remove(target, name, identifier, column=0):
        write(target, name, [r for i, r in enumerate(table(target, name))
                             if i == 0 or r[column] != identifier])

    def content_event(before, after, target, pair=None, content=None):
        global claim
        saved = claim
        claim = target
        try:
            result = prepare_amendment(before, after, content or
                                       'PRIVATE-COMBINED: F("x") = G(x) + ε, stage ' + after.name)
        finally:
            claim = saved
        event_id, ref, cc, ca, old_row, _ = result
        if pair is not None:
            nr = record(after, 'claim-corrections.tsv', cc)[3]
            mutate(after, 'claim-normalization-reviews.tsv', nr, 5, 'amend_and_reclassify')
            mutate(after, 'claim-corrections.tsv', cc, 5, 'amend_and_reclassify')
            for index, value in enumerate(pair, 5):
                mutate(after, 'claims.tsv', target, index, value)
                mutate(after, 'claim-corrections.tsv', cc, index + 3, value)
        mutate(after, 'source-invariants.tsv', old_row[1], 7, ref)
        refresh(after)
        return event_id

    def reclassification(before, after, target, pair):
        event_id = content_event(before, after, target, pair)
        old_row = record(before, 'claims.tsv', target)
        cc = next(r for r in table(after, 'claim-corrections.tsv')[1:] if r[1] == event_id)
        mutate(after, 'claim-normalization-reviews.tsv', cc[3], 5, 'reclassify')
        mutate(after, 'claim-corrections.tsv', cc[0], 5, 'reclassify')
        remove(after, 'claim-content-amendments.tsv', cc[0], 2)
        for index in (7, 8):
            mutate(after, 'claims.tsv', target, index, old_row[index])
        refresh(after)
        return event_id

    def synthetic_base(name, source=project):
        target = root / ('combined-base-' + name)
        shutil.copytree(source / 'registry', target / 'registry')
        for index, value in [(5, 'assertion'), (6, 'equation')]:
            mutate(target, 'claims.tsv', claim, index, value)
        mutate(target, 'claims.tsv', claim, 8, blob(record(target, 'claims.tsv', claim)[7]))
        refresh(target)
        return target

    def assert_content_step(before, after, event_id):
        event_row = record(after, 'correction-events.tsv', event_id)
        for name in history_tables:
            path = before / 'registry' / name
            if path.exists():
                assert (after / 'registry' / name).read_bytes().startswith(path.read_bytes()), name
        for cc in table(after, 'claim-corrections.tsv')[1:]:
            if cc[1] != event_id or cc[5] not in content_actions:
                continue
            x = cc[4]
            old_row, new_row = record(before, 'claims.tsv', x), record(after, 'claims.tsv', x)
            assert cc[6:8] == old_row[5:7] and cc[8:10] == new_row[5:7]
            assert old_row[7] != new_row[7] and blob(old_row[7]) != blob(new_row[7])
            mutable = (5, 6, 7, 8) if cc[5] == 'amend_and_reclassify' else (7, 8)
            assert all(a == b for i, (a, b) in enumerate(zip(old_row, new_row)) if i not in mutable)
            if cc[5] == 'amend_and_reclassify':
                assert old_row[5:7] != new_row[5:7]
            nrs = [r for r in table(after, 'claim-normalization-reviews.tsv')[1:]
                   if r[1] == event_id and r[3] == x]
            ccs = [r for r in table(after, 'claim-corrections.tsv')[1:]
                   if r[1] == event_id and r[4] == x]
            cas = [r for r in table(after, 'claim-content-amendments.tsv')[1:] if r[2] == cc[0]]
            assert len(nrs) == len(ccs) == len(cas) == 1
            ca = cas[0]
            assert ca[4:6] == [blob(old_row[7]), blob(new_row[7])]
            assert new_row[8] == ca[5] and nrs[0][8] == ca[7] == event_row[4]
            assert record(before, 'pages.tsv', old_row[3]) == record(after, 'pages.tsv', new_row[3])
            assert [r for r in table(before, 'item-claims.tsv')[1:] if r[2] == x] == [
                r for r in table(after, 'item-claims.tsv')[1:] if r[2] == x]
            for relation in [r for r in table(before, 'item-claims.tsv')[1:] if r[2] == x]:
                assert record(before, 'source-items.tsv', relation[0]) == record(after, 'source-items.tsv', relation[0])
        pages, claims = table(after, 'pages.tsv')[1:], table(after, 'claims.tsv')[1:]
        invariant = record(after, 'source-invariants.tsv', event_row[2])
        active = [r for r in claims if r[1] == event_row[2] and r[11] == 'false']
        source_pages = [p for p in pages if p[1] == event_row[2]]
        assert invariant[1:6] == [str(len(source_pages)), str(len(active)),
            str(sum(r[5] != 'out_of_scope' for r in active)),
            str(sum(r[6] == 'equation' for r in active)),
            str(sum(p[0] not in {r[3] for r in active} for p in source_pages))]
        assert invariant[6] == blob(''.join('\t'.join(r) + '\n' for r in pages + claims if r[1] == event_row[2]))
        assert invariant[7] == event_row[4]

    def fixture(kind):
        if kind in fixture_cache:
            return fixture_cache[kind]
        after = root / ('combined-fixture-' + kind)
        x = claim
        if kind in ('F', 'P', 'D', 'K', 'V', 'N', 'A'):
            before = synthetic_base(kind, legacy_base if kind == 'N' else project)
            if kind == 'P':
                mutate(before, 'claims.tsv', x, 8, 'PENDING')
                refresh(before)
            if kind == 'V':
                mutate(before, 'claim-vocabulary-review.tsv', x, 1, 'project_vocabulary')
                for vo in table(project, 'vocabulary.tsv')[1:]:
                    append(before, 'claim-vocabulary.tsv', [x, vo[0]])
            pairs = {'D': ['definition', 'equation'], 'K': ['assertion', 'lemma']}
            event_id = content_event(before, after, x, None if kind == 'A' else
                                     pairs.get(kind, ['definition', 'definition']))
        elif kind == 'Q':
            before = fixture('F')[0]
            event_id = reclassification(before, after, x, ['definition', 'definition'])
        elif kind == 'W':
            before, source, event_id, x = fixture('V')
            shutil.copytree(source, after)
            uses = table(after, 'claim-vocabulary.tsv')
            indices = [i for i, r in enumerate(uses[1:], 1) if r[0] == x]
            assert len(indices) == 2
            uses[indices[0]], uses[indices[1]] = uses[indices[1]], uses[indices[0]]
            write(after, 'claim-vocabulary.tsv', uses)
            reviews = table(after, 'claim-vocabulary-review.tsv')
            row = next(r for r in reviews[1:] if r[0] == x)
            write(after, 'claim-vocabulary-review.tsv', [r for r in reviews if r != row] + [row])
        elif kind == 'M':
            before, first, event_id, x = fixture('F')
            extra_event, _, nr, cc, y, _ = prepare_omission(first, after)
            ref = record(after, 'correction-events.tsv', event_id)[4]
            remove(after, 'correction-events.tsv', extra_event)
            for name, identifier in [('claim-normalization-reviews.tsv', nr), ('claim-corrections.tsv', cc)]:
                mutate(after, name, identifier, 1, event_id)
                mutate(after, name, identifier, 2, '2')
            mutate(after, 'claim-normalization-reviews.tsv', nr, 8, ref)
            ia = next(r for r in table(after, 'source-item-additions.tsv')[1:] if r[1] == extra_event)
            mutate(after, 'source-item-additions.tsv', ia[0], 1, event_id)
            mutate(after, 'source-item-additions.tsv', ia[0], 5, ref)
            mutate(after, 'claim-vocabulary-review.tsv', y, 2, ref)
            mutate(after, 'source-invariants.tsv', 'TASAKI2020', 7, ref)
            refresh(after)
            rows = table(after, 'claims.tsv')[1:]
            assert next(i for i, r in enumerate(rows) if r[0] == y) < len(rows) - 1
            assert record(after, 'claims.tsv', y)[2].startswith(record(before, 'claims.tsv', x)[2] + '.')
        elif kind in ('CC', 'CA', 'AC', 'CRAC', 'OC', 'CS', 'CX'):
            if kind == 'OC':
                seed = synthetic_base(kind)
                before = root / 'combined-omission-first'
                _, _, _, _, x, _ = prepare_omission(seed, before)
                event_id = content_event(before, after, x, ['definition', 'definition'])
            else:
                _, before, _, x = fixture('A' if kind == 'AC' else 'F')
                if kind == 'CRAC':
                    middle = root / 'combined-middle-reclass'
                    middle_event = reclassification(before, middle, x, ['domain', 'domain'])
                    fixture_cache['CRAC-middle'] = (before, middle, middle_event, x)
                    before = middle
                if kind in ('CA', 'CRAC'):
                    event_id = content_event(before, after, x)
                elif kind in ('CC', 'AC'):
                    pair = ['assertion', 'equation'] if kind == 'CC' else ['definition', 'definition']
                    event_id = content_event(before, after, x, pair)
                elif kind == 'CX':
                    event_id = reclassification(before, after, x, ['definition', 'definition'])
                    cc = next(r for r in table(after, 'claim-corrections.tsv')[1:] if r[1] == event_id)
                    ref = record(after, 'correction-events.tsv', event_id)[4]
                    nr = record(after, 'claim-normalization-reviews.tsv', cc[3])
                    mutate(after, 'claim-normalization-reviews.tsv', nr[0], 5, 'exclude_nonclaim')
                    mutate(after, 'claim-corrections.tsv', cc[0], 5, 'exclude_nonclaim')
                    mutate(after, 'claim-corrections.tsv', cc[0], 8, 'out_of_scope')
                    for col, value in [(5, 'out_of_scope'), (9, nr[7]), (10, ref)]:
                        mutate(after, 'claims.tsv', x, col, value)
                    remove(after, 'claim-vocabulary-review.tsv', x)
                    remove(after, 'claim-vocabulary.tsv', x)
                    refresh(after)
                else:
                    event_id, ref, nr, cc, z, _ = prepare_omission(before, after)
                    old_row = record(before, 'claims.tsv', x)
                    mutate(after, 'claim-normalization-reviews.tsv', nr, 3, x)
                    mutate(after, 'claim-normalization-reviews.tsv', nr, 5, 'split')
                    for col, val in [(4, x), (5, 'split'), (6, old_row[5]), (7, old_row[6]),
                                     (8, old_row[5]), (9, old_row[6])]:
                        mutate(after, 'claim-corrections.tsv', cc, col, val)
                    nr_row = record(after, 'claim-normalization-reviews.tsv', nr)
                    for col, val in [(11, 'true'), (12, z), (13, nr_row[7]), (14, ref)]:
                        mutate(after, 'claims.tsv', x, col, val)
                    append(after, 'claim-successors.tsv',
                           [unused_id(after, 'claim-successors.tsv', 'SE-RUNTIME'), event_id, cc, x, '1', 'new_successor', z])
                    remove(after, 'claim-vocabulary-review.tsv', x)
                    remove(after, 'claim-vocabulary.tsv', x)
                    refresh(after)
            # Earlier content events are checked by their own creating snapshots.
            if kind in ('CC', 'CA', 'AC', 'CRAC'):
                historical = [r for r in table(after, 'claim-content-amendments.tsv')[1:] if r[3] == x]
                assert len(historical) >= 2 and historical[-2][5] == historical[-1][4]
                assert historical[-2][5] != record(after, 'claims.tsv', x)[8]
                if kind in ('CC', 'CRAC'):
                    old_cc = record(after, 'claim-corrections.tsv', historical[-2][2])
                    assert old_cc[8:10] != record(after, 'claims.tsv', x)[5:7]
        elif kind == 'HIST':
            _, before, _, x = fixture('CC')
            event_id = content_event(before, after, x, ['definition', 'definition'])
        else:
            raise AssertionError('unknown fixture ' + kind)
        assert_content_step(before, after, event_id)
        fixture_cache[kind] = (before, after, event_id, x)
        return fixture_cache[kind]

    def second_source(target):
        sources = table(target, 'sources.tsv')
        row = sources[1].copy()
        row[0], row[2], row[4], row[12], row[13] = 'SRB', '2', 'SRB2026', 'source-b', 'runtime-source-b.pdf'
        write(target, 'sources.tsv', sources + [row])
        append(target, 'source-progress.tsv', ['SRB', 'registered', 'RUNTIME-SOURCE-B-REVIEW'])

    def mutate_combined(label, before, after, event_id, x):
        cc = next(r for r in table(after, 'claim-corrections.tsv')[1:] if r[1] == event_id and r[4] == x)
        nr, ref = cc[3], record(after, 'correction-events.tsv', event_id)[4]
        cas = [r for r in table(after, 'claim-content-amendments.tsv')[1:] if r[2] == cc[0]]
        ca = cas[0] if cas else None
        other = next(r[0] for r in table(before, 'claims.tsv')[1:] if r[1] == 'TASAKI2020' and r[0] != x)
        def change(name, identifier, col, value):
            mutate(after, name, identifier, col, value)
        def ca_change(col, value):
            change('claim-content-amendments.tsv', ca[0], col, value)
        def new_content(value):
            change('claims.tsv', x, 7, value)
            change('claims.tsv', x, 8, blob(value))
            ca_change(5, blob(value))
        def duplicate_nr(action='amend_and_reclassify'):
            row = record(after, 'claim-normalization-reviews.tsv', nr).copy()
            row[0] = unused_id(after, 'claim-normalization-reviews.tsv', 'NR-DUPLICATE')
            row[2], row[5] = '2', action
            append(after, 'claim-normalization-reviews.tsv', row)
            return row[0]
        simple = {
            'combined-unknown-outcome': ('claim-normalization-reviews.tsv', nr, 5, 'unknown_action'),
            'combined-unknown-action': ('claim-corrections.tsv', cc[0], 5, 'unknown_action'),
            'combined-open-review': ('claim-normalization-reviews.tsv', nr, 6, 'open'),
            'combined-wrong-scope': ('claim-normalization-reviews.tsv', nr, 4, 'census'),
            'combined-wrong-outcome': ('claim-normalization-reviews.tsv', nr, 5, 'amend_content'),
            'combined-static-ca-wrong-event': ('claim-content-amendments.tsv', ca[0] if ca else '', 1, 'UNKNOWN-EVENT'),
            'combined-static-ca-wrong-correction': ('claim-content-amendments.tsv', ca[0] if ca else '', 2, 'CC-UNKNOWN-0001'),
            'combined-static-ca-wrong-claim': ('claim-content-amendments.tsv', ca[0] if ca else '', 3, other),
            'combined-static-ca-wrong-review': ('claim-content-amendments.tsv', ca[0] if ca else '', 7, 'DIFFERENT-REVIEW'),
            'combined-static-nr-wrong-outcome': ('claim-normalization-reviews.tsv', nr, 5, 'amend_content'),
            'combined-static-nr-wrong-scope': ('claim-normalization-reviews.tsv', nr, 4, 'census'),
            'combined-static-nr-open': ('claim-normalization-reviews.tsv', nr, 6, 'open'),
            'combined-static-event-wrong-source': ('correction-events.tsv', event_id, 2, 'OTHER'),
            'combined-frozen-order': ('claims.tsv', x, 2, '000001.0999'),
            'combined-frozen-locator': ('claims.tsv', x, 4, 'synthetic-altered-locator'),
            'combined-source-identity-drift': ('claims.tsv', x, 1, 'OTHER'),
            'combined-source-pin-drift': ('sources.tsv', 'TASAKI2020', 14, 'a' * 40),
            'combined-vocabulary-basis-drift': ('claim-vocabulary-review.tsv', x, 1, 'project_vocabulary'),
            'combined-vocabulary-stale-ref': ('claim-vocabulary-review.tsv', x, 2, record(before, 'claim-vocabulary-review.tsv', x)[2]),
            'combined-unrelated-vocabulary-review': ('claim-vocabulary-review.tsv', other, 2, 'CHANGED-REVIEW'),
            'combined-invariant-review': ('source-invariants.tsv', 'TASAKI2020', 7, 'WRONG-REVIEW'),
        }
        if label in simple:
            change(*simple[label]); return
        if label in ('combined-static-missing-ca', 'combined-missing-ca-integration'):
            remove(after, 'claim-content-amendments.tsv', ca[0])
        elif label == 'combined-static-duplicate-ca':
            append(after, 'claim-content-amendments.tsv', ca.copy())
        elif label in ('combined-static-duplicate-owner-nr', 'combined-duplicate-owner-integration'):
            duplicate_nr()
        elif label in ('combined-static-duplicate-owner-cc', 'combined-static-mixed-owner'):
            row = cc.copy(); row[0] = unused_id(after, 'claim-corrections.tsv', 'CC-DUPLICATE'); row[2] = '2'
            if label.endswith('mixed-owner'):
                row[3], row[5] = duplicate_nr('reclassify'), 'reclassify'
            append(after, 'claim-corrections.tsv', row)
        elif label.startswith('combined-static-ca-owned-'):
            change('claim-corrections.tsv', cc[0], 5, label.removeprefix('combined-static-ca-owned-'))
        elif label.startswith('combined-class-pair-no-op-'):
            for col, value in enumerate(record(before, 'claims.tsv', x)[5:7], 5):
                change('claims.tsv', x, col, value); change('claim-corrections.tsv', cc[0], col + 3, value)
        elif label.startswith('combined-wrong-') and any(s in label for s in ('disposition-', 'subkind-')):
            which = label.removeprefix('combined-wrong-').rsplit('-', 1)[0]
            col, value = {'old-disposition': (6, 'domain'), 'old-subkind': (7, 'lemma'),
                          'new-disposition': (8, 'notation'), 'new-subkind': (9, 'theorem')}[which]
            change('claim-corrections.tsv', cc[0], col, value)
        elif label.startswith('combined-static-') and label.removeprefix('combined-static-') in {
                'none-old-disposition', 'none-old-subkind', 'old-out-of-scope', 'new-out-of-scope',
                'illegal-new-kind', 'illegal-new-subkind'}:
            col, value = {'none-old-disposition': (6, 'NONE'), 'none-old-subkind': (7, 'NONE'),
                          'old-out-of-scope': (6, 'out_of_scope'), 'new-out-of-scope': (8, 'out_of_scope'),
                          'illegal-new-kind': (8, 'unrecognized'), 'illegal-new-subkind': (9, 'unrecognized')
                          }[label.removeprefix('combined-static-')]
            change('claim-corrections.tsv', cc[0], col, value)
        elif label == 'legacy-amend-class-drift-static':
            change('claim-corrections.tsv', cc[0], 8, 'definition')
        elif label == 'legacy-amend-actual-class-drift-helper':
            change('claims.tsv', x, 5, 'definition'); change('claims.tsv', x, 6, 'definition')
        elif label == 'legacy-reclass-content-drift':
            value = 'Synthetic changed pure reclassification content'
            change('claims.tsv', x, 7, value); change('claims.tsv', x, 8, blob(value)); refresh(after)
        elif label in ('combined-static-pending-old', 'combined-static-pending-new', 'combined-static-mismatched-oid-width', 'combined-static-same-manifest-oids'):
            col, value = {'combined-static-pending-old': (4, 'PENDING'), 'combined-static-pending-new': (5, 'PENDING'),
                          'combined-static-mismatched-oid-width': (5, 'a' * 64), 'combined-static-same-manifest-oids': (5, ca[4])}[label]
            ca_change(col, value)
        elif label in ('combined-actual-content-unchanged', 'combined-unchanged-content-integration'):
            change('claims.tsv', x, 7, record(before, 'claims.tsv', x)[7])
        elif label == 'combined-wrong-pending-old-manifest': ca_change(4, 'a' * 40)
        elif label == 'combined-wrong-fixed-old-record':
            mutate(before, 'claims.tsv', x, 8, 'a' * 40); refresh(before)
        elif label == 'combined-wrong-new-manifest': ca_change(5, 'a' * 40)
        elif label in ('combined-wrong-current-new-record', 'combined-pending-current-new-record'):
            change('claims.tsv', x, 8, 'PENDING' if 'pending' in label else 'a' * 40)
        elif label == 'combined-newline-appended-new-hash':
            value = blob(record(after, 'claims.tsv', x)[7] + '\n'); ca_change(5, value); change('claims.tsv', x, 8, value)
        elif label == 'combined-newline-appended-old-hash': ca_change(4, blob(record(before, 'claims.tsv', x)[7] + '\n'))
        elif label.startswith('combined-contentless-'):
            new_content({'empty': '', 'true': 'True.', 'false': 'False'}[label.removeprefix('combined-contentless-')])
        elif label in ('combined-static-wrong-page-pin', 'combined-static-pending-page-pin'):
            ca_change(6, 'PENDING' if 'pending' in label else 'a' * 40)
        elif label == 'combined-base-page-pin-drift':
            mutate(before, 'pages.tsv', record(before, 'claims.tsv', x)[3], 9, 'a' * 40)
        elif label == 'combined-current-page-pin-drift':
            change('pages.tsv', record(after, 'claims.tsv', x)[3], 9, 'a' * 40); ca_change(6, 'a' * 40)
        elif label == 'combined-current-page-record-drift':
            change('pages.tsv', record(after, 'claims.tsv', x)[3], 5, 'synthetic-section')
        elif label in ('combined-unrelated-source-drift', 'combined-independent-second-source-control-t'):
            second_source(before); second_source(after)
            if 'unrelated' in label: change('sources.tsv', 'SRB', 5, 'Changed synthetic title')
        elif label == 'combined-page-identity-drift':
            page_row = next(r for r in table(after, 'pages.tsv')[1:] if r[1] == 'TASAKI2020' and r[0] != record(after, 'claims.tsv', x)[3])
            change('claims.tsv', x, 3, page_row[0]); ca_change(6, page_row[9])
        elif label.startswith(('combined-base-', 'combined-current-')):
            side, what = label.removeprefix('combined-').split('-', 1)
            target = before if side == 'base' else after
            active = {'excluded': (5, 'out_of_scope'), 'tombstoned': (11, 'true'),
                      'exclusion-rationale': (9, 'UNEXPECTED'), 'exclusion-ref': (10, 'UNEXPECTED'),
                      'successor': (12, 'CL-SYNTHETIC-9999'), 'tombstone-rationale': (13, 'UNEXPECTED'), 'tombstone-ref': (14, 'UNEXPECTED')}
            if what in active: mutate(target, 'claims.tsv', x, *active[what])
            elif what in ('skeleton_frozen', 'proof_active'): mutate(target, 'source-progress.tsv', 'TASAKI2020', 1, what)
            elif what.startswith('binding-'): append(target, 'bindings.tsv', binding_row(target, x if what == 'binding-x' else other))
            else:
                name, row = {'slice': ('slices.tsv', ['SL-RUNTIME-0001', '1', x]),
                             'dependency-out': ('dependencies.tsv', [x, 'requires', other, 'NONE']),
                             'dependency-in': ('dependencies.tsv', [other, 'consequence_of', x, 'NONE']),
                             'claim-axiom': ('claim-axioms.tsv', [x, 'AX-PROJECT-0001'])}[what]
                append(target, name, row)
        elif label == 'combined-unknown-frozen-claim': remove(before, 'claims.tsv', x)
        elif label.startswith('combined-new-') and label.endswith('-artifact'):
            name = label.removeprefix('combined-new-').removesuffix('-artifact') + '.tsv'
            values = {'bindings.tsv': ['CL-FOREIGN-9999'] + binding_row(after, other)[1:],
                      'claim-context.tsv': [other, '1', x, 'term_reference', 'inherited', 'FIXTURE'],
                      'statement-modules.tsv': ['LatticeSystem.Claims.Runtime', 'LatticeSystem/Claims/Runtime.lean', 'leaf'],
                      'statement-imports.tsv': ['LatticeSystem.Claims.Runtime', '1', 'Mathlib.Init', 'true', 'false', 'false'],
                      'axioms.tsv': ['AX-PROJECT-9999', 'LatticeSystem.Axioms.State.fixture', 'LatticeSystem.Axioms.State', 'state', 'fixture', 'fixture', 'reopen', 'PENDING']}
            append(after, name, values[name])
        elif label == 'combined-vocabulary-missing-review': remove(after, 'claim-vocabulary-review.tsv', x)
        elif label == 'combined-vocabulary-duplicate-review': append(after, 'claim-vocabulary-review.tsv', record(after, 'claim-vocabulary-review.tsv', x).copy())
        elif label == 'combined-vocabulary-add-use': append(after, 'claim-vocabulary.tsv', [x, table(after, 'vocabulary.tsv')[1][0]])
        elif label in ('combined-vocabulary-remove-use', 'combined-vocabulary-alter-use'):
            uses = table(after, 'claim-vocabulary.tsv'); indices = [i for i,r in enumerate(uses[1:],1) if r[0] == x]
            if 'remove' in label: uses.pop(indices[0])
            else: uses[indices[0]][1] = uses[indices[1]][1]
            write(after, 'claim-vocabulary.tsv', uses)
        elif label == 'combined-vocabulary-declaration-drift':
            change('vocabulary.tsv', table(after, 'vocabulary.tsv')[1][0], table(after, 'vocabulary.tsv')[0].index('design_role'), 'SYNTHETIC-CHANGED')
        elif label.startswith('combined-static-forbidden-'):
            name = label.removeprefix('combined-static-forbidden-') + '.tsv'
            row = ([unused_id(after, name, 'SE-RUNTIME'), event_id, cc[0], x, '1', 'new_successor', other]
                   if name == 'claim-successors.tsv' else
                   [unused_id(after, name, 'IA-RUNTIME'), event_id, cc[0], '1', 'IT-RUNTIME-0001', ref])
            append(after, name, row)
        elif label == 'combined-new-unowned-claim':
            tmp = after.with_name(after.name + '-omission')
            _, _, _, _, fresh, _ = prepare_omission(after, tmp)
            rows = table(after, 'claims.tsv'); fresh_row = record(tmp, 'claims.tsv', fresh)
            index = next(i for i,r in enumerate(rows[1:],1) if r[2] > fresh_row[2])
            rows.insert(index, fresh_row); write(after, 'claims.tsv', rows); refresh(after)
            shutil.rmtree(tmp)
        elif label == 'combined-new-unowned-item':
            tmp = after.with_name(after.name + '-omission'); _, _, _, _, _, fresh = prepare_omission(after, tmp)
            rows = table(after, 'source-items.tsv'); new_row = record(tmp, 'source-items.tsv', fresh)
            index = next(i for i,r in enumerate(rows[1:],1) if r[2] > new_row[2]); rows.insert(index,new_row)
            write(after,'source-items.tsv',rows); shutil.rmtree(tmp)
        elif label == 'combined-existing-item-metadata':
            item = next(r[0] for r in table(after,'item-claims.tsv')[1:] if r[2] == x)
            change('source-items.tsv',item,7,'Synthetic changed locator')
        elif label == 'combined-old-item-relation-delete': remove(after,'item-claims.tsv',x,2)
        elif label == 'combined-new-target-item-relation':
            item = next(r[0] for r in table(after,'item-claims.tsv')[1:] if r[2] == other)
            append(after,'item-claims.tsv',[item,'99',x])
        elif label.startswith('combined-invariant-'):
            col = {'active-count':2,'target-count':3,'equation-count':4,'no-claim-pages':5,'census-oid':6}[label.removeprefix('combined-invariant-')]
            value = 'a'*40 if col == 6 else str(int(record(after,'source-invariants.tsv','TASAKI2020')[col])+1)
            change('source-invariants.tsv','TASAKI2020',col,value)
        elif label == 'history-later-lifecycle-static-only-s': change('source-progress.tsv','TASAKI2020',1,'skeleton_frozen')
        elif label == 'history-stale-next-old-oid': ca_change(4, next(r[4] for r in table(after,'claim-content-amendments.tsv')[1:] if r[3] == x))
        elif label == 'history-second-event-wrong-old-class':
            change('claim-corrections.tsv',cc[0],6,'domain'); change('claim-corrections.tsv',cc[0],7,'domain')
        elif label == 'history-same-event-second-owner':
            previous = next(r for r in table(after,'claim-content-amendments.tsv')[1:] if r[3] == x and r[1] != event_id)
            old_event = previous[1]; old_ref = record(after,'correction-events.tsv',old_event)[4]
            for name, identifier in [('claim-normalization-reviews.tsv',nr),('claim-corrections.tsv',cc[0])]:
                change(name,identifier,1,old_event); change(name,identifier,2,'2')
            change('claim-normalization-reviews.tsv',nr,8,old_ref); ca_change(1,old_event); ca_change(7,old_ref)
        elif label == 'history-foreign-new-ca-event':
            tmp=after.with_name(after.name+'-foreign'); content_event(after,tmp,other)
            for name in history_tables:
                (after/'registry'/name).write_bytes((tmp/'registry'/name).read_bytes())
            # Static ownership uses the current claim and unchanged source page.
            for name in ('claims.tsv','claim-vocabulary-review.tsv','source-invariants.tsv'):
                (after/'registry'/name).write_bytes((tmp/'registry'/name).read_bytes())
            shutil.rmtree(tmp)
        elif label.startswith('history-prefix-reorder-') or label == 'history-helper-ca-prefix-reorder':
            name = ('claim-content-amendments.tsv' if label == 'history-helper-ca-prefix-reorder' else label.removeprefix('history-prefix-reorder-')+'.tsv')
            rows=table(after,name); key=2 if name=='claim-successors.tsv' else 1
            groups=[]
            for row in rows[1:]:
                if not groups or groups[-1][0][key] != row[key]: groups.append([])
                groups[-1].append(row)
            assert len(groups)>=2
            groups[0],groups[1]=groups[1],groups[0]
            write(after,name,[rows[0]]+[row for group in groups for row in group])
        elif label == 'history-event-physical-reorder':
            rows=table(after,'correction-events.tsv');rows[1],rows[2]=rows[2],rows[1];write(after,'correction-events.tsv',rows)
        elif label.startswith('history-old-value-'):
            name=label.removeprefix('history-old-value-')+'.tsv';row=table(after,name)[1]
            col, value={'correction-events.tsv':(4,'CHANGED-REVIEW'),
                'claim-normalization-reviews.tsv':(7,'exact-statement-ready-RUNTIME-HISTORY-MUTANT'),
                'claim-corrections.tsv':(9,'lemma'), 'claim-successors.tsv':(6,other),
                'source-item-additions.tsv':(5,'CORPUS-NORMALIZATION-INDEPENDENT-REVIEW-RUNTIME-HISTORY-MUTANT'),
                'claim-content-amendments.tsv':(7,'SOURCE-FIDELITY-TASAKI2020-0478-INDEPENDENT-REVIEW-V1-RUNTIME-HISTORY-MUTANT')}[name]
            frozen = {
                'claim-normalization-reviews.tsv': ('NR-TASAKI2020-0001', 'exact-statement-ready'),
                'claim-corrections.tsv': ('CC-TASAKI2020-0001', 'remark'),
                'source-item-additions.tsv': ('IA-TASAKI2020-0001', 'CORPUS-NORMALIZATION-INDEPENDENT-REVIEW'),
                'claim-content-amendments.tsv': ('CA-TASAKI2020-0001', 'SOURCE-FIDELITY-TASAKI2020-0478-INDEPENDENT-REVIEW-V1')}
            if name in frozen:
                assert (row[0], row[col]) == frozen[name]
            assert row[col] != value
            change(name,row[0],col,value)
        elif label == 'combined-ordinary-rejects-full-diff': pass
        elif label in ('history-reopen-old-event-class-content','selector-real-historical-reopen'):
            change('claims.tsv',x,5,'notation');change('claims.tsv',x,6,'notation')
            value='Synthetic historical reopen';change('claims.tsv',x,7,value);change('claims.tsv',x,8,blob(value));refresh(after)
        elif label == 'history-ordinary-ca-piggyback':
            row=ca.copy();row[0]=unused_id(after,'claim-content-amendments.tsv','CA-PIGGYBACK');append(after,'claim-content-amendments.tsv',row)
        elif label == 'none-old-combined-static':
            change('claim-corrections.tsv',cc[0],6,'NONE');change('claim-corrections.tsv',cc[0],7,'NONE')
        else: raise AssertionError('unimplemented mutant '+label)

    combined_cases = [
        ('combined-fixed-s', 'F', 'S', True, 'check-content-amendments: ok'),
        ('combined-fixed-h', 'F', 'H', True, 'check-content-amendments: ok'),
        ('combined-fixed-t', 'F', 'T', True, 'check-claim-corrections: ok'),
        ('combined-fixed-b', 'F', 'B', True, 'check-base-diff: ok'),
        ('combined-fixed-c', 'F', 'C', True, 'check-registry: ok'),
        ('combined-pending-h', 'P', 'H', True, 'check-content-amendments: ok'),
        ('combined-pending-t', 'P', 'T', True, 'check-claim-corrections: ok'),
        ('combined-pending-b', 'P', 'B', True, 'check-base-diff: ok'),
        ('combined-disposition-only-h', 'D', 'H', True, 'check-content-amendments: ok'),
        ('combined-disposition-only-t', 'D', 'T', True, 'check-claim-corrections: ok'),
        ('combined-subkind-only-h', 'K', 'H', True, 'check-content-amendments: ok'),
        ('combined-subkind-only-t', 'K', 'T', True, 'check-claim-corrections: ok'),
        ('combined-project-vocabulary-h', 'V', 'H', True, 'check-content-amendments: ok'),
        ('combined-project-vocabulary-t', 'V', 'T', True, 'check-claim-corrections: ok'),
        ('combined-legacy-no-ca-header-s', 'N', 'S', True, 'check-content-amendments: ok'),
        ('combined-legacy-no-ca-header-h', 'N', 'H', True, 'check-content-amendments: ok'),
        ('combined-legacy-no-ca-header-t', 'N', 'T', True, 'check-claim-corrections: ok'),
        ('combined-independent-omission-nested-insert-h', 'M', 'H', True, 'check-content-amendments: ok'),
        ('combined-independent-omission-nested-insert-t', 'M', 'T', True, 'check-claim-corrections: ok'),
        ('combined-independent-omission-nested-insert-b', 'M', 'B', True, 'check-base-diff: ok'),
        ('combined-independent-omission-nested-insert-i', 'M', 'I', True, 'check-source-items: ok'),
        ('combined-target-vocab-row-order-preserved-set-h', 'W', 'H', True, 'check-content-amendments: ok'),
        ('combined-target-vocab-row-order-preserved-set-t', 'W', 'T', True, 'check-claim-corrections: ok'),
        ('combined-unknown-outcome', 'F', 'T', False, 'invalid claim normalization review ledger'),
        ('combined-unknown-action', 'F', 'T', False, 'invalid claim correction ledger'),
        ('combined-open-review', 'F', 'T', False, 'invalid claim normalization review ledger'),
        ('combined-wrong-scope', 'F', 'T', False, 'invalid claim normalization review ledger'),
        ('combined-wrong-outcome', 'F', 'T', False, 'invalid claim correction ledger'),
        ('combined-static-missing-ca', 'F', 'S', False, 'content amendment is missing its provenance row'),
        ('combined-static-duplicate-ca', 'F', 'S', False, 'duplicate content amendment'),
        ('combined-static-duplicate-owner-nr', 'F', 'S', False, 'combined correction lacks exactly one owning review and correction'),
        ('combined-static-duplicate-owner-cc', 'F', 'S', False, 'combined correction lacks exactly one owning review and correction'),
        ('combined-static-mixed-owner', 'F', 'S', False, 'combined correction lacks exactly one owning review and correction'),
        ('combined-static-ca-wrong-event', 'F', 'S', False, 'content amendment event or correction ownership mismatch'),
        ('combined-static-ca-wrong-correction', 'F', 'S', False, 'content amendment event or correction ownership mismatch'),
        ('combined-static-ca-wrong-claim', 'F', 'S', False, 'content amendment event or correction ownership mismatch'),
        ('combined-static-ca-wrong-review', 'F', 'S', False, 'content amendment review ownership mismatch'),
        ('combined-static-nr-wrong-outcome', 'F', 'S', False, 'content amendment review ownership mismatch'),
        ('combined-static-nr-wrong-scope', 'F', 'S', False, 'content amendment review ownership mismatch'),
        ('combined-static-nr-open', 'F', 'S', False, 'content amendment review ownership mismatch'),
        ('combined-static-event-wrong-source', 'F', 'S', False, 'content amendment source mismatch'),
        ('combined-static-ca-owned-reclassify', 'F', 'S', False, 'content amendment event or correction ownership mismatch'),
        ('combined-static-ca-owned-split', 'F', 'S', False, 'content amendment event or correction ownership mismatch'),
        ('combined-static-ca-owned-add_omitted_claim', 'F', 'S', False, 'content amendment event or correction ownership mismatch'),
        ('combined-duplicate-owner-integration', 'F', 'T', False, 'invalid claim normalization review ledger'),
        ('combined-missing-ca-integration', 'F', 'T', False, 'content amendment is missing its provenance row'),
        ('combined-class-pair-no-op-s', 'F', 'S', False, 'combined correction requires changed classification'),
        ('combined-class-pair-no-op-h', 'F', 'H', False, 'combined correction requires changed classification'),
        ('combined-wrong-old-disposition-h', 'F', 'H', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-old-disposition-t', 'F', 'T', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-old-subkind-h', 'F', 'H', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-old-subkind-t', 'F', 'T', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-new-disposition-h', 'F', 'H', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-new-disposition-t', 'F', 'T', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-new-subkind-h', 'F', 'H', False, 'combined correction classification does not match claim transition'),
        ('combined-wrong-new-subkind-t', 'F', 'T', False, 'combined correction classification does not match claim transition'),
        ('combined-static-none-old-disposition', 'F', 'S', False, 'combined correction has invalid classification'),
        ('combined-static-none-old-subkind', 'F', 'S', False, 'combined correction has invalid classification'),
        ('combined-static-old-out-of-scope', 'F', 'S', False, 'combined correction has invalid classification'),
        ('combined-static-new-out-of-scope', 'F', 'S', False, 'combined correction has invalid classification'),
        ('combined-static-illegal-new-kind', 'F', 'S', False, 'combined correction has invalid classification'),
        ('combined-static-illegal-new-subkind', 'F', 'S', False, 'combined correction has invalid classification'),
        ('legacy-amend-class-drift-static', 'A', 'S', False, 'content amendment changes classification'),
        ('legacy-amend-actual-class-drift-helper', 'A', 'H', False, 'content amendment changed frozen claim identity or metadata'),
        ('legacy-reclass-content-drift', 'Q', 'T', False, 'unmanifested claim drift'),
        ('combined-static-pending-old', 'F', 'S', False, 'content amendment requires frozen old and new content OIDs'),
        ('combined-static-pending-new', 'F', 'S', False, 'content amendment requires frozen old and new content OIDs'),
        ('combined-static-mismatched-oid-width', 'F', 'S', False, 'content amendment requires frozen old and new content OIDs'),
        ('combined-static-same-manifest-oids', 'F', 'S', False, 'content amendment is a no-op'),
        ('combined-actual-content-unchanged', 'F', 'H', False, 'content amendment is a no-op'),
        ('combined-wrong-pending-old-manifest', 'P', 'H', False, 'content amendment old content OID is stale'),
        ('combined-wrong-fixed-old-record', 'F', 'H', False, 'content amendment old content OID is stale'),
        ('combined-wrong-new-manifest', 'F', 'H', False, 'content amendment new content OID is stale'),
        ('combined-wrong-current-new-record', 'F', 'H', False, 'content amendment new content OID is stale'),
        ('combined-pending-current-new-record', 'F', 'H', False, 'content amendment new content OID is stale'),
        ('combined-newline-appended-new-hash', 'F', 'H', False, 'content amendment new content OID is stale'),
        ('combined-newline-appended-old-hash', 'P', 'H', False, 'content amendment old content OID is stale'),
        ('combined-contentless-empty', 'F', 'H', False, 'contentless content amendment surrogate'),
        ('combined-contentless-true', 'F', 'H', False, 'contentless content amendment surrogate'),
        ('combined-contentless-false', 'F', 'H', False, 'contentless content amendment surrogate'),
        ('combined-unchanged-content-integration', 'F', 'T', False, 'content amendment is a no-op'),
        ('combined-static-wrong-page-pin', 'F', 'S', False, 'content amendment page source mismatch'),
        ('combined-static-pending-page-pin', 'F', 'S', False, 'content amendment page source mismatch'),
        ('combined-base-page-pin-drift', 'F', 'H', False, 'content amendment page source mismatch'),
        ('combined-current-page-pin-drift', 'F', 'H', False, 'content amendment page source mismatch'),
        ('combined-current-page-record-drift', 'F', 'H', False, 'combined correction page record changed'),
        ('combined-source-pin-drift', 'F', 'H', False, 'combined correction source record changed or is not frozen'),
        ('combined-unrelated-source-drift', 'F', 'T', False, 'unrelated frozen registry drift'),
        ('combined-independent-second-source-control-t', 'F', 'T', True, 'check-claim-corrections: ok'),
        ('combined-frozen-order', 'F', 'H', False, 'combined correction changed frozen claim identity or metadata'),
        ('combined-frozen-locator', 'F', 'H', False, 'combined correction changed frozen claim identity or metadata'),
        ('combined-source-identity-drift', 'F', 'H', False, 'content amendment source mismatch'),
        ('combined-page-identity-drift', 'F', 'H', False, 'combined correction changed frozen claim identity or metadata'),
        ('combined-base-excluded', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-base-tombstoned', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-base-exclusion-rationale', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-base-exclusion-ref', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-base-successor', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-base-tombstone-rationale', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-base-tombstone-ref', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-excluded', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-tombstoned', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-exclusion-rationale', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-exclusion-ref', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-successor', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-tombstone-rationale', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-current-tombstone-ref', 'F', 'H', False, 'combined correction requires an active formalization target'),
        ('combined-unknown-frozen-claim', 'F', 'H', False, 'content amendment does not target a frozen source claim'),
        ('combined-base-skeleton_frozen', 'F', 'H', False, 'content amendment requires a pre-R4 source'),
        ('combined-base-proof_active', 'F', 'H', False, 'content amendment requires a pre-R4 source'),
        ('combined-base-binding-x', 'F', 'H', False, 'content amendment source already has bindings'),
        ('combined-base-binding-other_same_source', 'F', 'H', False, 'content amendment source already has bindings'),
        ('combined-base-slice', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-base-dependency-out', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-base-dependency-in', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-base-claim-axiom', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-current-skeleton_frozen', 'F', 'H', False, 'content amendment requires a pre-R4 source'),
        ('combined-current-proof_active', 'F', 'H', False, 'content amendment requires a pre-R4 source'),
        ('combined-current-binding-x', 'F', 'H', False, 'content amendment source already has bindings'),
        ('combined-current-binding-other_same_source', 'F', 'H', False, 'content amendment source already has bindings'),
        ('combined-current-slice', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-current-dependency-out', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-current-dependency-in', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-current-claim-axiom', 'F', 'H', False, 'content amendment target already has skeleton or axiom relations'),
        ('combined-new-bindings-artifact', 'F', 'T', False, 'correction event introduces an R4 artifact'),
        ('combined-new-claim-context-artifact', 'F', 'T', False, 'correction event introduces an R4 artifact'),
        ('combined-new-statement-modules-artifact', 'F', 'T', False, 'correction event introduces an R4 artifact'),
        ('combined-new-statement-imports-artifact', 'F', 'T', False, 'correction event introduces an R4 artifact'),
        ('combined-new-axioms-artifact', 'F', 'T', False, 'correction event introduces an axiom artifact'),
        ('combined-vocabulary-basis-drift', 'F', 'H', False, 'content amendment lacks its refreshed vocabulary review'),
        ('combined-vocabulary-stale-ref', 'F', 'H', False, 'content amendment lacks its refreshed vocabulary review'),
        ('combined-vocabulary-missing-review', 'F', 'H', False, 'content amendment lacks its refreshed vocabulary review'),
        ('combined-vocabulary-duplicate-review', 'F', 'H', False, 'content amendment lacks its refreshed vocabulary review'),
        ('combined-vocabulary-add-use', 'F', 'H', False, 'content amendment changed vocabulary use'),
        ('combined-vocabulary-remove-use', 'V', 'H', False, 'content amendment changed vocabulary use'),
        ('combined-vocabulary-alter-use', 'V', 'H', False, 'content amendment changed vocabulary use'),
        ('combined-unrelated-vocabulary-review', 'F', 'T', False, 'unrelated vocabulary review drift'),
        ('combined-vocabulary-declaration-drift', 'F', 'T', False, 'unrelated frozen registry drift'),
        ('combined-static-forbidden-claim-successors', 'F', 'S', False, 'content amendment cannot introduce successors or source items'),
        ('combined-static-forbidden-source-item-additions', 'F', 'S', False, 'content amendment cannot introduce successors or source items'),
        ('combined-new-unowned-claim', 'F', 'T', False, 'split successor provenance is incomplete'),
        ('combined-new-unowned-item', 'F', 'T', False, 'unmanifested source item addition'),
        ('combined-existing-item-metadata', 'F', 'T', False, 'historical source item drift'),
        ('combined-old-item-relation-delete', 'F', 'T', False, 'historical source item relation drift'),
        ('combined-new-target-item-relation', 'F', 'T', False, 'unrelated item-claim drift'),
        ('combined-invariant-active-count', 'F', 'T', False, 'census invariant count is stale'),
        ('combined-invariant-target-count', 'F', 'T', False, 'formalization target count is stale'),
        ('combined-invariant-equation-count', 'F', 'T', False, 'census invariant count is stale'),
        ('combined-invariant-no-claim-pages', 'F', 'T', False, 'census invariant count is stale'),
        ('combined-invariant-census-oid', 'F', 'T', False, 'census OID is stale'),
        ('combined-invariant-review', 'F', 'H', False, 'combined correction lacks its event invariant review'),
        ('history-combined-then-combined-t', 'CC', 'T', True, 'check-claim-corrections: ok'),
        ('history-combined-then-combined-b', 'CC', 'B', True, 'check-base-diff: ok'),
        ('history-combined-then-combined-s', 'CC', 'S', True, 'check-content-amendments: ok'),
        ('history-combined-then-combined-o', 'CC', 'O', True, 'check-base-diff: ok'),
        ('history-combined-then-amend-t', 'CA', 'T', True, 'check-claim-corrections: ok'),
        ('history-combined-then-amend-b', 'CA', 'B', True, 'check-base-diff: ok'),
        ('history-combined-then-amend-s', 'CA', 'S', True, 'check-content-amendments: ok'),
        ('history-combined-then-amend-o', 'CA', 'O', True, 'check-base-diff: ok'),
        ('history-amend-then-combined-t', 'AC', 'T', True, 'check-claim-corrections: ok'),
        ('history-amend-then-combined-b', 'AC', 'B', True, 'check-base-diff: ok'),
        ('history-amend-then-combined-s', 'AC', 'S', True, 'check-content-amendments: ok'),
        ('history-amend-then-combined-o', 'AC', 'O', True, 'check-base-diff: ok'),
        ('history-combined-reclass-amend-t', 'CRAC', 'T', True, 'check-claim-corrections: ok'),
        ('history-combined-reclass-amend-b', 'CRAC', 'B', True, 'check-base-diff: ok'),
        ('history-combined-reclass-amend-s', 'CRAC', 'S', True, 'check-content-amendments: ok'),
        ('history-combined-reclass-amend-o', 'CRAC', 'O', True, 'check-base-diff: ok'),
        ('history-omission-then-combined-t', 'OC', 'T', True, 'check-claim-corrections: ok'),
        ('history-omission-then-combined-b', 'OC', 'B', True, 'check-base-diff: ok'),
        ('history-omission-then-combined-s', 'OC', 'S', True, 'check-content-amendments: ok'),
        ('history-omission-then-combined-o', 'OC', 'O', True, 'check-base-diff: ok'),
        ('history-combined-then-split-t', 'CS', 'T', True, 'check-claim-corrections: ok'),
        ('history-combined-then-split-b', 'CS', 'B', True, 'check-base-diff: ok'),
        ('history-combined-then-split-s', 'CS', 'S', True, 'check-content-amendments: ok'),
        ('history-combined-then-split-o', 'CS', 'O', True, 'check-base-diff: ok'),
        ('history-combined-then-exclude-t', 'CX', 'T', True, 'check-claim-corrections: ok'),
        ('history-combined-then-exclude-b', 'CX', 'B', True, 'check-base-diff: ok'),
        ('history-combined-then-exclude-s', 'CX', 'S', True, 'check-content-amendments: ok'),
        ('history-combined-then-exclude-o', 'CX', 'O', True, 'check-base-diff: ok'),
        ('history-intervening-pure-reclassification-t', 'CRAC', 'T', True, 'check-claim-corrections: ok'),
        ('history-later-lifecycle-static-only-s', 'CC', 'S', True, 'check-content-amendments: ok'),
        ('history-stale-next-old-oid', 'CC', 'S', False, 'content amendment history chain is stale'),
        ('history-second-event-wrong-old-class', 'CC', 'H', False, 'combined correction classification does not match claim transition'),
        ('history-same-event-second-owner', 'CC', 'S', False, 'combined correction lacks exactly one owning review and correction'),
        ('history-foreign-new-ca-event', 'F', 'H', False, 'content amendment belongs to another event'),
        ('history-prefix-reorder-claim-normalization-reviews', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-prefix-reorder-claim-corrections', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-prefix-reorder-claim-successors', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-prefix-reorder-source-item-additions', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-prefix-reorder-claim-content-amendments', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-event-physical-reorder', 'HIST', 'T', False, 'invalid correction event ledger'),
        ('history-helper-ca-prefix-reorder', 'HIST', 'H', False, 'historical content amendment drift'),
        ('history-old-value-correction-events', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-old-value-claim-normalization-reviews', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-old-value-claim-corrections', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-old-value-claim-successors', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('history-old-value-source-item-additions', 'HIST', 'T', False, 'unmanifested source item addition'),
        ('history-old-value-claim-content-amendments', 'HIST', 'T', False, 'historical correction ledger drift'),
        ('combined-ordinary-rejects-full-diff', 'F', 'O', False, 'identity/order/locator/content/exclusion/supersession'),
        ('history-reopen-old-event-class-content', 'CC', 'E', False, 'identity/order/locator/content/exclusion/supersession'),
        ('history-ordinary-ca-piggyback', 'CC', 'O', False, 'historical correction ledger drift'),
        ('selector-real-first-combined', 'J', 'R', True, 'check-base-diff: ok'),
        ('selector-real-second-combined', 'J', 'R', True, 'check-base-diff: ok'),
        ('selector-real-historical-ordinary', 'J', 'R', True, 'check-base-diff: ok'),
        ('selector-real-wrong-base', 'J', 'R', False, 'new correction event base commit does not match the actual merge base'),
        ('selector-real-two-new-events', 'J', 'R', False, 'multiple new correction events require an explicit CI policy change'),
        ('selector-real-invalid-base', 'J', 'R', False, 'invalid or unfetched base ref'),
        ('selector-real-class-fact-mutant', 'J', 'R', False, 'combined correction classification does not match claim transition'),
        ('selector-real-historical-reopen', 'J', 'R', False, 'identity/order/locator/content/exclusion/supersession'),
        ('none-old-combined-static', 'F', 'S', False, 'combined correction has invalid classification'),
        ('none-old-combined-new-id-transition', 'F', 'T', False, 'correction predecessor source mismatch'),
        ('combined-generator-privacy', 'PUBLIC', 'G', True, 'combined generator privacy contract: ok'),
    ]
    def run_selector(label, expected, diagnostic):
        # Registry-only Git graph composes the actual selector and guards. There
        # is deliberately no CHECK_BASE_DIFF override or substitute executable.
        assert 'CHECK_BASE_DIFF' not in os.environ
        with tempfile.TemporaryDirectory(prefix='selector-real-', dir=root) as directory:
            repo = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.STDOUT).decode().strip()
            git('init', '-q')
            git('config', 'user.name', 'phasetr')
            git('config', 'user.email', 'phasetr@gmail.com')
            git('commit', '--allow-empty', '-qm', 'Synthetic selector seed')
            seed = git('rev-parse', 'HEAD')
            fbase = fixture('F')[0]
            shutil.copytree(fbase / 'registry', repo / 'registry')
            git('add', 'registry'); git('commit', '-qm', 'Synthetic selector base')
            b0 = git('rev-parse', 'HEAD')
            b0_snapshot = repo.with_name(repo.name + '-b0')
            shutil.copytree(repo / 'registry', b0_snapshot / 'registry')
            e1 = repo.with_name(repo.name + '-e1')
            e1_event = content_event(b0_snapshot, e1, claim, ['definition', 'definition'])
            mutate(e1, 'correction-events.tsv', e1_event, 3, b0)
            shutil.copytree(e1 / 'registry', repo / 'registry', dirs_exist_ok=True)
            base_ref = b0
            if label in ('selector-real-second-combined', 'selector-real-historical-ordinary',
                         'selector-real-two-new-events', 'selector-real-historical-reopen'):
                assert_content_step(b0_snapshot, e1, e1_event)
                git('add', 'registry'); git('commit', '-qm', 'Synthetic first combined event')
                e1_sha = git('rev-parse', 'HEAD')
                e2 = repo.with_name(repo.name + '-e2')
                e2_event = content_event(e1, e2, claim, ['assertion', 'equation'])
                mutate(e2, 'correction-events.tsv', e2_event, 3, e1_sha)
                shutil.copytree(e2 / 'registry', repo / 'registry', dirs_exist_ok=True)
                assert_content_step(e1, e2, e2_event)
                base_ref = e1_sha
                if label == 'selector-real-two-new-events': base_ref = b0
                if label in ('selector-real-historical-ordinary', 'selector-real-historical-reopen'):
                    git('add', 'registry'); git('commit', '-qm', 'Synthetic second combined event')
                    base_ref = git('rev-parse', 'HEAD')
                    if label.endswith('reopen'):
                        mutate_combined(label, e2, repo, e2_event, claim)
            else:
                if label == 'selector-real-wrong-base': mutate(repo, 'correction-events.tsv', e1_event, 3, seed)
                elif label == 'selector-real-invalid-base': base_ref = 'refs/heads/does-not-exist'
                elif label == 'selector-real-class-fact-mutant':
                    cc = next(r for r in table(repo,'claim-corrections.tsv')[1:] if r[1] == e1_event)
                    mutate(repo,'claim-corrections.tsv',cc[0],6,'domain')
                else: assert_content_step(b0_snapshot, repo, e1_event)
            output = expect(label, expected,
                            [str(project/'scripts/check-base-diff-ci.sh'), str(repo), base_ref], diagnostic)
            if expected:
                assert 'check-base-diff: ok' in output
                assert ('check-base-diff-ci: ok' in output) == (label != 'selector-real-historical-ordinary')
            for suffix in ('-b0','-e1','-e2'):
                path = repo.with_name(repo.name + suffix)
                if path.exists(): shutil.rmtree(path)

    assert len(combined_cases) == len({c[0] for c in combined_cases}) == 212
    assert sum(c[3] for c in combined_cases) == 58
    for label, kind, route, expected, diagnostic in combined_cases:
        if route == 'R':
            run_selector(label, expected, diagnostic)
            continue
        source_kind = 'F' if kind == 'PUBLIC' else kind
        source_before, source_after, event_id, x = fixture(source_kind)
        if label == 'history-intervening-pure-reclassification-t':
            source_before, source_after, event_id, x = fixture_cache['CRAC-middle']
        with tempfile.TemporaryDirectory(prefix='combined-case-', dir=root) as directory:
            case_root = Path(directory)
            before, after = case_root/'base', case_root/'current'
            if route in ('O','E') and label != 'combined-ordinary-rejects-full-diff':
                source_before = source_after
            shutil.copytree(source_before, before)
            shutil.copytree(source_after, after)
            if label == 'none-old-combined-new-id-transition':
                shutil.rmtree(after)
                event_id, ref, nr, cc, x, _ = prepare_omission(before, after)
                mutate(after,'claim-normalization-reviews.tsv',nr,5,'amend_and_reclassify')
                mutate(after,'claim-corrections.tsv',cc,5,'amend_and_reclassify')
                row=record(after,'claims.tsv',x)
                append(after,'claim-content-amendments.tsv',[
                    unused_id(after,'claim-content-amendments.tsv','CA-RUNTIME'),event_id,cc,x,
                    blob('Synthetic prior bytes'),row[8],record(after,'pages.tsv',row[3])[9],ref])
            elif not expected or label in ('combined-independent-second-source-control-t','history-later-lifecycle-static-only-s'):
                mutate_combined(label,before,after,event_id,x)
            if expected and route not in ('O', 'G') and label != 'history-later-lifecycle-static-only-s':
                assert_content_step(before,after,event_id)
            if route == 'G':
                data = generator.load_registry(after)
                catalog = generator.public_catalog(data)
                outputs = generator.build_outputs(catalog)
                item_id = next(r[0] for r in table(after,'item-claims.tsv')[1:] if r[2] == x)
                item = next(i for i in catalog['items'] if i['item_id'] == item_id)
                rendered = next(c for c in item['claims'] if c['claim_id'] == x)
                assert rendered['disposition'] == 'definition' and rendered['subkind'] == 'definition'
                original_item=record(before,'source-items.tsv',item_id)
                assert item['public_group'] == original_item[8] and item['public_slug'] == original_item[9]
                assert table(before,'source-items.tsv') == table(after,'source-items.tsv')
                assert table(before,'item-claims.tsv') == table(after,'item-claims.tsv')
                public_text=json.dumps(catalog,ensure_ascii=False)+''.join(outputs.values())
                row=record(after,'claims.tsv',x)
                cc=next(r for r in table(after,'claim-corrections.tsv')[1:] if r[1] == event_id)
                ca=next(r for r in table(after,'claim-content-amendments.tsv')[1:] if r[2] == cc[0])
                for private in ('PRIVATE-COMBINED',record(before,'claims.tsv',x)[7],row[7],
                                ca[4],ca[5],event_id,cc[0],cc[3],ca[0],ca[7]):
                    assert private not in public_text, private
                generator.write_outputs(after,outputs)
                assert generator.check_outputs(after,outputs,quiet=True)
                assert_content_step(before,after,event_id)
                print(diagnostic)
                count += 1; accepted += 1
                continue
            commands = {
                'S':['python3',helper,'--static',str(after)],
                'H':['python3',helper,'--transition',str(before),str(after),event_id],
                'T':[corrections_checker,'--fixture-dirs',str(before),str(after)],
                'B':[base_checker,'--correction-event',event_id,'--fixture-dirs',str(before),str(after)],
                'O':[base_checker,'--fixture-dirs',str(before),str(after)],
                'E':[base_checker,'--correction-event',event_id,'--fixture-dirs',str(before),str(after)],
                'C':[str(project/'scripts/check-registry.sh'),str(after)],
                'I':[str(project/'scripts/check-source-items.sh'),str(after)]}
            expect(label,expected,commands[route],diagnostic)
    assert (count-combined_start[0],accepted-combined_start[1],rejected-combined_start[2]) == (212,58,154)
    print('test-content-amendments-runtime: combined cases 212 (58 positive, 154 rejection; 3 real selector positive chains)')
    print('test-content-amendments-runtime: ok (' + str(count) + ' cases; ' +
          str(accepted) + ' positive, ' + str(rejected) + ' rejection cases)')
PY
