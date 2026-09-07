---
layout: page
title: "Parked documentation-hygiene decisions"
permalink: /limitations/documentation-hygiene-parked/
---

# Parked documentation-hygiene decisions

This page is the record of documentation-hygiene populations this repository has decided not to
act on. Each entry states what is parked, the command that measures it on tracked paths at a
pinned revision, why it is not being fixed, the condition that reopens it, and how often the
measurement is retaken. A state diagnosis that encounters one of these populations reads the entry
first and does not record it as an unresolved defect.

An entry records a decision, not a claim that the population is harmless in general. Reopening one
requires its stated condition to hold; observing that the population still exists is not itself a
reason to reopen.

## Issue and pull-request identifiers in Lean doc comments

**Target.** Tracker identifiers embedded in module and declaration doc comments under
`LatticeSystem/`, against the convention that comments carry only non-obvious reasons and no task
identifiers.

**Measurement.** Four digits or more, which excludes the book's equation and problem numbers:

```
git grep -o -E '#[0-9]{4,}' 080ebac2 -- 'LatticeSystem/**/*.lean' | wc -l
git grep -n -E '#[0-9]{4,}' 080ebac2 -- 'LatticeSystem/**/*.lean' | wc -l
git grep -l -E '#[0-9]{4,}' 080ebac2 -- 'LatticeSystem/**/*.lean' | wc -l
```

At revision `080ebac2`: 1250 occurrences on 1128 lines across 530 files.

**Reason.** A single sweep edits 530 modules at once, so every one of them and every downstream
importer is rebuilt. The rebuild is the dominant cost and it buys no change to any statement,
proof, or published claim, which puts the sweep off the critical path of the book-order
formalization. The population is also not uniformly mechanical: some four-digit references are
internal cross-reference labels rather than tracker numbers, so a blind pattern edit would corrupt
meaning.

**Fix on touch.** A change that touches a module's doc comments for any other reason removes the
identifiers in that module, in the same commit. No separate sweep is opened for the remainder.

**Reopen condition.** Fix-on-touch brings the occurrence count below roughly one hundred, so that
one closing sweep is reviewable as a single diff; or a linter that rejects the pattern is adopted,
which makes the convention enforceable rather than aspirational.

**Cadence.** Re-measure with the commands above at every twenty-pull-request refactor cycle and
replace the figures here with the new ones.

## Proof-route names in the Marshall–Lieb–Mattis proof tree

**Target.** Names of proof routes in the Marshall–Lieb–Mattis and Theorem 2.3 tree — "ladder
route", "Perron–Frobenius route", "sublattice route" and the rest of that family — in Lean module
documentation, published pages, and the proof guide.

**Measurement.** The name is written with an en dash, so the pattern accepts the en dash as well as
the hyphen; a hyphen-only pattern reports a small spelling-dependent subset instead of the family:

```
git grep -noiE '(ladder|sublattice|perron[-–]+frobenius|PF|MLM|saturated[- ]ladder|N[ée]el)[- ]route' 080ebac2 -- '*.lean' '*.md' '*.tex' | wc -l
```

At revision `080ebac2`: 44 phrases.

**Reason.** These phrases name the mathematical strategy a declaration follows — the `sl₂` ladder,
the Perron–Frobenius argument, the sublattice decomposition — and in one case the boundary of a
hypothesis. They are technical content and are correct as written, so there is no defect here to
fix.

**Reopen condition.** A phrase in this family is found to name a review or workflow step rather
than a mathematical argument. That is a defect and is rewritten when found rather than parked.

**Cadence.** None. The command is kept so that a later diagnosis can confirm the family is
unchanged rather than re-derive the classification.

## References to retired audit tooling

**Target.** Prose under `LatticeSystem/`, `docs/` and `tex/` that names the audit-gate tooling
retired when the hard-check infrastructure was abolished: `audit_gate.py`, `audit-helpers.sh`, the
`capstones.txt` allowlist, the `docs_names.py` registry that backed the dead-declaration sweep, and
the pre-push hook that ran them. A sentence naming a mechanism that no longer exists cannot be
current documentation of anything, so a surviving mention would be a defect rather than a
population to weigh.

**Measurement.** One pattern covers every retired name:

```
git grep -niE 'audit_gate|audit-helpers|capstones\.txt|docs_names\.py|pre-push' 080ebac2 -- '*.lean' '*.md' '*.tex' | wc -l
```

At revision `080ebac2`: 0.

**Disposition.** Resolved by measurement. The population is empty, so nothing is parked here, and a
reopen condition would have nothing to reopen. The entry is kept because what settles the question
is the measurement rather than an argument: a later diagnosis re-runs the command instead of
re-deriving the classification. A mention that appears afterwards is a defect and is removed when
found rather than parked.

**Not tracked here.** The same revision carries 23 references to the live checker:

```
git grep -niE 'check_docs_hierarchy\.py' 080ebac2 -- '*.lean' '*.md' '*.tex' | wc -l
```

That script exists and enforces exactly the constraint each surrounding sentence describes, so
naming it is current documentation of the page it governs. Those 23 lines are neither a defect nor
a parked population, and this page does not track them.

**Cadence.** Re-measure the first command at every twenty-pull-request refactor cycle.

## Frozen historical text in migrated pages

**Target.** Sentences held inside `legacy-source` blocks or inside a `legacy-detail` long record
on migrated pages, together with the version-1 catalogue wording and the interim-authority anchor
inside the `legacy-source:217:228` block of `docs/formalization/legacy/index.md`.

**Measurement.** List the frozen spans on a page and compare a candidate line number against them:

```
git grep -n 'legacy-source:start' 080ebac2 -- docs
git grep -n 'legacy-detail:start' 080ebac2 -- docs
```

At revision `080ebac2` this places 7 proof-route lines (the route-name command above, restricted to
`docs`) and 5 review-narration lines (`git grep -niE 'codex' 080ebac2 -- docs`) inside frozen
regions: the proof-route lines and 4 of the narration lines inside `legacy-source` blocks, the
remaining narration line inside the `legacy-detail` long record of
`docs/formalization/legacy/details/group-spin-models-part-04.md`, along with the two
`docs/formalization/legacy/index.md` items named above.

**Reason.** The text inside a `legacy-source` block is a verbatim snapshot of the page it was
migrated from, held at byte parity against a fixed baseline revision by
`scripts/check_docs_hierarchy.py`; a `legacy-detail` long record is a snapshot of the same kind,
held by the same checker at whitespace-normalized exact parity. Rewording either one means
amending that comparison and recomputing its pinned digests, which weakens an audited check in
order to edit preserved text. The block records what its source said; it is not a current claim of
this project.

**Rule.** A frozen block or long record is a historical snapshot, and a correction to it is
written outside it on the same page. The current claims of `docs/formalization/legacy/index.md`
are in its banner above the block, not in the block.

**Reopen condition.** The migrated catalogue stops being the authority for formalization status, at
which point these blocks and records are no longer pinned and the pages are freely editable or
removable.

**Cadence.** None.

## Prose line references in archival text and record keys

**Target.** References of the form `line N` or `lines A-B` in prose under `docs/` and `tex/`, the
form left over after citations of Lean source by file and line were converted to declaration names.

**Measurement.** The pattern needs PCRE: `git grep -E` accepts `\b` and then matches nothing, so an
ERE spelling of this command reports an empty population instead of failing.

```
git grep -P -n -I '\blines? [0-9]+' 080ebac2 -- docs tex | wc -l
git grep -P -o -I '\blines? [0-9]+' 080ebac2 -- docs tex | wc -l
```

At revision `080ebac2`: 37 occurrences on 37 lines. Thirty are `## Record from former line N`
headings on the detail pages under `docs/formalization/legacy/details/`. Five sit in machine-frozen
regions: three inside `legacy-source` blocks held at byte parity, two of them on the Horsch–von der
Linden pages and one on the Jordan–Wigner backbone page, and two inside a `legacy-detail` long
record held at whitespace-normalized exact parity on
`docs/formalization/legacy/details/group-spin-models-part-05.md`. One is a prose reference to a
record key on `docs/formalization/legacy/details/group-spin-models-part-03.md`, and one is a
labelled quotation of a frozen record in `docs/limitations/documented-axioms/chapter-07.md`.

**Reason.** Frozen archival text and index keys are historical, so none of the thirty-seven is a
citation this repository can rewrite. A record heading is the identifier of its record: the same
number spells the record's `legacy-detail` marker, its `#record-N` anchor, and the catalogue row
that points at it, so it keys the record rather than pointing into a file, and re-keying it breaks
those links. The five frozen references sit in regions `scripts/check_docs_hierarchy.py` compares
against the tracked baseline, so editing them fails that check; only one of the five refers to Lean
source at all, the others being a range of printed proof lines, a line of a displayed equation, and
two occurrences of a record's own superseded pointer. The last two reference frozen text rather
than source: one names a record by its key, and the quotation states in the same sentence that the
quoted number is superseded and gives the live file and declaration.

**Reopen condition.** The parity mechanism changes so that archival rows may be rewritten, in which
case the frozen references are rewritten with them; or the detail records stop being keyed by their
former line number, in which case the headings are re-keyed and the two references to a key follow.

**Cadence.** Re-measure with the commands above at every twenty-pull-request refactor cycle and
replace the figures here with the new ones.

## Closed-issue identifiers in the formalization-status surface

**Target.** Surviving references to the governance issues that staged the formalization-status
migration, wherever they occur on tracked paths: the issue-keyed lines of
`docs/formalization-status-contract.md`, the two provenance pointers kept outside the contract on
`docs/index.md` and `docs/formalization-publication.md`, and the retired-banner entry in the
forbidden-phrase list of `scripts/check_generated_site.py`. Every issue these lines name is closed.

**Measurement.** One command covers the whole surface, documentation and scripts together:

```
git grep -n -P '#(5227|5228|5229)' 080ebac2 -- docs scripts
```

At revision `080ebac2`: 17 lines in total. Thirteen are in
`docs/formalization-status-contract.md` — the three rows of the migration map, and ten sentences
that attribute ownership, obligation, or delivery to the same keys, among them the
publication-contract section heading, the cross-reference in the machine-artifact section, and the
staged-migration sentences beneath the map. Two are the provenance pointers, one on
`docs/index.md` and one on `docs/formalization-publication.md`. One is the forbidden-phrase entry
in `scripts/check_generated_site.py`. The seventeenth sits in the `legacy-source:217:228` block of
`docs/formalization/legacy/index.md`, which the entry on frozen historical text above already
records; it is not parked twice.

**Reason.** The hygiene pass over these pages corrected the sentences whose truth depended on an
issue still being open and kept the pointers that record where a decision or its evidence lives.
Each of the three surviving groups is kept for a reason of its own.

The migration map is keyed by these identifiers: each row states what one identifier owns, what it
delivers, and the condition under which its output becomes authoritative, and the sentences around
the map read the same keys. Removing them means choosing another index for the map and restating
every ownership and acceptance condition in the new terms, which rewrites an accepted contract
instead of correcting how that contract is documented. Documentation hygiene changes the wording of
a claim and not what a contract accepts, so this population lies outside it.

The two lines outside the contract are provenance rather than obligation: one names the separate
project under which formalization-status publication is tracked, the other names where the accepted
publication run's cost evidence and permission audit are recorded. Neither becomes false when its
issue closes, and deleting either leaves a claim on the page whose source can no longer be reached.

The forbidden-phrase entry is a rejection rule and not a claim: it makes the retired
interim-authority banner fail publication if it reappears on a generated page. Dead prose is a
reason to stop writing a phrase, not a reason to stop rejecting it, so the entry stays for as long
as that banner could be republished, and the identifier inside it is a fragment of the rejected
string rather than a reference this repository makes.

**Reopen condition.** The migration map is rewritten onto a different key, or it is retired because
the migration it stages is finished; in either case the cross-reference and staged-migration
sentences are re-keyed in the same change. Independently, a documented decision removes the
provenance pointers, in which case whatever they point at is relocated in the same change.

**Cadence.** Re-measure with the command above at every twenty-pull-request refactor cycle and
replace the figures here with the new ones.

## The printed constant of the double-commutator bound

**Target.** Whether the printed constant `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` of eq. (3.4.13) holds for
even `L ≥ 4r+2` (H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, Problem 3.4.a, statement pp. 67-68, printed solution p. 501).

**Measurement.** The places that record the regime as open:

```
git grep -n -F '4r+2' 080ebac2 -- LatticeSystem docs tex
```

At revision `080ebac2`: 4 lines across 3 files.

**Reason.** This repository has neither a proof of the printed constant in that regime nor a
counterexample to it. What is settled is the constant as literally quantified, refuted by a witness
at `L ≤ 4r+1`, where both counting windows already cover the whole lattice; that mechanism does not
reach the complementary regime and the witness says nothing about it. The bound this repository
proves in place of the printed one is larger and carries the same shape, so nothing downstream
waits on the open regime.

**Reopen condition.** A proof or a counterexample candidate for even `L ≥ 4r+2` is obtained, or the
constant proved here is tightened to the printed one.

**Cadence.** None; the entry is reopened by the condition above rather than by a schedule.
