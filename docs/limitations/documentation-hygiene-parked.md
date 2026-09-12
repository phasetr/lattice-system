---
layout: page
title: "Parked documentation-hygiene decisions"
permalink: /limitations/documentation-hygiene-parked/
---

# Parked documentation-hygiene decisions

This page is the record of documentation-hygiene populations this repository has decided not to
act on, together with the measurements that settled such a population instead of parking it. Each
entry states what it covers, the command that measures it on tracked paths at a pinned revision,
and how often the measurement is retaken. A parked entry adds why it is not being fixed and the
condition that reopens it; an entry whose population is measured empty states its disposition
instead, because there is nothing left to reopen. A state diagnosis that encounters one of these
populations reads the entry first and does not record it as an unresolved defect.

A command whose paths reach this page excludes it from its own pathspec. The page quotes the
phrases it measures, so without that exclusion a command would count this record of a population as
part of the population.

A parked entry records a decision, not a claim that the population is harmless in general.
Reopening one requires its stated condition to hold; observing that the population still exists is
not itself a reason to reopen.

## Issue and pull-request identifiers in Lean doc comments

**Target.** Identifiers of four digits or more in `.lean` files under `LatticeSystem/`, wherever a
comment carries them — module documentation, declaration doc comments and line comments are all
counted — against the convention that comments carry only non-obvious reasons and no task
identifiers.

**Measurement.** The four-digit threshold is the one the decision fixed, and it keeps the book's
equation and problem numbers out of the count. Shorter tracker identifiers are left uncounted by it
and lie outside this entry rather than being measured by it:

```
git grep -o -E '#[0-9]{4,}' 0fcd9ba7 -- 'LatticeSystem/**/*.lean' | wc -l
git grep -n -E '#[0-9]{4,}' 0fcd9ba7 -- 'LatticeSystem/**/*.lean' | wc -l
git grep -l -E '#[0-9]{4,}' 0fcd9ba7 -- 'LatticeSystem/**/*.lean' | wc -l
```

At revision `0fcd9ba7`: 1250 occurrences on 1128 lines across 530 files.

**Reason.** A single sweep edits 530 modules at once, so every one of them and every downstream
importer is rebuilt. The rebuild is the dominant cost and it buys no change to any statement,
proof, or published claim, which puts the sweep off the critical path of the book-order
formalization. The population is also not uniformly mechanical: some four-digit references are
internal cross-reference labels rather than tracker numbers, so a blind pattern edit would corrupt
meaning.

**Fix on touch.** A change that touches a module's doc comments for any other reason removes the
identifiers in that module, in the same commit. No separate sweep is opened for the remainder.

**Reopen condition.** Fix-on-touch brings the measured count below roughly one hundred, so that
one closing sweep is reviewable as a single diff; or a linter that rejects the pattern is adopted,
which makes the convention enforceable rather than aspirational.

**Cadence.** Re-measure with the commands above at every 20-PR refactor cycle and replace the
figures here with the new ones.

## Proof-route names in the Marshall–Lieb–Mattis proof tree

**Target.** Names of proof routes in the Marshall–Lieb–Mattis and Theorem 2.3 tree — "ladder
route", "Perron–Frobenius route", "sublattice route" and the rest of that family — in Lean module
documentation, published pages, and the proof guide.

**Measurement.** The name is written with an en dash, so the pattern accepts the en dash as well as
the hyphen; a hyphen-only pattern reports a small spelling-dependent subset instead of the family:

```
git grep -noiE '(ladder|sublattice|perron[-–]+frobenius|PF|MLM|saturated[- ]ladder|N[ée]el)[- ]route' 080ebac2 -- '*.lean' '*.md' '*.tex' ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
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

This entry parks nothing. The population below is empty at the pinned revision, so what is recorded
here is a measurement and not a decision to leave something unfixed.

**Target.** Prose under `LatticeSystem/`, `docs/` and `tex/` that names the audit-gate tooling
retired when the hard-check infrastructure was abolished: `audit_gate.py`, `audit-helpers.sh`, the
`capstones.txt` allowlist, the `docs_names.py` registry that backed the dead-declaration sweep, and
the pre-push hook that ran them. A sentence naming a mechanism that no longer exists cannot be
current documentation of anything, so a surviving mention would be a defect rather than a
population to weigh.

**Measurement.** One pattern covers every retired name:

```
git grep -niE 'audit_gate|audit-helpers|capstones\.txt|docs_names\.py|pre-push' 0fcd9ba7 -- '*.lean' '*.md' '*.tex' ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
```

At revision `0fcd9ba7`: 0.

**Disposition.** Resolved by measurement, so a reopen condition would have nothing to reopen. The
entry is kept because what settles the question is the measurement rather than an argument: a later
diagnosis re-runs the command instead of re-deriving the classification. A mention that appears
afterwards is a defect and is removed when found rather than parked.

**Not tracked here.** The same revision carries 23 references to the live checker:

```
git grep -niE 'check_docs_hierarchy\.py' 0fcd9ba7 -- '*.lean' '*.md' '*.tex' ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
```

That script exists and enforces exactly the constraint each surrounding sentence describes, so
naming it is current documentation of the page it governs. Those 23 lines are neither a defect nor
a parked population, and this page does not track them.

**Cadence.** Re-measure the first command at every 20-PR refactor cycle.

## Frozen historical text in migrated pages

**Target.** Sentences held inside `legacy-source` blocks or inside a `legacy-detail` long record
on migrated pages, together with the version-1 catalogue wording and the interim-authority anchor
inside the `legacy-source:217:228` block of `docs/formalization/legacy/index.md`.

**Measurement.** List the frozen spans on a page and compare a candidate line number against them:

```
git grep -n 'legacy-source:start' 080ebac2 -- docs ':!docs/limitations/documentation-hygiene-parked.md'
git grep -n 'legacy-detail:start' 080ebac2 -- docs ':!docs/limitations/documentation-hygiene-parked.md'
```

At revision `080ebac2` this places 7 proof-route lines (the route-name command above, restricted to
`docs`) and 5 review-narration lines inside frozen regions: the proof-route lines and 4 of the
narration lines inside `legacy-source` blocks, the remaining narration line inside the
`legacy-detail` long record of `docs/formalization/legacy/details/group-spin-models-part-04.md`,
along with the two
`docs/formalization/legacy/index.md` items named above.

The narration population is the mentions, in migrated prose, of the external review tool consulted
while the recorded work was done. Its pattern is that tool's name, which is not printed here: doing
so would put back on a current page the wording the hygiene pass removed from live prose. A
case-insensitive search for the name over `docs`, excluding this page, returns the 5 lines counted
above.

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
git grep -P -n -I '\blines? [0-9]+' 0fcd9ba7 -- docs tex ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
git grep -P -o -I '\blines? [0-9]+' 0fcd9ba7 -- docs tex ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
```

At revision `0fcd9ba7`: 37 occurrences on 37 lines. Thirty are `## Record from former line N`
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

**Cadence.** Re-measure with the commands above at every 20-PR refactor cycle and replace the
figures here with the new ones.

## Closed-issue identifiers in the formalization-status surface

**Target.** Surviving references to the governance issues that staged the formalization-status
migration, wherever they occur on tracked paths: the issue-keyed lines of
`docs/formalization-status-contract.md`, the two provenance pointers kept outside the contract on
`docs/index.md` and `docs/formalization-publication.md`, and the retired-banner entry in the
forbidden-phrase list of `scripts/check_generated_site.py`. Every issue these lines name is closed.

**Measurement.** One command covers the whole surface, documentation and scripts together:

```
git grep -n -P '#(5227|5228|5229)' 0fcd9ba7 -- docs scripts ':!docs/limitations/documentation-hygiene-parked.md'
```

At revision `0fcd9ba7`: 17 lines in total. Thirteen are in
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
interim-authority banner fail publication once the catalogue is in the authoritative state, if it
reappears on a generated page. Until then the rule is staged rather than live, as the entry on
pinned phrases below records. Dead prose is a reason to stop writing a phrase, not a reason to stop
rejecting it, so the entry stays for as long as that banner could be republished, and the
identifier inside it is a fragment of the rejected string rather than a reference this repository
makes.

**Reopen condition.** The migration map is rewritten onto a different key, or it is retired because
the migration it stages is finished; in either case the cross-reference and staged-migration
sentences are re-keyed in the same change. Independently, a documented decision removes the
provenance pointers, in which case whatever they point at is relocated in the same change.

**Cadence.** Re-measure with the command above at every 20-PR refactor cycle and replace the
figures here with the new ones.

## Pinned phrases without a self-test of their own

**Target.** Two kinds of pinned string that no self-test asserts to occur in the sources they
guard: the entries of the forbidden-phrase tuple in `scripts/check_generated_site.py`, which are
rejection rules held inside that script rather than published text, and the interim-authority
sentence that `scripts/generate_formalization_site.py` writes into the provenance header of every
generated view. Deleting an entry from the tuple, or reverting the generator sentence to an anchor
that no longer exists, leaves every gate green for as long as the catalogue is published in the
prototype state.

**Measurement.** The tuple is read as a range, because the quoted shape of its entries recurs in
other string tuples of the same file; the generator sentence is matched on a fragment of itself that
is not one of the forbidden phrases:

```
git show 0fcd9ba7:scripts/check_generated_site.py | sed -n '/^AUTHORITATIVE_FORBIDDEN_PHRASES = (/,/^)/p' | grep -c '^    "'
git grep -F 'remains authoritative for as long as' 0fcd9ba7 -- scripts/generate_formalization_site.py | wc -l
```

At revision `0fcd9ba7`: 11 tuple entries and 1 generator sentence.

**Observed property.** The self-test iterates over whatever the tuple contains and requires each
phrase found there to be rejected in the authoritative state, so a tuple with an entry removed is a
shorter loop that still passes. The rejection is skipped outside the authoritative state, which
leaves the generator's sentence unconstrained while the catalogue is a prototype: replacing it with
a dead anchor rewrites the provenance header of every generated view, and each check over the
generated source still passes.

**Reason.** Closing this means strengthening the self-test until it asserts that these phrases are
present in the sources they guard, which is a change to the checker beyond the scope approved for
the documentation-hygiene pass. The exposure is bounded meanwhile, because the phrases guard a
publication state this repository has not entered.

**Reopen condition.** The catalogue cutover, at which point the rejection becomes live and the
phrases begin guarding the published state; or the next approved change to
`scripts/check_generated_site.py`, which is the occasion on which the self-test can be strengthened
in the same change.

**Cadence.** Re-measure with the commands above at every 20-PR refactor cycle and replace the
figures here with the new ones.

## The printed constant of the double-commutator bound

**Target.** Whether the printed constant `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` of eq. (3.4.13) holds for
even `L ≥ 4r+2` (H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, Problem 3.4.a, statement pp. 67-68, printed solution p. 501).

**Measurement.** The places that record the regime as open. The same condition is written both as
`L ≥ 4r+2` and as `L > 4r+1`, and the TeX spelling carries no space around its relation, so the
pattern accepts both forms; a fixed-string scan for one of them reports a spelling-dependent subset
of the population instead of all of it:

```
git grep -n -E '4r\+2|L ?[>≥] ?4r\+1' 080ebac2 -- LatticeSystem docs tex ':!docs/limitations/documentation-hygiene-parked.md'
```

At revision `080ebac2`: 6 lines across 4 files.

**Reason.** This repository has neither a proof of the printed constant in that regime nor a
counterexample to it. What is settled is the constant as literally quantified, refuted by a witness
at `L ≤ 4r+1`, where the radius-`2r` and radius-`4r` balls each cover the ring, so the
ball-counting constant collapses; that mechanism does not reach the complementary regime and the
witness says nothing about it. The bound this repository proves in place of the printed one is
larger and carries the same shape, so nothing downstream waits on the open regime.

**Reopen condition.** A proof or a counterexample candidate for even `L ≥ 4r+2` is obtained, or the
constant proved here is tightened to the printed one.

**Cadence.** None; the entry is reopened by the condition above rather than by a schedule.

## Superseded headings preserved in the migration map and the permalink stubs

**Target.** Two records of what a heading used to be, both held verbatim against the frozen
baseline by `scripts/check_docs_hierarchy.py`: the third column of every row of
`docs/formalization/migration-map.md`, which reproduces the baseline heading its row maps, and the
`<a id="..."></a>` stubs on `docs/index.md`, whose identifiers are the Kramdown identifiers of
those same baseline headings. When a heading is corrected on the page that now owns it, both of
these keep stating the superseded wording.

**Measurement.** Each population is the set the checker matches one to one against the frozen
headings, so counting the rows and the stubs counts it:

```
git grep -c -P '^\| `[^`]+` \| `\d+` \| ' a12cbb0e -- docs/formalization/migration-map.md
git grep -c -P '<a\s+id="[^"]+"></a>' a12cbb0e -- docs/index.md
```

At revision `a12cbb0e`: 68 mapped rows and 68 anchor stubs.

**Reason.** Neither is a current claim of this project. The map's third column is defined as the
historical heading that its anchor and line number identify, and the checker compares it against
the baseline text, so rewriting it would falsify the map rather than correct it. An anchor
identifier is a permalink for a page that once carried the heading; changing it breaks the external
links that resolve through it, and the checker requires the stub set to equal the identifiers
derived from the frozen headings. Where a heading has been corrected, the correction is carried by
the page that owns it and by the visible link label, which no check reads.

**Reopen condition.** The frozen baseline stops being the authority for the migrated pages, at
which point the map and the stubs are regenerated from the current headings in the same change.

**Cadence.** None. Both counts move only when the fixture moves, which the checker reports on every
run.

## Issue identifiers and time-relative wording in the proof guide and the non-legacy pages

**Target.** References of four digits or more to issues and pull requests, and wording that dates a
statement by when it changed rather than by what it says, in `tex/proof-guide.tex` and under
`docs/` outside the frozen legacy catalogue. The entry on Lean doc comments above covers the same
identifiers under `LatticeSystem/`, and the entry on the formalization-status surface covers the
three governance identifiers kept there on purpose.

**Measurement.** The patterns need PCRE: `git grep -E` accepts `\b` and then matches nothing, so an
ERE spelling reports an empty population instead of failing. The identifier pattern accepts the TeX
spelling, in which the hash is escaped:

```
git grep -P -o -I '(?<!\w)\\?#\d{4,}' a12cbb0e -- tex | wc -l
git grep -P -n -I '(?<!\w)#\d{4,}' a12cbb0e -- docs ':!docs/formalization/legacy' ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
git grep -P -n -I '\b(now|previously|formerly|earlier|no longer|used to|recently|originally)\b' a12cbb0e -- tex docs ':!docs/formalization/legacy' ':!docs/limitations/documentation-hygiene-parked.md' | wc -l
```

At revision `a12cbb0e`: 609 identifier occurrences on 508 lines of the proof guide, 430 lines
across 24 files under `docs/`, and 298 lines across 25 files carrying one of the listed words.

**Reason.** Neither population is a defect class that a pattern settles. The identifier counts (609
occurrences on 508 lines in the proof guide; 430 lines across 24 files under `docs/`) are known to
include deliberate provenance pointers, which is what the formalization-status entry above records
for three of them, so a pattern edit would delete pointers whose removal leaves a claim with no
reachable source; both counts are therefore upper bounds on the population of unwanted identifiers
rather than exact counts of it. The listed words are ordinary English that mathematical prose uses
for reasons unrelated to repository history, so the third command's count (298 lines across 25
files) is likewise an upper bound on the population rather than the population itself; acting on it
requires reading several hundred lines one at a time, which is off the critical path of the
book-order formalization. The classification of individual sites is therefore not recorded here,
and none of the three figures above should be read as a count of defects.

**Fix on touch.** A change that edits one of these passages for another reason converts that
passage in the same commit. No separate sweep is opened for the remainder.

**Reopen condition.** Fix-on-touch brings the proof-guide identifier count low enough that one
closing sweep is reviewable as a single diff, or a prose linter that rejects the identifier pattern
outside frozen text is adopted.

**Cadence.** Re-measure with the commands above at every 20-PR refactor cycle and replace the
figures here with the new ones.
