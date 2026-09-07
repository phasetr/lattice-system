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
git grep -o -E '#[0-9]{4,}' a70632ea -- 'LatticeSystem/**/*.lean' | wc -l
git grep -n -E '#[0-9]{4,}' a70632ea -- 'LatticeSystem/**/*.lean' | wc -l
git grep -l -E '#[0-9]{4,}' a70632ea -- 'LatticeSystem/**/*.lean' | wc -l
```

At revision `a70632ea`: 1252 occurrences on 1130 lines across 531 files.

**Reason.** A single sweep edits 531 modules at once, so every one of them and every downstream
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
git grep -noiE '(ladder|sublattice|perron[-–]+frobenius|PF|MLM|saturated[- ]ladder|N[ée]el)[- ]route' a70632ea -- '*.lean' '*.md' '*.tex' | wc -l
```

At revision `a70632ea`: 46 phrases.

**Reason.** These phrases name the mathematical strategy a declaration follows — the `sl₂` ladder,
the Perron–Frobenius argument, the sublattice decomposition — and in one case the boundary of a
hypothesis. They are technical content and are correct as written, so there is no defect here to
fix.

**Reopen condition.** A phrase in this family is found to name a review or workflow step rather
than a mathematical argument. That is a defect and is rewritten when found rather than parked.

**Cadence.** None. The command is kept so that a later diagnosis can confirm the family is
unchanged rather than re-derive the classification.

## References to the documentation checker

**Target.** Prose that names the repository's documentation-checking tooling.

**Measurement.** The live checker, then the retired tooling:

```
git grep -niE 'check_docs_hierarchy\.py' a70632ea -- '*.lean' '*.md' '*.tex' | wc -l
git grep -niE 'audit_gate|audit-helpers|capstones\.txt|docs_names\.py|pre-push' a70632ea -- '*.lean' '*.md' '*.tex' | wc -l
```

At revision `a70632ea`: 22 and 0.

**Reason.** All 22 name `scripts/check_docs_hierarchy.py`, which exists and enforces exactly the
constraint the surrounding sentence describes. Naming the mechanism that governs a page is current
documentation of that page, not narration of an internal process. The retired tooling has no
surviving mention, so that half of the class is empty.

**Reopen condition.** The second command returns a non-zero count, that is, prose names tooling
that no longer exists; or `scripts/check_docs_hierarchy.py` is retired or renamed, in which case
the references are updated with it in the same change.

**Cadence.** Re-measure both commands at every twenty-pull-request refactor cycle.

## Frozen historical text in migrated pages

**Target.** Sentences held inside `legacy-source` blocks on migrated pages, together with the
version-1 wording and the interim-authority anchor on lines 28 and 30 of
`docs/formalization/legacy/index.md`.

**Measurement.** List the block spans on a page and compare a candidate line number against them:

```
git grep -n 'legacy-source:start' a70632ea -- docs
```

At revision `a70632ea` this places 7 proof-route lines (the route-name command above, restricted to
`docs`) and 4 review-narration lines (`git grep -niE 'codex' a70632ea -- docs`) inside such blocks,
along with the two lines of `docs/formalization/legacy/index.md` named above.

**Reason.** The text inside a `legacy-source` block is a verbatim snapshot of the page it was
migrated from, held at byte parity against a fixed baseline revision by
`scripts/check_docs_hierarchy.py`. Rewording it means amending that comparison and recomputing its
pinned digests, which weakens an audited check in order to edit preserved text. The block records
what its source said; it is not a current claim of this project.

**Rule.** A frozen block is a historical snapshot, and a correction to it is written outside the
block on the same page. The current claims of `docs/formalization/legacy/index.md` are in its
banner above the block, not in the block.

**Reopen condition.** The migrated catalogue stops being the authority for formalization status, at
which point these blocks are no longer pinned and the pages are freely editable or removable.

**Cadence.** None.

## The printed constant of the double-commutator bound

**Target.** Whether the printed constant `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` of eq. (3.4.13) holds for
even `L ≥ 4r+2` (H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, Problem 3.4.a, statement pp. 67-68, printed solution p. 501).

**Measurement.** The places that record the regime as open:

```
git grep -n -F '4r+2' a70632ea -- LatticeSystem docs tex
```

At revision `a70632ea`: 4 lines across 3 files.

**Reason.** This repository has neither a proof of the printed constant in that regime nor a
counterexample to it. What is settled is the constant as literally quantified, refuted by a witness
at `L ≤ 4r+1`, where both counting windows already cover the whole lattice; that mechanism does not
reach the complementary regime and the witness says nothing about it. The bound this repository
proves in place of the printed one is larger and carries the same shape, so nothing downstream
waits on the open regime.

**Reopen condition.** A proof or a counterexample candidate for even `L ≥ 4r+2` is obtained, or the
constant proved here is tightened to the printed one.

**Cadence.** None; the entry is reopened by the condition above rather than by a schedule.
