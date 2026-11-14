# LatticeSystem formalization: from-scratch design


## 1. Status and authority

This document is the tracked design authority for the rewrite.
The active production checker capability is `vocabulary`. It records the
currently enabled production contract, independently of checker infrastructure
available for later stages and of each source's frontier. Each source advances
independently through `registry/source-progress.tsv`.
`TASAKI2020` is currently `vocabulary_reviewed`; its corrected, reconciled, and
frozen census contains 534 physical PDF pages, 3,235 active atomic claims,
3,209 formalization targets, 1,392 distinct source-label/page pairs among active
claims with subkind `equation`, and 63 pages with no claim. Twenty-two additional
rows are reviewed tombstones.
The current tree has the two R3 vocabulary definitions required by that source.
There are no source-claim theorem statements, proofs, or intended axioms yet.
Their type and declaration OIDs, direct imports, and elaborated environment
have passed the R3 semantic contract. A newly registered source may remain at
an earlier lifecycle while the global checker capability stays `vocabulary`.
The recorded census, lifecycle, and vocabulary review do not certify printed-source
statement fidelity. The full rendered-source re-audit and reviewed content
corrections remain incomplete.
A reflection-bound proof-source event records thirty-eight statement-readiness
outcomes: twenty-six identity-preserving content repairs, including eleven
combined classification repairs, three compound-claim splits with eight new
atomic successors and one unchanged canonical duplicate link, and nine
previously omitted atomic claims. Eight genuine new source items preserve the
additions' provenance; the scalar inequality joins its existing whole-Note item,
and all split successors remain in their predecessor items. The unit begins at
the reflection-bound proof heading after the complete conclusion following
(4.1.61), includes (4.1.62)–(4.1.82), footnotes 12 and 13, and the full closing
paragraph before section 4.2. A separately reviewed adjacent-Note addendum
repairs the existing record for the repeated-layer configuration's x1 uniformity
after (4.1.60), preserving its identity and stable metadata. Footnote 13 remains
background with external conditions unresolved. This event does not certify
the printed proof, unresolved source conventions, external references, other
source units, or R4 readiness.
A tower-introduction and setup subset records eight correction-owning
statement-readiness reviews and nine active mathematical outcomes: one
split into separate long-range-order and absence-of-symmetry-breaking recalls,
one identity-preserving variance repair, two combined definition and content
repairs, and four omitted assertions. The additions comprise separate
vector-independence and local-energy outcomes in one genuine named footnote,
plus sector placement and pairwise orthogonality in their shared prose unit.
The accepted subset preserves its nine outcomes without adding the later
tower-energy result. A separate event repairs the existing canonical
energy-display record with its full source context, index domains, uniform
positive constants, and explicit nonzero-numerator premise. A subsequent
split retires the compound theorem record, adds one definedness successor in
its existing theorem item, and reuses the corrected energy record unchanged
as the canonical duplicate. The separate definedness and conditional-energy
outcomes retain the original jointly witnessed statement through a common
cutoff. The modal physical-state discussion remains coverage-only.
A local-energy and spectral-consequence event records fifteen correction-owning
statement-readiness reviews: five identity-preserving content repairs, one
combined definition and content repair, two exclusions, and seven previously
omitted atomic claims. Four new source items preserve the additions' provenance;
the other three additions join their existing source items. The canonical
spectral-equation record carries the repaired shared witness contract. A
separate reviewed event retires the duplicate corollary record in favor of
that unchanged canonical record, preserving both original source items and
memberships. These events do not certify printed proofs, external-reference
proofs, whole-source fidelity, or R4 readiness.
A full-symmetry-breaking source unit records forty-one statement-readiness
outcomes: twenty identity-preserving content repairs, including four combined
classification repairs, six exclusions of nonclaim prose, seven previously
omitted atomic claims, and eight unchanged records. Seven new source items
preserve the additions' provenance, including one named footnote. Existing
claim identities, locators, item metadata, and memberships remain fixed. The
unit covers the full-symmetry-breaking section through the final proposition
proof route. It does not certify printed proofs, unresolved source conventions,
whole-source fidelity, or R4 readiness.
The first order-parameter comparison core event records eight statement-readiness
outcomes: one unchanged theorem, one duplicate retirement into that unchanged
theorem, three nonclaim exclusions, one split into a definition and a conjecture,
one repair to definition content and classification, and one conjecture
reclassification preserving its text. It adds two atomic successors to the
existing conjecture item, preserves all original item metadata and memberships,
and introduces no source item. The separate duplicate-only event retires the two
repaired historical records into the existing definition and conjecture records.
The canonical records, vocabulary reviews and uses, and all source-item metadata
and memberships remain fixed.
Both ordered core transitions are independently accepted in production,
including faithful integration and each new automatic production CI, and
[Issue #5542](https://github.com/phasetr/lattice-system/issues/5542) is completed
and closed. The footnote 25 source contract remains unresolved and tracked in
[Issue #5541](https://github.com/phasetr/lattice-system/issues/5541). The
independently reviewed bounded assessment retains the reported source assertion;
its exact model, objects, parameter domain and relation to the ordered-moment
definition are not fully resolved. No correction event or new formalization
target is authorized.
Neither event certifies whole-unit fidelity,
absence of omissions, mathematical truth, printed-proof correctness, R4, or
proof completion.
An infinitesimal-field source event records six statement-readiness outcomes:
three identity-preserving content repairs, including one combined definition
reclassification, two compound splits, and one unchanged recalled bound.
Each split creates its own first-relation successor in its existing source item
and reuses the unchanged earlier bound for the second relation. The two new
successors retain distinct theorem and equation provenance; no source item or
vocabulary declaration is added. A separate duplicate-only event retires the
atomic theorem successor into the unchanged equation successor, preserving
both source items, all historical memberships and the original split relations.
The equation remains the active canonical record, with its vocabulary review
unchanged. The definition and conjecture in the Remark remain separate.
The bounded source normalization explicitly retains
the footnote-qualified limiting convention; it does not certify printed proofs,
whole-unit fidelity, absence of omissions, mathematical truth, or R4 readiness.
An XXZ local-description event records three active mathematical outcomes:
one identity-preserving Hamiltonian definition repair and two independent
ground-state consequences created by splitting the recalled compound record.
The split preserves the historical predecessor and its source item; no source
item or vocabulary declaration is added. These local model and ground-state
descriptions do not resolve the remaining XXZ long-range-order, theorem-transfer
or order-parameter contracts and duplicate question tracked in
[Issue #5553](https://github.com/phasetr/lattice-system/issues/5553).
They do not certify the whole XXZ unit, mathematical truth, printed proofs,
whole-source fidelity, or R4 readiness.
These bounded registry corrections do not certify printed proofs,
whole-source fidelity, or R4 readiness.

No claim is represented merely because its source PDF exists locally.
The registries are authoritative only for facts they explicitly record.
An empty claims registry means that the census has not begun.
It does not mean that the source has no claims.

## 2. Legacy boundary

The immutable legacy anchor is:
`01bcb49d49db92c225cfa74b74d409dd0a9c4edc`
The anchor exists for provenance and dependency-pin comparison only.
Legacy Lean source is not imported, copied, adapted, or wrapped.
Legacy theorem names do not constrain the new public API.
Legacy documentation, TeX, status records, scripts, and generated artifacts
are not carried into the rewrite.
Good architectural lessons may be restated as principles after independent
review, but no old code or proof text is adopted.
Only `lean-toolchain` and `lake-manifest.json` are byte-preserved from the
anchor.
The package name and the existing mathlib revision remain unchanged.
`.self-local/refs` is private source material and must remain untouched.
Nothing else under `.self-local` belongs to the tracked design.

## 3. Reset tree

The production Lean root is `LatticeSystem.lean`.
During R1 and R2 it contains a module doc comment and nothing else.
There is no `LatticeSystem/` source directory during R1 or R2.
There is no tracked `tex/` or `formalization-status/` directory. The tracked
`docs/` tree is generated public registry output and is drift-checked in CI.
There is no compatibility shim or archived source subtree.
There is one CI workflow for the rewrite.
The root README reports current facts only.
Fixture data is test input, never project status.

## 4. Architectural principles

The main combinatorial abstraction will be a graph.
Lattices and chains will be examples of graphs, not the root abstraction.
The vertex type remains general unless a source claim requires more.
`Fintype` assumptions are introduced locally for finite sums, matrices,
traces, finite-volume Hamiltonians, and other genuinely finite operations.
Infinite graphs must remain expressible without a global finiteness instance.
Finite-volume exhaustion is modeled explicitly when the source requires it.
Finite-dimensional operators use mathlib's matrix and linear-map vocabulary
when that vocabulary matches the source statement.
Conversions between representations must be named, typed, and justified.
No theorem receives a stronger hypothesis merely because it makes a proof
easier.
No conclusion is weakened merely because it is easier to formalize.
Definitions are introduced because a registered source claim needs them.
Convenience APIs are added only after their necessity is demonstrated.

## 5. Tracks, sources, and independent lifecycle

`registry/tracks.tsv` has columns `track_id`, `position`, `title`, and
`public_slug`. Track IDs have the form `TR-[A-Z][A-Z0-9_]*`; positions are
globally unique and contiguous. `registry/sources.tsv` has columns `source_id`,
`track_id`, `source_position`, `source_kind`, `citation_key`, `title`, `authors`,
`year`, `edition`, `identifier_kind`, `identifier`, `public_url`, `public_slug`,
`local_ref_key`, `pdf_oid`, `text_oid`, and `coverage`. Source positions are
unique and contiguous inside a track. The closed source kinds are `book`,
`paper`, `preprint`, and `other`; identifier kinds are `isbn`, `doi`, `arxiv`,
and `none`. Bibliographic identifiers and URLs are verified, never guessed.

The local reference key identifies private material without exposing it in
public generated documentation. PDF and extracted-text OIDs freeze atomically,
have the same Git object width, and cannot silently drift. Coverage follows the
monotone chain `pending`, `pass1`, `pass2`, `reconciled`, `frozen`.

`registry/source-progress.tsv` records each source's independent lifecycle and
review token. The closed lifecycle is `registered`, `source_frozen`,
`census_pass1`, `census_pass2`, `census_reconciled`, `vocabulary_reviewed`,
`skeleton_frozen`, `proof_active`, `complete`. A lifecycle may not exceed the
global checker capability and may not regress. This permits a new registered
book or paper to coexist with an already vocabulary-reviewed source.

`registry/source-invariants.tsv` freezes reconciled sources by source ID,
physical-page count, active-claim count, formalization-target count,
`equation_pair_count`, no-claim-page count, `census_oid`, and review token.
`equation_pair_count` counts distinct source-label/page pairs among active claims
with subkind `equation`, independently of source-item kind. Classification
repairs preserve the original equation source items.
A formalization target is active and not `out_of_scope`. The census OID is the Git
blob OID of that source's canonical `pages.tsv` rows followed by `claims.tsv`
rows, with headers excluded, registry order preserved, UTF-8, and LF endings.

The tracked public catalog is derived from `registry/source-items.tsv` and
`registry/item-claims.tsv`; the former is the authority for stable item IDs and
public metadata rather than a disposable output of locator grouping. Every registered claim, including a reviewed
tombstone retained for provenance, belongs to exactly one reviewed source
item; item/source/page foreign keys, order, label, public group, and slug
are checked. `scripts/generate-public-docs.py` deterministically generates the
Markdown and JSON under `docs/`; both its unit tests and a no-drift check run in
the aggregate checker. Group pages are source-scoped, so equal chapter/group
slugs in different sources cannot mix. A claim is displayed as
`vocabulary_ready` only when it has a review row and its source lifecycle is at
least `vocabulary_reviewed`; an earlier source is at most `review_staged`.
Private local keys, source fingerprints, normalized
source text, and content OIDs are not emitted.

## 6. Page registry

`registry/pages.tsv` is the page-by-page census ledger.
Each row has a stable page ID and source-relative order.
Page IDs are `PG-<source_id>-<decimal>` with a decimal suffix of at least four
digits; the embedded source token must equal the row's source ID.
Printed and PDF page coordinates are separate fields.
The PDF coordinate is a positive physical-page number. A physical PDF page
without a printed page label uses exactly `NONE`; labels are never inferred.
The section field is the most-specific source section active at the start of
the physical PDF page, or exactly `NONE` when no section is active. When a new
section starts partway through a page, claims after the transition carry that
exact local section in their locators even though the page row retains the
section active at page start.
For each physical page, `source_oid` is the Git blob OID of the exact raw UTF-8
page segment in the frozen extracted text, including its terminal form-feed.
`PENDING` is permitted only before that page fingerprint is fixed; a page whose
two census passes are complete must have a valid Git OID.
Pass-one and pass-two census results are recorded separately. Their operational
independence is a human and pull-request attestation under Section 18, not a
second machine-readable observation registry.
Pages with no formalization target still receive a page row after census.
That negative fact must be independently confirmed in pass two.

## 7. Atomic claim registry

`registry/claims.tsv` contains source-atomic mathematical assertions.
A source theorem containing multiple independently usable assertions is split
into atomic claims while preserving their common source label.
Definitions that carry mathematical obligations are registered claims.
Displayed equations are claims when later reasoning depends on them.
Exercises, `remark` claims, and proof-internal lemmas are classified explicitly.
Each claim has one stable ID, one page ID, and one stable order key.
Claim IDs are `CL-<source_id>-<decimal>` with a decimal suffix of at least four
digits; the embedded source token must equal the row's source ID.
Each claim records a precise locator and normalized source content.
The normalized source content and its OID are recorded independently of Lean.
Claim `content_oid` may remain `PENDING` and may transition once to a valid Git
OID. Ordinary changes freeze the normalized content and every fixed OID.
The reviewed `amend_content` and `amend_and_reclassify` transitions below
are the only exceptions for correcting the content of the same source-atomic
claim before R4.
Disposition classifies assertions, definitions, notation, hypotheses, domains,
conjectures, and material explicitly placed out of scope.
Only `out_of_scope` claims carry an exclusion rationale and review reference;
both are mandatory and every other disposition uses `NONE` for both fields.
All non-`NONE` exclusion, tombstone, and dependency rationale/review fields are
ASCII machine tokens matching `[A-Za-z0-9][A-Za-z0-9._:/#@+-]*`.
Detailed prose belongs in the referenced review or source artifact.
Stable IDs are never reused after deletion or reclassification.
An active claim has `tombstone=false` and no supersession metadata.
A tombstoned claim names a distinct existing successor and carries a nonempty
rationale and review reference. Successor chains are acyclic.
Ordinary PRs freeze all exclusion and supersession fields. A dedicated reviewed
correction must invoke the explicit transition checker. Only a false/`NONE`
record may transition to true/successor/rationale/review while all original
identity and content fields remain fixed.
Proof and implementation status is derived from these facts plus the Lean
environment; it is never a hand-edited claim field.

The permanent correction protocol uses six ledgers. `correction-events.tsv`
binds a position, event, and independent review token to one source and exact
base commit. `claim-normalization-reviews.tsv` records every reviewed claim,
including unchanged outcomes. `claim-corrections.tsv` is owned through the
review row and records one of `reclassify`, `exclude_nonclaim`, `split`,
`amend_content`, `amend_and_reclassify`, `retire_duplicate`, or
`add_omitted_claim`, including its old and new classification. The first six
actions target a frozen claim.
`add_omitted_claim` introduces a previously unrecorded source-atomic claim without pretending to split an
existing assertion. Only this action uses `NONE` for both old classification
fields: the claim did not exist in the event base. `NONE` never stands for an
unknown classification of an existing claim.
`claim-successors.tsv` is owned through the correction row and records a
contiguous ordered list of `new_successor` and `existing_duplicate` relations.
`source-item-additions.tsv` is also owned through the correction row and
manifests each new stable source-item ID introduced by an event. Its rows,
their item metadata, and their item-to-claim relations become frozen history.
`claim-content-amendments.tsv` records the identity-preserving content
transition with exactly these columns: `amendment_id`, `event_id`,
`correction_id`, `claim_id`, `old_content_oid`, `new_content_oid`,
`page_source_oid`, and `review_ref`. It is header-only until an actual reviewed
content event is introduced. Amendment IDs have the form
`CA-<machine-token>-<at-least-four-digits>` and are unique. Every
`amend_content` or `amend_and_reclassify` correction owns exactly one amendment
row, with the same event and claim; no other correction action may own one.
The event's closed exact-statement-readiness review owns the correction, and all three review
references agree. The source-atomic claim ID is retained because this action
repairs its transcription, rather than splitting or replacing the assertion.

An `amend_content` correction changes only `claims.tsv` columns 8 and 9:
`normalized_content` and `content_oid`. Its old and new classification pairs
remain equal. The claim must remain an active formalization target.
Its source, order, page, locator, classification, exclusion and tombstone
metadata remain fixed. The new content is nonempty, changed, and not a
literal `True` or `False` surrogate. Both provenance content OIDs are real Git
blob OIDs of the exact UTF-8 field bytes, without an appended newline. The
old OID is recomputed from the event base's content even when the base claim
still records `PENDING`; an already fixed base OID must also match those
bytes. The new OID must equal both the new field's computed blob OID and its
recorded `content_oid`. `page_source_oid` must match the unchanged frozen
page fingerprint. The fingerprints establish which recorded bytes were
reviewed; they do not establish agreement with the printed source.

An `amend_and_reclassify` correction changes both the classification pair
(columns 6 and 7) and the content (columns 8 and 9) of the same claim. The old
and new pairs must differ, although either individual component may stay fixed.
Both pairs use the existing formalization-target disposition and subkind
enumerations: neither `NONE` nor `out_of_scope` is allowed. The correction's
recorded pairs must match the exact event base and current claim rows. The
content bytes and recomputed old and new OIDs must also differ; a class-only
or content-only change cannot use this action. Exactly one closed owning
review, one correction and one amendment manifest the combined change.

The permitted claim-column changes are:

| Action | Mutable columns (1-based) | Required scope |
| --- | --- | --- |
| Ordinary | 9 (`PENDING` to fixed only) | Content and classification fixed |
| `reclassify` | 6, 7 | Existing classification-only contract |
| `amend_content` | 8, 9 | Changed content; classification fixed |
| `amend_and_reclassify` | 6, 7, 8, 9 | Changed classification pair and changed content |
| `exclude_nonclaim` | 6, 10, 11 | Existing reviewed exclusion contract |
| `split` | 12, 13, 14, 15 | Existing reviewed tombstone and successor contract |
| `retire_duplicate` | 12, 13, 14, 15 | Reviewed atomic duplicate; one unchanged existing canonical target; initial mathlib_only predecessor scope |
| `add_omitted_claim` | Fresh row | Existing independent creation contract |

Every unlisted column remains fixed. Both rows of a combined correction are
active formalization targets with `NONE` exclusion and supersession metadata.
The entire source and page records remain unchanged, with frozen source and
page fingerprints. The source invariant review token matches the event review;
counts and census OID are derived by the dedicated checker. These are capability
rules; this foundation introduces no source correction event or registry row.

For both content actions, the base and current source lifecycle must precede
`skeleton_frozen`, and the source must have no bindings in either tree. The target has no slice,
dependency in either direction, or claim-to-axiom relation in either tree.
Its vocabulary-use rows and review basis remain unchanged; its vocabulary
review reference is refreshed to the owning event review. An amendment
owns no successor or source-item-addition rows. Existing correction rules still
reject other unmanifested claim changes, vocabulary drift, unrelated source
changes, stale derived census counts, and R4 or axiom artifacts.

Every historical amendment row is immutable. Both content actions participate
in one per-claim OID history. A later event may amend the same
claim again, deriving its old content OID from that later event's exact base;
the per-claim event history must chain old and new OIDs. Historical new OIDs
and historical classification pairs are not compared indiscriminately with the
latest claim. A pure reclassification between content events leaves the OID
chain intact. Later split, exclusion or lifecycle advancement does not
retroactively invalidate a content event: active-target and pre-R4 eligibility
are checked against that event's base and current trees. A historical base
without this ledger is treated as an empty header; the current tree always
requires it. An ordinary change may introduce only that missing empty header,
and cannot add an amendment row or reopen a past event's exception.
Every split has at least one `new_successor`. A new successor receives a new stable claim
ID, an independently frozen normalized-content OID, an exactly one-item
provenance relation, and a fresh vocabulary review. A correction may retain the
predecessor item or introduce a manifested item when the source has a distinct
publicly reviewed source unit. Excluded and tombstoned predecessors have
no vocabulary review or use rows. The dedicated checker compares the event
tree to its exact base and is the only mode that may admit the manifested
classification, exclusion, tombstone, successor, item, review, and invariant
changes. The event source is a foreign key: every reviewed predecessor,
successor, added item, and updated invariant must belong to it; other sources
remain byte-for-byte frozen. Existing-duplicate successors must already be
active formalization targets in the base and must remain unchanged. It rejects
unrelated registry drift and any correction that introduces
an axiom, binding, contentless surrogate, or other R4 artifact.

A `retire_duplicate` correction retires a second registry record of the same
source-atomic assertion without splitting that assertion or treating it as
nonclaim. Its predecessor is an active formalization target in the exact base,
has exactly one `mathlib_only` vocabulary review, and has no project-vocabulary
use rows in either tree. The correction preserves claim columns 1--11,
including a still-`PENDING` content OID, and changes only the tombstone fields.
It owns exactly one position-1 `existing_duplicate` edge to a distinct
same-source active formalization target that already exists in the base and
remains entirely unchanged. The canonical target may have either reviewed
vocabulary basis; its complete review rows and use-row set remain fixed even
when another correction in the same event names that target. Any needed
canonical repair must be accepted in an earlier separate production event.

Retirement owns no fresh claim, source item or content amendment. Original
item metadata and all existing item-to-claim relations remain fixed, including
the predecessor's membership; the canonical is not inserted into that item.
The source lifecycle in both trees precedes `skeleton_frozen`, and the source
has no bindings in either tree. The predecessor has no slice, dependency in
either direction, axiom or claim-context owner/setup relation in either tree.
Eligibility is checked only against the selected event's base and current
trees, so historical retirement does not prevent a later reviewed canonical
amendment. A selected event containing a retirement must carry its own review
token in the source invariant. Counts and census OID are derived from the
actual resulting registry, including the preserved equation subkinds and item
provenance; retirement grants no source-coverage exception.

Independent source review must establish the same source-atomic assertion,
its faithful context and shared witnesses. Proposition equivalence alone is
insufficient, and normalized text need not be identical. Machine checks
validate frozen evidence and ownership, not this mathematical judgment.
Existing history, source/page fingerprint, vocabulary, R4, invariant and
ordinary base-diff rules remain in force. This initial capability does not
admit project-vocabulary predecessors; extending that boundary requires a
separate reviewed capability change. Infrastructure acceptance does not
accept a source retirement event.

An omitted-claim addition requires exactly one owning closed
`exact_statement_readiness` review with the matching action, event, source and
review token. Its new stable claim ID must be absent from the exact event base.
The new row is an active formalization target with its actual classification,
nonempty source content and the computed Git blob OID of that UTF-8 field
without a trailing newline. `PENDING` and literal `True` or `False` surrogates
are rejected. Its page already exists in the base, with the same frozen source
fingerprint. The source must precede R4 and have no bindings in either tree;
the new claim has no slice, dependency or axiom relation. Existing source,
page, vocabulary declarations and unrelated claim rows remain frozen.

Each new claim has exactly one creation owner: either one split-successor
relation or one omitted-claim correction, never both or multiple split owners.
An addition has no predecessor, successor or content-amendment provenance.
It receives exactly one source-item relation and an event-owned vocabulary
review whose basis agrees with its uses of existing vocabulary. It may join an
existing item while preserving its metadata and old relations. A genuinely
new item requires exactly one `source-item-additions.tsv` row. For an
omission-owned item, its canonical item creator is the omission correction of
the position-1 claim. Further members may have distinct creation corrections,
but each must be a fresh omitted claim with its own closed review and creation
correction in that same event and source. Every member has exactly one item
globally and shares the item's page; existing claims and split successors
cannot join this branch. A split-owned item retains strict single-correction
ownership for all its new successor members. Item manifests, canonical public
grouping, relation positions, first-claim order and historical metadata remain
enforced without exceptions for named items.
Counts and the census OID are derived from the actual corpus;
the updated source invariant carries the event's review token.

Historical addition rows retain their creation-time classification and
ownership. Static validation does not require a historically added claim to
keep that classification or the source to remain before R4 forever: a later
reviewed event may amend, reclassify or split it. Creation-time content,
classification and scope are validated only against the creating event's
exact base. An event may independently own an addition and an amendment;
neither action inherits the other's exception. Ordinary changes cannot create
an unmanifested claim or reopen a historical event.
All six correction ledgers, including their headers, retain the exact base
bytes as a prefix in the same physical order. The content helper independently
enforces this for the amendment ledger. This append restriction applies only
to these six historical ledgers; claims, source items and vocabulary relations
retain their existing canonical-order and set-comparison contracts.
A future event may append its own contiguously positioned review, correction,
successor, item-addition, and content-amendment rows without changing historical ownership.

Source-fidelity review precedes statement freezing. Review each claim against
the rendered source, including its surrounding hypotheses, quantifiers,
coefficients, decorations and limiting order. Record unresolved readings and
the actual depth of verification; a prior audit's absence of findings is not
a fidelity certificate. Coverage accounts separately for formalization
targets, excluded records, and historical tombstones. Private source excerpts
and working audit data remain untracked. Independently reviewed discrepancies
enter the permanent correction protocol before the affected source's R4
statements are accepted. A build, schema check, or OID comparison cannot
replace this mathematical source review.


An independent infrastructure change may migrate an empty bindings or axioms
schema and introduce header-only statement/context tables. Correction guards
compare all artifact rows and preserve the headers of populated tables;
changing an empty header creates no mathematical artifact. A source correction
may not introduce rows in any statement/context/binding or axiom table. Existing
content-amendment and grouped-omission ownership contracts remain unchanged.

## 8. Implementation slices

`registry/slices.tsv` assigns ordered, distinct claims to implementation slices.
A slice may aggregate multiple claims, ordered contiguously from position one.
When slice rows exist, every non-tombstoned claim belongs to exactly one slice.
A claim cannot occur in more than one slice.
Splitting or aggregating work cannot hide or discharge any assertion.

## 9. Dependencies

`registry/dependencies.tsv` records claim-to-claim dependencies.
The closed roles are `requires`, `consequence_of`, and `required_by`.
For `requires`, a claim depends on an earlier target claim.
For `consequence_of`, a claim is derived from an earlier target claim.
For `required_by`, the later source claim is exceptionally pulled forward
because the earlier target at the current frontier needs it.
Global source order is the tuple `(track.position, source.source_position,
claim.order_key)`. Thus every role targets an earlier tuple; `required_by` reverses
the logical edge and requires a nonempty review rationale.
Logical edges are claim-to-target for `requires` and `consequence_of`, and
target-to-claim for `required_by`.
The resulting graph must be acyclic; self and duplicate edges are forbidden.
Cross-track edges are permitted only when the target tuple is earlier and a
nonempty review rationale records the deliberate track crossing.
Every non-`NONE` dependency rationale is an ASCII machine token under the same
rule as claim review fields.
Vocabulary and module imports are not claim edges. The R3 registry, import,
and Lean-environment checks validate them separately under Section 9A.
An unregistered helper cannot silently become a source-level prerequisite.
Proof-local helpers remain local unless reused and independently justified.
Front-to-back order is checked against the dependency graph and registry.

## 9A. R3 vocabulary and import contract

For a source to reach `vocabulary_reviewed`, R3 requires a complete review of
its frozen active claim corpus. `registry/claim-vocabulary-review.tsv` has columns `claim_id`,
`basis`, and `review_ref`. Every active claim has exactly one row. The closed
`basis` values are `mathlib_only` and `project_vocabulary`; `review_ref` is a
nonempty ASCII machine token. A `mathlib_only` claim has no row in
`registry/claim-vocabulary.tsv`. A `project_vocabulary` claim has at least one
such row. Tombstoned claims have no R3 review or use rows.

`registry/vocabulary.tsv` has columns `vocabulary_id`, `declaration`, `module`,
`declaration_kind`, `origin`, `parent_vocabulary_id`, `type_oid`,
`declaration_oid`, `design_role`, and `finiteness_scope`. Stable vocabulary IDs have the form
`VO-LS-NNNN`; the two existing `VO-TASAKI2020-NNNN` IDs are grandfathered and
remain frozen. Declaration and module names live below
`LatticeSystem`. The closed declaration kinds are `definition`, `abbrev`,
`inductive`, `structure`, `class`, `constructor`, `recursor`, `projection`,
and `instance`. Notation has no `ConstantInfo` and is not a registrable R3
vocabulary declaration. The closed origins are `primary` and `generated`.
A primary row has parent `NONE`; a generated row names a distinct primary row
and records a generated declaration kind. Each `type_oid` is the Git object ID
of the canonical serialization of the elaborated declaration's
`ConstantInfo.type` under the R3 environment checker contract. The separate
`declaration_oid` freezes the canonical semantic payload, including a
definition value or abbreviation RHS, so body drift is rejected even when its
type is unchanged. Generated and inductive-family rows use the kind-specific
payload defined by the semantic checker. Both OIDs may be `PENDING` only before
the global checker capability advances to `vocabulary`.

The closed design roles are `graph_core`, `finite_volume`, `linear_algebra`,
`operator_algebra`, `quantum_state`, `stat_mech`, `fermion`, and `generated`.
The closed finiteness scopes are `none`, `local_operation`,
`explicit_finite_volume`, and `inherited`. Generated rows use the `generated`
role and inherit their parent's finiteness scope. A global lattice or graph
vocabulary declaration may not require `Fintype`; finiteness appears only in a
local operation or in explicit finite-volume data.

`registry/claim-vocabulary.tsv` has columns `claim_id` and `vocabulary_id`.
It records the complete many-to-many use relation. Every project vocabulary
row, including every registrable surface generated declaration, maps
to at least one reviewed active claim. Thus an unused convenience declaration
is rejected. Compiler-internal generated artifacts in the checker's exact,
version-pinned baseline are not public vocabulary and are not registry rows.
This relation is vocabulary use, not a source-claim dependency
and not evidence that the source claim has been stated or proved.

`registry/modules.tsv` has columns `module`, `source_path`, and `role`, with
closed roles `leaf`, `umbrella`, and `root`. Module names and source paths are
bijective by the standard dot-to-directory mapping, and exactly one row is the
root `LatticeSystem` module at `LatticeSystem.lean`. Every project vocabulary
declaration belongs to a registered leaf module. Umbrella and root modules
contain no vocabulary declarations of their own.

`registry/imports.tsv` has columns `module`, `position`, `imported_module`,
`is_exported`, `is_meta`, and `import_all`. Positions start at one and are
contiguous within a module. The three flags are literal booleans. Every actual
direct import of a registered module is represented exactly once in source
order, and every recorded import exists in the elaborated module. Imports
below `LatticeSystem` target registered modules; production external imports
target Mathlib modules allowed by the R3 environment contract. Compiler-added
implicit `Init` is a semantic-checker baseline and is not a registry row.
Project import
edges are acyclic. Unregistered modules, declarations, or imports fail R3.

The R3 semantic checker inspects the elaborated Lean environment rather than
trusting source text. It compares declaration name, owning module, kind, and
normalized type OID with the registries; compares the direct import structures
and their flags with `imports.tsv`; and rejects all unregistered project
declarations. It also rejects project axioms, theorem or lemma declarations,
direct or transitive `sorryAx` use, and source-claim declarations disguised as
vocabulary. Static lexical checks remain defense in depth only.

All five R3 registries are header-only in `bootstrap`. At global capability
`vocabulary`, every source whose lifecycle is `vocabulary_reviewed` has complete
active-claim review and vocabulary use, every vocabulary OID is frozen, and
module and import registries match the environment. Sources at an earlier
lifecycle may coexist without weakening those completed-source guarantees.

## 10. Bindings and statement contexts

`registry/bindings.tsv` joins each active formalization target to its primary
statement and, for an assertion or conjecture, its separate proof declaration.
Its columns are `claim_id`, `statement_decl`, `proof_decl`, `module`,
`statement_kind`, `statement_shape`, `statement_type_oid`,
`statement_value_oid`, `implementation_status`, `proof_kind`,
`proof_type_oid`, `proof_value_oid`, `nonvacuity_decl`, `nonvacuity_oid`, and
`review_ref`. Primary statements are definitions or abbreviations whose kernel
type and value are frozen independently. A `proof_proposition` carries its
proposition as a value; the proof theorem's type is exactly that bound primary
statement, rather than a disjunction, implication, or other weakening of it.
Assertions and conjectures use `proof_stub`; definitions, notation, hypotheses,
and domains use their corresponding definitional statement shapes and no
separate proof fields. A definitional binding has no direct or transitive hole.
The checker requires an actual proposition value for `proof_proposition`.
The other shape names classify the source disposition; they do not by
themselves certify that a definition, relation, hypothesis, or domain has a
particular Lean type. Those bindings still have checked declaration kinds and
frozen type and value OIDs. Whether their types and values express the source,
including any parameterized hypothesis or predicate, requires independent
original-source review.

Before source skeleton freeze, every formalization target of that source must
have exactly one binding, with no inactive or out-of-scope bindings. All type
and value OIDs required by the frozen schema must be real Git object IDs;
`PENDING` is only a staging value. The separate proof's `proof_value_oid` is
`NONE` while its direct hole remains. R5 changes that value OID when discharging
the proof, while preserving the primary statement and the proof's frozen type.
No binding may disappear or silently change identity. A reviewed migration is
required to change a frozen statement. Registry text alone does not establish
that a declaration exists or that it faithfully represents the source.
The semantic binding fields remain frozen subject to the staged OID rules;
`proof_value_oid` can change when a proof is discharged or revised, and
`review_ref` is mutable provenance metadata. Updating that review token grants
no permission to change a frozen statement or its proof type.

`registry/statement-modules.tsv` records each statement module's path and
`leaf` or `umbrella` role. `statement-imports.tsv` freezes its ordered direct
imports and environment flags. These are separate from the vocabulary module
registries. One module cannot occupy both roles. Exactly one skeleton umbrella
reaches every statement leaf, while the production root reaches none of the
unresolved statement modules.

`registry/claim-context.tsv` records `claim_id`, contiguous `position`,
`setup_claim_id`, `use_kind`, `scope`, and `review_ref`. Its targets are earlier
registered definitions, notation, hypotheses, or domains. An `assumption` must
occur in a binder domain or antecedent of the statement; a term-level `let`
supplies a value and is not an assumption. Repeated rows for a setup retain
every assumption requirement; a `term_reference` row cannot erase it in either
row order. `same_item` context cannot cross a
source item; `inherited` context still requires explicit independent review.
Every project constant used in a primary statement is registered vocabulary or
a registered primary statement. Each vocabulary constant occurring directly
in the primary type or value additionally requires that claim's reviewed
`claim-vocabulary.tsv` admission and `project_vocabulary` basis. A generated
surface declaration uses its own vocabulary ID; admitting its parent does not
admit it automatically. This necessary direct-use check does not require all
R3 review links to occur directly in a primary declaration, expand context
dependencies into vocabulary links, or define future proof-use policy.
Actual inter-claim uses require a reviewed
context or dependency edge. The `required_by` dependency is the explicit
source-order exception that pulls a later prerequisite forward.

The environment gate verifies declaration kind and owning module, primary type
and value OIDs, exact proof type, direct-hole status, ordered imports and
reviewed context. An exact proof type is the bare bound primary constant applied
to the proof declaration's own universe parameters in their declared order. Both
declarations quantify the same number of parameters; their parameter names may
differ. Specialized, reordered, duplicated, or extra universe arguments are not
that universally quantified obligation. A nonvacuity theorem must reference its bound statement and
may not be `True`, a restatement of its own hypotheses, or those same shapes
hidden behind a definition. These checks do not replace original-source
statement review or the separate review of locator documentation.
The nonvacuity guard unfolds the tested implication and conjunction shapes
with fuel 16, comparing hypotheses and conclusions at the same weak-head
normalization boundary using explicit `.all` transparency, including irreducible
definitions. The primary-value `True` check uses the same transparency. These
local classifications do not change the frozen expression encodings. It is a bounded structural defense against self-fulfilling
obligations, not a proof of mathematical nonemptiness or source fidelity.

## 11. Axioms

All intentional project axioms live under `LatticeSystem/Axioms/`.
No intentional project axiom may be declared elsewhere.
The closed taxonomy is `abstract_cstar`, `state`, `gns`, `kms`, `weak_dual`,
`wigner`, and `contentless_predicate`.
Their required module suffixes are respectively `AbstractCStar`, `State`, `GNS`,
`KMS`, `WeakDual`, `Wigner`, and `ContentlessPredicate`.
Thermodynamic or infinite limits and all finite-dimensional statements are not
axiom categories.
Taxonomy membership is not permission to add an axiom.
Every axiom needs a stable ID, category, declaration, module, source locator,
rationale, reopen condition, and frozen `axiom_type_oid`. Its declaration and module are under the
category-consistent `LatticeSystem.Axioms.*` namespace.
That string-level namespace check is not semantic existence evidence; the Lean
environment gate remains mandatory before skeleton freeze.
Approval is an explicit review event, not a hand-edited derived status column.
`registry/claim-axioms.tsv` records the approved claim-to-axiom relation.
Actual `#print axioms` dependency is derived from the Lean environment and
compared exactly with that approved relation. This is the actual syntactic
kernel dependency closure, not a claim that every axiom is logically necessary.
Outside the kernel standards
`propext`, `Classical.choice`, and `Quot.sound`, every actual axiom must be
registered and accounted for; an unknown imported axiom is rejected. A direct
`sorryAx` is permitted only for its registered unresolved proof stub.
An ordinary unproved theorem must never be converted to an axiom.
An axiom cannot be hidden behind a definition, instance, or wrapper theorem.
Unused approved axioms and unapproved actual axioms both fail the final gate.

## 12. Production and skeleton isolation

Final claim modules use their stable production paths from the moment they are
created.
During skeleton construction those modules may contain registered `sorry`
stubs only under the skeleton build target.
A dedicated `LatticeSystem.Skeleton` umbrella imports every registered
claim module for completeness checking.
The production root must not import that umbrella or any unresolved claim.
When registered statement modules and bindings are present, the skeleton gate
also checks the following Lake isolation contract. With both tables empty, the
gate instead performs the contract-only check described in §13 and does not run
this Lake configuration inspection or the nondefault Skeleton build.
The supported default Lake target is the `LatticeSystem` Lean library with its
`leanArts` facet. The pinned Lake TOML decoder and effective glob expansion must
select the canonical root and only registered vocabulary modules at their exact
registered source paths. Every registered vocabulary module, including a
transitive nonseed import, must also resolve through Lake's actual package
provider to that same registered physical source. The nondefault Skeleton target
must likewise resolve every registered statement umbrella and leaf to its exact
registered physical source; statement modules remain excluded from default seeds. Multiple safe vocabulary seeds
and explicit safe globs are allowed; a library's name or the spelling of its `roots` is not sufficient.
Package `extraDepTargets` and every library's `needs`/`extraDepTargets` must be
empty, as must package and library `dynlibs`/`plugins`, which also fetch build
targets during ordinary module setup. Nonempty target dependencies and other
default facets are unsupported and
fail closed; this gate does not implement general custom/native target analysis.
The future R5 production policy may import only declarations at the proved
frontier; the current R4 production root reaches no statement module.
The skeleton target may locally permit the warnings corresponding exactly to
registered stubs.
Global `warningAsError` must remain enabled. The registered-skeleton Lake gate
requires it in the normalized package options and each library's effective
build-type/package/library options; absence has Lean's false default. Library
inheritance and equivalent typed true values are permitted.
The skeleton mechanism must not disable all warnings to accommodate `sorry`.
Lean's frontend advances parsing and elaboration together, retaining scoped
and local syntax. Its command trees and imported declaration ranges bind each permitted
`set_option warningAsError false in` to its exact registered unresolved theorem.
File, section, namespace, unrelated-declaration, and completed-proof exceptions
are rejected; comments and layout do not determine option scope.
Diagnostic-consuming `#guard_msgs`/`#guard_panic` test commands, `nolint`
attributes, and explicit
Boolean-false `linter.*` or `warn.*` options are forbidden in registered statement
sources, including within an otherwise permitted proof exception. The direct
command, term, tactic, and grind option forms use the same recognizer; conversion
tactics delegate their nested ordinary tactics to that ordinary tactic form.
The owned
warningAsError exception does not authorize additional checker exemptions.
The ordinary missing-owner and kernel-axiom guards retain their independent
diagnostics before this additional suppression policy is checked.
The Lake configuration is checked using Lean's effective option normalization:
known diagnostic-disabling options are forbidden in package or library options,
including `weak` names and string-valued Booleans. Unknown weak options are
ignored as Lean ignores them. Unrelated options, including harmless false values
and recursion/printing settings, are permitted. Package and library
`moreLeanArgs`/`weakLeanArgs` must be empty: these raw CLI argument arrays can
override diagnostic options, and the supported configuration uses typed
`leanOptions` instead of a general command-line argument interpreter.
R1 contains no fake Lean stubs and no skeleton umbrella.
The declaration-free bootstrap and census phases supply only registry data,
the checker contract, and runtime-generated checker fixtures.

## 13. Direct-sorry bijection

Before skeleton freeze, a semantic checker must inspect the elaborated Lean
environment, not source text alone.
It must establish a bijection between registered unresolved claim bindings and
direct uses of `sorryAx` in their bound declarations.
Every registered stub must exist at its claim-bound module and name.
Every direct `sorryAx` occurrence must have exactly one registered claim.
The checker must reject a stub hidden behind another unproved declaration.
It must distinguish direct unresolved status from transitive axiom dependency.
It must also verify declaration kind, module ownership, the primary statement's
`statement_type_oid` and `statement_value_oid`, and the separate proof's exact
bound statement type and `proof_type_oid`.
The same environment inspection must compute actual intentional-axiom use.
Lexical grep checks remain defense in depth, not semantic evidence.
The infrastructure provides this environment checker and positive and negative
runtime cases. Its presence with empty production binding and statement tables
is a contract-only check, not a registered skeleton or R4 completion. Source
fidelity, exact statement construction, frozen OIDs, and complete source
coverage remain separate prerequisites.

## 14. Checker capabilities and source lifecycles

The value in `phase.tsv` is a global checker capability. It advances only when
the corresponding validation is implemented and exercised, and it does not
assert that every registered source has reached that stage. Source completion
is represented only by `source-progress.tsv`.

R1 is atomic reset and bootstrap checker construction.
R1 produces the clean tree, schemas, exact-root check, base-diff guard, fixtures,
CI, and buildable empty production root.
R2 is a whole-book two-pass census.
Pass one records every page and candidate atomic claim in source order.
Pass two independently reconciles every page, label, equation, claim boundary,
and no-claim page.
R2 cannot finish with an unreviewed page or an unresolved census discrepancy.
For a source at `census_reconciled`, its R2 registry has every page in both-pass `complete` state, a
frozen page-source OID, and no tombstoned claim. Slices, dependencies, bindings,
claim contexts, axioms, claim-to-axiom relations, statement modules, and statement
imports remain empty until their later phases.
R3 is vocabulary and type construction.
Only vocabulary required to state the full registered corpus is implemented.
Every active claim is classified as Mathlib-only or as requiring registered
project vocabulary, and every project declaration is justified by at least
one active claim.
Graph-centric structure and local finiteness are enforced during R3 review.
R3 does not prove source claims except unavoidable well-definedness obligations,
which are registered as their own slices.
R4 creates the whole-book exact-statement typed skeleton.
R4 infrastructure may be developed separately while source corrections are
reviewed. Its existence does not make uncorrected statements ready to freeze;
correction events and R4 artifacts remain separate changes.
Every implement disposition receives its final module, declaration, exact
statement, locator doc comment, and registered temporary proof hole.
The skeleton umbrella elaborates all claims together.
The production root remains isolated from every unresolved claim.
R4 freezes IDs, locators, source order, module paths, names, types, and digests.
The semantic environment bijection is a mandatory R4 completion gate.
Proof work is blocked throughout R1, R2, R3, and R4.
R5 replaces registered stubs with proofs strictly front to back.
No R5 PR may skip an earlier unresolved logical prerequisite.
The frontier advances only when the claim is proved and its actual axiom set
matches the approved set exactly.

## 15. Anti-regression rules

Stable IDs cannot be deleted or reused.
Source order and slice positions cannot move backward or silently change.
Verified locators cannot drift.
Frozen source-content and binding statement OIDs cannot change silently.
Bindings cannot disappear after introduction.
The global checker capability cannot regress. The production policy recognizes `vocabulary`
only when the R3 registry, module/import, and Lean-environment checks all run
and pass. The `skeleton` capability requires its registered semantic contract; `proof`
production policy remains unavailable.
Derived claim state cannot regress from proved to unresolved.
The number of registered proof declarations whose actual values directly use
`sorryAx` is monotone nonincreasing in R5. Their permanent `proof_stub`
implementation classification does not change when their proof values do.
Bootstrap and a declaration-free census use the exact canonical doc-only root.
At vocabulary capability, only the canonical vocabulary root and registered
vocabulary modules are permitted;
they remain subject to the semantic vocabulary gate and contain no source-claim
theorem, `sorry`, `admit`, `native_decide`, or axiom.
A later lifecycle never disables that source's frozen identity, counts,
census OID, active-state, source-order, page-coupling, or two-pass census
invariants. For `TASAKI2020`, those frozen counts are 534 pages, 3,235 active
claims, 3,209 formalization targets, and 1,392 distinct source-label/page pairs
among active claims with subkind `equation`. The census-capability requirement
that slices, source-claim dependencies,
bindings, contexts, axioms, claim-to-axiom relations, statement modules, and
statement imports are header-only is phase-local;
it is not part of the later frozen-census invariant check.
A theorem deletion is not proof progress.
An assumption strengthening or conclusion weakening is statement drift.
Future or unresolved modules cannot enter production imports.
The base-diff checker compares the PR tree with a verified merge base.
If the base predates registries, the checker reports a documented bootstrap
skip only after proving that the base is a valid ancestor commit; it does not
claim historical coverage.
Default base-diff freezes all exclusion and supersession fields. A reviewed
normalization is accepted only when `--correction-event` invokes the dedicated
checker against the event's exact base commit; ordinary PR checks reject it.
The CI selector supplies that option only when exactly one event is new relative
to the actual merge base and its recorded `base_commit` equals that merge base.
Once the event is present in the base, the selector returns to ordinary
base-diff mode, so the exception is one-shot and the permanent ledgers are
frozen like other registry history.

## 16. Structural checker guarantee through R3

The checker guarantees only structural facts visible in tracked files.
It enforces the closed tracked-path policy, rejects tracked symlinks, and
requires `git ls-files fixtures` to be empty. Test-only fixture mode requires
an explicit flag and a canonical path below an exported, repository-external
`LATTICE_TEST_ROOT`. Runtime tests copy the production registry into a system
temporary root and apply named mutations; cases absent from production, such
as minimal multi-source, Lean-semantic, tree, policy, and base-diff scenarios,
are generated there deterministically.
It verifies the two preserved pin blobs against the legacy anchor.
It accepts the atomic source-freeze prerequisite during `bootstrap` and keeps
coverage `pending` until census begins.
It validates TSV headers, column counts, control-character exclusions, ID
forms, enumerations, uniqueness, ordering, foreign keys, slice positions,
dependency roles, axiom references, and phase-specific registry semantics.
For every reconciled production source it additionally requires that source's
frozen invariant row, contiguous page IDs/order keys/PDF coordinates with two
complete passes and fixed source OIDs, its exact active-claim and equation-pair
counts, and strict global tuple order with page coupling. The census gate requires
the eight implementation registries (slices, dependencies, bindings, contexts,
axioms, claim-to-axiom relations, statement modules, and statement imports) to
be header-only only at census capability. At vocabulary capability, the
registry and R3 contract separately enforce their header-only requirements,
complete claim review and vocabulary use, and exact registered module and
import coverage; the frozen census check does not supply those R3 guarantees.
During bootstrap and a declaration-free census it compares the production root
byte-for-byte with the canonical doc-only source. During R3 staging and in
vocabulary it compares the root with the canonical registered umbrella import
and requires every production Lean path to be derived exactly from
`modules.tsv`.
Future-file lexical checks are only nonsemantic hygiene and never environment
evidence.
It checks the written merge gate and an unchecked `USER ONLY` box.
It exercises generated positive and negative runtime cases without committed
fixture data.
The correction suites cover classification-only, content-only, combined
content/classification, exclusion, split, duplicate retirement and omitted-claim transition families and
negative cases for review, event-source ownership, manifest completeness,
successor provenance and ID freshness, stable source-item additions, nested
order keys, item and vocabulary propagation, immutable rows and OIDs, derived
counts, census OID, contentless surrogates, production content OIDs, historical
row forgery, split-without-new-successor, axioms, and premature R4 artifacts.
Content-amendment cases additionally exercise pending and fixed old content,
actual old/new hashes, page fingerprints, unchanged identities, pre-R4 scope,
vocabulary review renewal, absent historical ledgers, repeated amendments,
unrelated sources, and the return to ordinary immutable-history checks.
Combined cases additionally exercise mandatory dual changes, each classification
component alone, exact old/new classification facts, direct static ownership,
mixed chronological content histories, later split and exclusion, six-ledger
byte-prefix ordering, legal nested claim/item insertion and vocabulary row-set
permutations. Three real temporary-Git selector compositions exercise first and
second combined events and historical ordinary fallback through the actual
base-diff and transition guards, without replacing the selector's checker.
These are distinct from the seven existing real skeleton composition chains.
Synthetic public generation checks the corrected public classification while
keeping content, hashes and correction ownership private.
Shared-item cases exercise independently created omissions within one named
item, canonical first-relation ownership, per-member provenance and uniqueness,
strict split ownership, unchanged public generation and privacy, frozen later
item/history relations, and a later reviewed amendment of one grouped member.
Duplicate-retirement cases exercise the initial mathlib-only predecessor
boundary, an unchanged project-vocabulary canonical, direct canonical review
and use preservation despite same-event correction ownership, pre-R4 and
unreferenced-predecessor eligibility, preserved original item membership,
exact event invariant review, and all six ledger prefixes. A real temporary
Git chain exercises earlier canonical repair, retirement, ordinary historical
fallback and later canonical amendment through the actual selector and guards.
The CI-selector suite separately checks the one-shot correction route,
historical-event fallback to normal mode, a later event, merge-base mismatch rejection,
multiple-new-event rejection, and invalid-base rejection.
Against a valid registry-bearing merge base it detects stable-ID deletion,
identity/order/locator/OID drift, page-pass and reference-coverage regression,
slice membership or position loss, dependency or claim-axiom loss, binding
loss or frozen declaration drift, tombstone reversal, and phase regression.
It does not independently prove that the reviewed census omitted no source
claim or that two readings were operationally independent.
It does not parse or understand mathematics.
It does not prove that a locator matches the book.
The separate R3 semantic gate inspects the elaborated Lean environment for the
registered vocabulary and imports. The R4 infrastructure separately tests the
direct-`sorryAx` bijection, exact statement/proof types, transitive axiom
dependencies, contexts, and warning exception ownership, including a minimal
counterfactual tree through the production gate entrypoints. These are not
guarantees of this structural section or an actual source's R4 freeze. Neither
gate certifies adequacy of hypotheses or original-source fidelity; source
statement construction and independent review remain required.
The source-freeze prerequisite must not be represented as satisfying the R2
census gate, and R1 must not be represented as satisfying any R2, R3, or R4
gate. For each source, only its reviewed lifecycle row records completion of a
source-specific census, vocabulary review, skeleton, or proof stage.

## 17. Review and merge authority

Every rewrite PR requires explicit user permission for that exact PR number and
its current exact head SHA.
Permission for a branch, design, previous SHA, or different PR is invalid.
Any head change invalidates prior permission.
Green CI and reviewer approval are evidence, not merge authority.
The rewrite trunk must be protected and `rewrite-ci` must be a required check.
Repository-side protection is external state and must be verified separately.
The agent may not check the `USER ONLY` confirmation box.
Auto-merge and merge-queue enrollment are forbidden.
Direct push to the protected rewrite trunk is forbidden.
Force push is forbidden.
No merge action is taken merely because implementation is complete.
The PR remains open until the exact gate is satisfied.

## 18. Human review obligations

Humans verify the source edition and fingerprint.
Humans reconcile both census passes.
Humans judge atomic claim boundaries and exact statement fidelity.
Humans approve every intentional axiom and its rationale.
Humans review assumption strength, conclusion strength, and source order.
Humans decide whether an architectural abstraction is faithful and maintainable.
Humans grant or withhold merge authority at an exact PR and SHA.
Automation makes omissions and regressions visible; it does not replace these
judgments.
