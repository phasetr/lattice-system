# Tasaki formalization: from-scratch design


## 1. Status and authority

This document is the tracked design authority for the rewrite.
The current registry phase is `census`.
The R2 ledger has been reconciled and frozen. It contains 534 physical PDF
pages, 3,172 active atomic claims, 1,401 unique equation-label/page pairs, and
63 pages with no claim.
The current tree has two candidate R3 vocabulary definitions for partial trace.
There are no source-claim theorem statements, proofs, or intended axioms yet.
The R3 vocabulary schema, working inventory, and candidate vocabulary type
OIDs exist, but the phase has not advanced. Rows staged while the phase remains
`census`, including apparently complete rows and non-`PENDING` OIDs, are work
in progress rather than evidence that the R3 review, implementation,
independent review, or semantic gate is complete.
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
The reset is one atomic change, not a chain of design and deletion PRs.
Only `lean-toolchain` and `lake-manifest.json` are byte-preserved from the
anchor.
The package name and the existing mathlib revision remain unchanged.
`.self-local/refs` is private source material and must remain untouched.
Nothing else under `.self-local` belongs to the tracked design.

## 3. Reset tree

The production Lean root is `LatticeSystem.lean`.
During R1 and R2 it contains a module doc comment and nothing else.
There is no `LatticeSystem/` source directory during R1 or R2.
There is no tracked `docs/`, `tex/`, or `formalization-status/` directory.
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

## 5. Source identity

Every phase contains exactly one source row, whose stable ID is `TASAKI2020`;
missing, alternate, and extra sources are rejected until a future design change
explicitly extends the source set.
The initial bootstrap row requires a nonempty local key, edition exactly
`unspecified`, blank PDF/text OIDs, and `pending` coverage.
As the first R2 prerequisite, that row may transition while the phase remains
`bootstrap` to a verified edition and two valid, equal-width Git OIDs, while
coverage remains `pending` and all census registries remain header-only.
This source-freeze transition is atomic and does not assert that census has
started or completed.
The local reference key identifies a private file without tracking that file.
Edition, pagination, and coverage remain `pending` or `unspecified` until
verified from the actual source.
No ISBN, DOI, page range, or theorem number may be guessed.
Edition may transition once from `unspecified` to a verified ASCII edition
token and is then frozen. Post-bootstrap tokens may not equal `unspecified`,
`pending`, `unknown`, or `NONE`, compared case-insensitively.
The PDF object OID and extracted-text object OID transition atomically from
both blank to two valid Git OIDs before R2 census begins and then freeze. Both
fingerprints use the same Git object width (40 or 64 lowercase hexadecimal
digits); mixed object formats are rejected.
Coverage follows the closed monotone chain `pending`, `pass1`, `pass2`,
`reconciled`, `frozen`; post-bootstrap coverage is not `pending`.
Blank OIDs are permitted only during bootstrap.
Changing either source fingerprint requires explicit review and a new census.

## 6. Page registry

`registry/pages.tsv` is the page-by-page census ledger.
Each row has a stable page ID and source-relative order.
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
Each claim records a precise locator and normalized source content.
The normalized source content and its OID are recorded independently of Lean.
Claim `content_oid` may remain `PENDING`, may transition once to a valid Git
OID, and is immutable thereafter; no other transition is valid.
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
Ordinary PRs freeze all exclusion and supersession fields. A future dedicated,
reviewed supersession workflow must invoke the explicit transition checker;
only a false/`NONE` record may transition to true/new-ID/rationale/review while
all original identity and content fields remain fixed.
Proof and implementation status is derived from these facts plus the Lean
environment; it is never a hand-edited claim field.

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
Thus every role targets an earlier source-order claim; `required_by` reverses
the logical edge and requires a nonempty review rationale.
Logical edges are claim-to-target for `requires` and `consequence_of`, and
target-to-claim for `required_by`.
The resulting graph must be acyclic; self and duplicate edges are forbidden.
Every non-`NONE` dependency rationale is an ASCII machine token under the same
rule as claim review fields.
Vocabulary and module imports are not claim edges. R3 will add a separate
import/environment checker for them.
An unregistered helper cannot silently become a source-level prerequisite.
Proof-local helpers remain local unless reused and independently justified.
Front-to-back order is checked against the dependency graph and registry.

## 9A. R3 vocabulary and import contract

R3 begins with a complete review of the frozen active claim corpus before its
phase advances. `registry/claim-vocabulary-review.tsv` has columns `claim_id`,
`basis`, and `review_ref`. Every active claim has exactly one row. The closed
`basis` values are `mathlib_only` and `project_vocabulary`; `review_ref` is a
nonempty ASCII machine token. A `mathlib_only` claim has no row in
`registry/claim-vocabulary.tsv`. A `project_vocabulary` claim has at least one
such row. Tombstoned claims have no R3 review or use rows.

`registry/vocabulary.tsv` has columns `vocabulary_id`, `declaration`, `module`,
`declaration_kind`, `origin`, `parent_vocabulary_id`, `type_oid`,
`declaration_oid`, `design_role`, and `finiteness_scope`. Stable vocabulary IDs have the form
`VO-TASAKI2020-NNNN`. Declaration and module names live below
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
the phase advances to `vocabulary`.

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

All five R3 registries are header-only in `bootstrap`. During `census`, R3 may
stage partial review, vocabulary, module, and import rows, and either vocabulary
OID may be `PENDING`; those rows carry no phase-completion meaning. In
`vocabulary`, the review covers the entire frozen active claim corpus, every
type OID is frozen, the vocabulary/use relation is complete, and module and
import registries match the environment. The existence of this contract and a
staged inventory do not mean those vocabulary-phase conditions currently hold.

## 10. Bindings

`registry/bindings.tsv` is the declaration binding ledger.
A binding joins a claim to its statement declaration, optional proof
declaration, stable module, statement OID, and optional nonvacuity declaration.
The content OID identifies the frozen declaration text under a documented
normalization rule.
Once frozen, a binding cannot disappear or silently change identity.
Changing a frozen statement requires explicit user review, a migration record,
and a new digest; ordinary proof PRs cannot do it.
Registry text alone does not prove that a Lean declaration exists.
That fact requires a semantic Lean environment checker.

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
rationale, and reopen condition. Its declaration and module are under the
category-consistent `LatticeSystem.Axioms.*` namespace.
That string-level namespace check is not semantic existence evidence; the Lean
environment gate remains mandatory before skeleton freeze.
Approval is an explicit review event, not a hand-edited derived status column.
`registry/claim-axioms.tsv` records the approved claim-to-axiom relation.
Actual `#print axioms` dependency is derived from the Lean environment and
compared exactly with that approved relation.
An ordinary unproved theorem must never be converted to an axiom.
An axiom cannot be hidden behind a definition, instance, or wrapper theorem.
Unused approved axioms and unapproved actual axioms both fail the final gate.

## 12. Production and skeleton isolation

Final claim modules use their stable production paths from the moment they are
created.
During skeleton construction those modules may contain registered `sorry`
stubs only under the skeleton build target.
A dedicated future `LatticeSystem.Skeleton` umbrella imports every registered
claim module for completeness checking.
The production root must not import that umbrella or any unresolved claim.
Production targets may import only declarations at the proved frontier.
The skeleton target may locally permit the warnings corresponding exactly to
registered stubs.
Global `warningAsError` must remain enabled.
The skeleton mechanism must not disable all warnings to accommodate `sorry`.
R1 contains no fake Lean stubs and no skeleton umbrella.
The declaration-free bootstrap and census phases supply only registry data,
the checker contract, and static checker fixtures.

## 13. Direct-sorry bijection

Before skeleton freeze, a semantic checker must inspect the elaborated Lean
environment, not source text alone.
It must establish a bijection between registered unresolved claim bindings and
direct uses of `sorryAx` in their bound declarations.
Every registered stub must exist at its claim-bound module and name.
Every direct `sorryAx` occurrence must have exactly one registered claim.
The checker must reject a stub hidden behind another unproved declaration.
It must distinguish direct unresolved status from transitive axiom dependency.
It must also verify declaration kind, module ownership, statement type, and
the normalized binding `statement_oid`.
The same environment inspection must compute actual intentional-axiom use.
Lexical grep checks remain defense in depth, not semantic evidence.
R4 cannot complete until this checker exists and its positive and negative
fixtures pass.

## 14. Phases

R1 is atomic reset and bootstrap checker construction.
R1 produces the clean tree, schemas, exact-root check, base-diff guard, fixtures,
CI, and buildable empty production root.
R2 is a whole-book two-pass census.
Pass one records every page and candidate atomic claim in source order.
Pass two independently reconciles every page, label, equation, claim boundary,
and no-claim page.
R2 cannot finish with an unreviewed page or an unresolved census discrepancy.
The completed R2 registry has every page in both-pass `complete` state, a
frozen page-source OID, and no tombstoned claim. Slices, dependencies, bindings,
axioms, and claim-to-axiom relations remain empty until their later phases.
R3 is vocabulary and type construction.
Only vocabulary required to state the full registered corpus is implemented.
Every active claim is classified as Mathlib-only or as requiring registered
project vocabulary, and every project declaration is justified by at least
one active claim.
Graph-centric structure and local finiteness are enforced during R3 review.
R3 does not prove source claims except unavoidable well-definedness obligations,
which are registered as their own slices.
R4 creates the whole-book exact-statement typed skeleton.
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
The phase value cannot regress. The production policy recognizes `vocabulary`
only when the R3 registry, module/import, and Lean-environment checks all run
and pass. It rejects `skeleton` and `proof` until their semantic phase checks
exist.
Derived claim state cannot regress from proved to unresolved.
The number of registered unresolved claim bindings is monotone nonincreasing in R5.
Bootstrap and a declaration-free census use the exact canonical doc-only root.
Once R3 staging registries name production modules during census, only the
canonical vocabulary root and registered vocabulary modules are permitted;
they remain subject to the semantic vocabulary gate and contain no source-claim
theorem, `sorry`, `admit`, `native_decide`, or axiom.
A later phase never disables the frozen source identity, 534-page, 3,172-claim,
1,401-equation, active-state, source-order, page-coupling, or two-pass census
invariants. The census requirement that slices, source-claim dependencies,
bindings, axioms, and claim-to-axiom relations are header-only is phase-local;
it is not part of the later frozen-census invariant check.
A theorem deletion is not proof progress.
An assumption strengthening or conclusion weakening is statement drift.
Future or unresolved modules cannot enter production imports.
The base-diff checker compares the PR tree with a verified merge base.
If the base predates registries, the checker reports a documented bootstrap
skip only after proving that the base is a valid ancestor commit; it does not
claim historical coverage.
Default base-diff freezes all exclusion and supersession fields. Retirement is
accepted only by the explicit dedicated supersession mode, with a new stable
claim ID and reviewed tombstone transition; ordinary PR checks reject it.

## 16. Structural checker guarantee through R3

The checker guarantees only structural facts visible in tracked files.
It enforces the closed tracked-path policy and rejects tracked symlinks.
It binds every committed fixture path to its staged Git blob OID, rejects
unlisted, binary/NUL, oversized, symlink, and unexpected fixture paths, and
permits fixture mode only through an explicit test-only flag below `fixtures/`.
It verifies the two preserved pin blobs against the legacy anchor.
It accepts the atomic source-freeze prerequisite during `bootstrap` and keeps
coverage `pending` until census begins.
It validates TSV headers, column counts, control-character exclusions, ID
forms, enumerations, uniqueness, ordering, foreign keys, slice positions,
dependency roles, axiom references, and phase-specific registry semantics.
For the production census and every later phase it additionally requires the
exact one-row frozen
source record, 534 contiguous page IDs/order keys/PDF coordinates with two
complete passes and fixed source OIDs, exactly 3,172 active, unsuperseded claims
in strict source order whose order-key page prefix matches the referenced page,
and exactly 1,401 unique equation-label/page pairs. Only `census` requires the
five pre-R3 implementation registries to be header-only. `vocabulary` instead
requires complete claim review and vocabulary use, exact registered module and
import coverage; its absence requirements are enforced by the R3 contract,
not by the frozen census check.
During bootstrap and a declaration-free census it compares the production root
byte-for-byte with the canonical doc-only source. During R3 staging and in
vocabulary it compares the root with the canonical registered umbrella import
and requires every production Lean path to be derived exactly from
`modules.tsv`.
Future-file lexical checks are only nonsemantic hygiene and never environment
evidence.
It checks the written merge gate and an unchecked `USER ONLY` box.
It exercises committed positive and negative fixtures.
Against a valid registry-bearing merge base it detects stable-ID deletion,
identity/order/locator/OID drift, page-pass and reference-coverage regression,
slice membership or position loss, dependency or claim-axiom loss, binding
loss or frozen declaration drift, tombstone reversal, and phase regression.
It does not independently prove that the reviewed census omitted no source
claim or that two readings were operationally independent.
It does not parse or understand mathematics.
It does not prove that a locator matches the book.
It does not inspect the elaborated Lean environment.
It does not establish the direct-`sorryAx` bijection.
It does not compute transitive axiom dependencies.
It does not certify theorem correctness or adequacy of hypotheses.
Those are future semantic checks and human review obligations.
The source-freeze prerequisite must not be represented as satisfying the R2
census gate, and R1 must not be represented as satisfying any R2, R3, or R4
gate. A staged R3 inventory does not satisfy the vocabulary gate.

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
