# LatticeSystem: permanent contracts

## 1. Authority and scope

This document defines the rewrite's enduring mathematical and acceptance
contracts. Current counts, declarations, schemas and stages are read from the
registries, generated catalog and Lean environment, not duplicated here.
The README is the usage/restart entry; Issue #5479 owns the current work and
single next action. Project `AGENTS.md` governs private material, delegation,
package management, disposal and the exact user merge gate.

The rewrite does not copy, adapt, import, wrap or depend on legacy code, proofs,
APIs, scripts or documentation. The legacy anchor
`01bcb49d49db92c225cfa74b74d409dd0a9c4edc` is used only for provenance and the
byte-preserved `lean-toolchain` and `lake-manifest.json` pins. The package name
and declared Mathlib revision remain fixed unless a dependency change is
explicitly authorized.

The tracked tree is closed by `Checker/CheckAll.lean`. Runtime fixtures belong
only in isolated system temporary roots; they are test inputs, not project
status. Public `docs/` are generated exclusively by
`lake exe checker --docs` from registered metadata. They omit private
source text, paths and fingerprints.

## 2. Mathematical representation and source review

Graphs are the primary combinatorial abstraction; lattices and chains are
instances. Vertex types remain general. Finiteness is local to an operation or
explicit finite-volume model that needs it, rather than a global `Fintype`
restriction. Infinite graphs and thermodynamic limits are not excluded by
default or assigned an axiom category merely for being infinite. Use existing
Mathlib matrix/linear-map interfaces when faithful; transfers between
representations must be named, typed and justified.

Definitions and APIs are introduced because a registered claim requires them.
Implementation convenience does not justify stronger hypotheses, weaker
conclusions, a changed domain or an invented source definition. Preserve the
source's objects, quantifiers, coefficients, modalities, qualifications, shared
witnesses and limit order. Distinguish mathematical assertions from explanatory,
navigational or bibliographic context. Record genuinely unresolved source
contracts without completing them by assumption. A source author or user raw
input is not a blanket prerequisite for independent source review.

Review the rendered original and its necessary surrounding context before
freezing a statement. Inherited normalized text, a previous audit's silence,
OID agreement and machine success are not source-fidelity evidence. A bounded
accepted correction does not certify whole-unit completeness, mathematical
truth, printed proofs or whole-source fidelity.

## 3. Capability, lifecycle and order

Global checker capability and each source's lifecycle are distinct, monotone
records. A new earlier-stage source may coexist with a completed later-stage
source without weakening the latter's guarantees.

| Stage | Acceptance meaning |
| --- | --- |
| R1 | Clean reset, source-freeze prerequisite and structural checker foundation. |
| R2 | Independent two-pass page/claim census, reconciled boundaries and frozen provenance. |
| R3 | Required vocabulary, types, complete target basis/use review and environment agreement. |
| R4 | Source-faithful exact primary statements, bindings and complete typed skeleton; all freeze gates pass. |
| R5 | Replace registered proof stubs strictly in source/dependency order. |

Proof implementation is blocked until R4 is complete. R3 constructs definitions
and types; well-definedness assertions remain explicit mathematical obligations
subject to source, binding and proof gates, not exceptions authorizing early
proofs or slices. Checker infrastructure and fixtures for a later stage do not
advance a production source or certify its coverage.

Global source order is `(track position, source position, claim order key)`.
Front-to-back implementation cannot skip an unresolved logical prerequisite.
Dependency roles and implementation slices must preserve this order and account
for their claims. `required_by` is the reviewed exception that pulls a later
prerequisite forward; its logical edge is reversed relative to the other roles.
Cross-track dependencies need explicit rationale. Cycles, hidden unregistered
prerequisites and missing assertions cannot be disguised by work aggregation.

## 4. Identity, provenance and permanent corrections

Stable source, page, item and claim identities are never deleted or reused.
Printed and physical PDF coordinates are distinct. A page records the section
at its start; a claim after a within-page transition needs its exact local
section and locator. Every physical page is inventoried, including pages with
no claim. Two-pass independence and source-atomic boundaries require independent
review, not just two recorded completion fields.

Source PDF/text fingerprints freeze atomically. Page fingerprints identify the
frozen extracted page segment, including its terminal form-feed. Claim content
OIDs identify exact UTF-8 field bytes without an appended newline. These bind
observed bytes, not agreement with the original. Per-source invariant counts
and census OIDs are derived from the actual canonical corpus. Classification
repairs do not rewrite original equation-item identity.

Ordinary changes freeze content, classification, identity, provenance and
historical supersession, apart from explicitly staged OID finalization. A source
correction is a separate independently reviewed transition against one exact
base and source. Its closed readiness review owns the corrective action;
source, page and unrelated records stay fixed. Source corrections cannot create
axioms, bindings or other R4 artifacts.

The seven permanent ledgers are correction events, normalization reviews,
corrections, successors, source-item additions, content amendments and location
amendments. Their
headers and rows retain the exact previous bytes as a prefix; a later event
appends its own contiguous positions without reopening historical ownership.
The concrete schemas and allowed field changes are checked by
the Lean correction and content checkers.
Their distinct mathematical meanings remain:

| Action | Meaning and identity boundary |
| --- | --- |
| `reclassify` | Repair classification while retaining the same source assertion and content. |
| `exclude_nonclaim` | Record reviewed exclusion, including an author's withdrawal of a source strategy, without deleting the record or asserting that every retained step is false. |
| `amend_content` | Repair the transcription of the same source-atomic assertion; classification is fixed. |
| `amend_and_reclassify` | Repair both content and classification of that same assertion. |
| `amend_location` | Refine an existing claim and its singleton item's locators on the same frozen page, preserving all other fields. |
| `split` | Preserve a compound predecessor as history and create at least one new atomic successor. |
| `retire_duplicate` | Preserve a second record of the same source-atomic assertion and link one unchanged existing canonical target. |
| `add_omitted_claim` | Independently create a previously unrecorded assertion, with no fictitious predecessor. |

Location maintenance requires a closed `source_location_readiness` review and
one uniquely event-owned amendment for the existing claim/item pair. Physical
and printed page, section, identities, source order, content and its OID,
source/page fingerprints, item membership and classification remain fixed.
Exact old/new locator chains end at the current rows; historical ledger prefixes
remain unchanged. Ordinary transitions cannot alter locators. Earlier snapshots
without this ledger retain their observed absence rather than acquiring a
fabricated historical artifact.

An author's withdrawal removes the reviewed unit from formalization-target
scope while preserving its identities, wording and source history. It neither
rejects all intermediate calculations as false nor changes unaffected adjacent
material or creates a replacement mathematical model.

Content repairs and additions require real recomputed content OIDs and agreement
with the unchanged frozen page fingerprint, and
nonempty source-faithful text, not literal `True`/`False` or contentless
surrogates. Content-repair old/new hashes must chain across later events.
Eligibility is checked at each event's own base/current trees; a later amendment,
reclassification or retirement does not rewrite the earlier event.

Corrections are pre-R4 and require the applicable absence of bindings, slices,
claim dependencies, contexts and axiom uses enforced by the transition guard.
Vocabulary declarations and uses stay fixed except the explicitly owned new
review/use relations. Counts and census fingerprints are derived, not granted
an exception. Capability acceptance itself does not accept a source event.

Each fresh claim has exactly one creation owner: a split-successor relation or
an omission correction, never both. The closed readiness review covers its
creation action; each omission has its own creation review and correction.
Each new target has a fresh vocabulary review and exactly one item relation.
Genuine source paragraphs or labeled units determine
item boundaries. An existing item can receive new claims while its metadata
and historical relations stay fixed. For a genuinely new omission-owned item,
the position-one claim's correction is the sole item creator; further members
are independently created omissions in the same event/source. A new split-owned
item has one split owner. A manifested new item cannot mix split and omission
ownership. Historical item metadata and memberships remain preserved.

Duplicate retirement requires independent identity, context and shared-witness
review: proposition equivalence alone is insufficient, and normalized wording
need not be identical. The initial capability admits only a `mathlib_only`
predecessor without project-vocabulary uses, and one unchanged existing active
canonical formalization target. Any required canonical repair must have been accepted in an
earlier separate production event. Retirement creates no fresh claim/item,
changes no original membership and does not treat the assertion as nonclaim.

The actual base-diff selector permits a correction exception only for one new
event whose recorded base equals the verified merge base. Once present in that
base, the event returns to ordinary immutable-history checks. An invalid or
missing base cannot silently supply historical coverage.

## 5. Vocabulary and typed statements

Every active formalization target has exactly one reviewed R3 basis and the
complete required relation to existing project vocabulary. `mathlib_only`
has no project-use row; `project_vocabulary` has at least one. Excluded and
historical records do not receive a target review. Every public vocabulary
declaration, including registrable generated declarations, needs a target use.
A basis/use review is not a closed typed physics contract or statement proof.

The Lean environment must agree with registered declarations, owning modules,
ordered direct imports, types and semantic values. Reject unregistered project
declarations, imports, intentional axioms and direct/transitive proof holes in
vocabulary. Lexical inspection is defense in depth, not semantic evidence.
Exact version-pinned encodings and compiler baselines belong to `Checker/` and
the driver implementations; module paths and current type/value OIDs belong to
the registries.

Before source skeleton freeze, every target has exactly one primary statement
binding and no excluded/historical claim has one. Freeze the primary type and
value independently. Assertions and conjectures have a separate proof theorem
whose type is exactly the bound primary proposition with its own universe
parameters in order. A disjunction, implication, specialization or other
weakening is not that proof obligation. Definitional binding forms have no
separate proof fields and no direct or transitive hole.

Statement context must record actual earlier setup uses and dependencies.
An assumption occurs in a binder domain or antecedent; a term-level `let` is
not an assumption. Repeated setup rows retain every assumption requirement.
Same-item context cannot cross item boundaries; inherited context requires
review. Admitting a parent vocabulary declaration does not admit a generated
surface declaration. Actual direct vocabulary use needs the corresponding
claim's admission. Structural nonvacuity checks are bounded defenses, not
proofs of existence or source fidelity.

## 6. Axioms, skeleton isolation and proofs

Intentional axioms need separate explicit approval, source rationale, reopening
condition and registered category/module/type. An unproved theorem cannot be
turned into an axiom or hidden behind a definition or wrapper. Actual
nonstandard kernel dependencies must match approved claim-to-axiom relations;
unused approved relations and unapproved dependencies fail acceptance. Kernel
standard axioms `propext`, `Classical.choice` and `Quot.sound`, and registered
direct proof holes have their separate defined
roles; imported unknown axioms are not silently accepted.

Final statement modules use their stable production paths from construction.
A dedicated skeleton umbrella reaches every registered statement leaf; the
production root reaches no unresolved statement. Its default Lake target must
resolve only registered production vocabulary at the registered physical paths.
The separate skeleton target must resolve all registered statements. Unsupported
build hooks, providers or targets fail closed under the Lean skeleton checker.

Global warnings remain errors. A local warning exception belongs only to its
exact registered unresolved proof stub, never a file, section or unrelated
completed proof. Diagnostic suppression is not a way to pass a source gate.
The elaborated environment must establish a bijection between registered
unresolved proof bindings and direct `sorryAx` uses; hidden/transitive-only holes
are rejected. Contract-only checks with empty statement tables are not a source
skeleton freeze. R5 discharges proof values while preserving primary statements
and exact proof types; its direct-hole count cannot increase. A theorem deletion
or weakened statement is not proof progress.

## 7. Verification and review authority

Repository-owned validation, derivation, public generation, transition selection,
regression execution and CI control have one Lean implementation. There is no
Python or Shell implementation exception, embedded body, or indirect escape
through a Lean wrapper. Before pinned Lean is available, only the minimal native
OS launch and transfer are permitted; existing Git, HTTP, archive, filesystem
and compiler operations remain thin IO primitives, with project decisions and
contracts owned by the typed Lean implementation.

Automation represents state with pure transformations, functional folds and
explicit-state recursion. Local imperative updates are not moved into reference
cells as a workaround. Ordered diagnostics, refusal conditions, fixture meaning
and the complexity of indexed data structures are preserved; IO handles the
necessary external effects.

Current-tree checks, regression tests, Lean builds and source review have
distinct scopes. Required checks use the shared `lake exe checker` entrypoint.
Current registries, generation, applicable semantic inspection and the actual
transition are always fresh. Independent regression groups may reuse only
verified successful-run evidence for identical actual reader inputs; unknown or
changed inputs execute the required groups. A global dispatcher identity is
separate from those input closures. Image build labels are audit provenance;
actual OS, architecture, native ABI, tool and compiler identities remain reuse
inputs. Parallel groups retain separate owned fixtures, bounded concurrency and
complete child cleanup; a failed group prevents acceptance and further batches.
Mathematical production builds depend on
their own source, configuration and dependency inputs, not an unrelated checker
change. Unchanged input evidence must cover the exact base and checkout;
unknown mathematical inputs require the build. Necessary checker compilation,
semantic imports and fixture builds are distinct work. Execution, verified reuse
and work not required are reported separately before execution. Reuse replaces
neither an actual transition nor source review. Failed, cancelled, skipped or
missing selected verification is not success. Implementation details and
negative cases live in the Lean checker and regression modules rather than a
duplicated execution specification here.

Source-claim fidelity, independent census observations, qualification strength,
atomicity and axiom approval require independent mathematical review. A build,
schema check, OID comparison or previous absence of findings proves none of
those judgments. Review evidence states its exact revision and bounded scope.

The rewrite trunk remains protected with strict up-to-date required job context
`verify` in workflow `rewrite-ci`; external protection is checked independently.
Only the user may authorize merge of an exact PR at its current exact head SHA
under `AGENTS.md`. CI/review success is not permission. Agents leave `USER ONLY`
unchecked; auto-merge, merge queue, direct trunk push and force push are forbidden.
