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

### Source notation and concrete mathematical types

Source presentation is not automatically a primary mathematical object. The
definition marker, context-dependent approximation signs, object-dependent
isomorphism sign and summation-filter typography in TASAKI2020 claims
0001/0002/0003/0005 are presentation conventions. Preserve their source records
without inventing a universal approximation relation, an untyped isomorphism or
a proposition whose only content is formatting. The vector, matrix, entry and
identity conventions in 0020/0021/0023 also name mathematical objects; they are
not excluded merely because typography helps identify those objects.

The following choices fix the implementation meaning of the remaining Symbols
entries. They specify source objects and usable interfaces, not the existence
of production declarations or completed primary bindings.

| Source claims | Mathematical interface |
| --- | --- |
| 0004 | Finite-set cardinality through `Finset.card`, or the cardinality of an explicitly finite subtype. The ambient vertex type need not be finite. |
| 0006 | Complex conjugation is `star` on a complex scalar. |
| 0007–0009 | A general site type `V`, a `SimpleGraph V`, its `edgeSet : Set (Sym2 V)` and `neighborSet`. Bonds are unordered distinct pairs; general graph vocabulary has no global `Fintype V` assumption. |
| 0010–0011 | The finite periodic hypercube has positive dimension and positive even side length. `Fin d → ZMod L` supplies periodic coordinates; `ZMod.valMinAbs` supplies representatives in the source's half-open centered cell. Nearest neighbors change one coordinate by one modulo `L`; ordinary distances between representatives do not silently replace periodic adjacency. |
| 0012 | Integer-coordinate length is the norm after embedding in `EuclideanSpace ℝ (Fin d)`, rather than the default norm on a function type. |
| 0013, 0020–0026 | Use finite complex matrices and Euclidean column vectors. Adjoint, transpose and entrywise conjugation are respectively `Matrix.conjTranspose`, `Matrix.transpose` and `A.map star`. The last operation is not matrix `star`. An outer product is `Matrix.vecMulVec u (fun j => star (v j))`; inner products conjugate the first argument. Matrix action uses `Matrix.mulVec`; determinant uses `Matrix.det` with its finite-index assumptions. |
| 0014–0015 | The spin construction below fixes positive half-integral spin, descending magnetic basis, local components and finite-site action. Total spin is the finite sum of site operators. Commutator, Casimir and spectral assertions retain their own source claims. |
| 0016–0017 | Finite-lattice one-particle spaces use `EuclideanSpace ℂ V` and `EuclideanSpace ℂ (V × Fin 2)`, with the two spin labels fixed consistently. |
| 0018–0019 | Creation and annihilation act on the full fermionic Fock space, including vacuum. Their restrictions change particle-number sectors; they are not endomorphisms of one fixed `H_N`. Number-preserving composites may restrict to a sector. The smeared creation operator is linear in the one-particle input, while annihilation is conjugate-linear. |

The hypercube correspondence uses the stated representative and periodicity
conditions; merely choosing `ZMod` does not prove the source equivalence.
Likewise, a Fock coordinate realization must specify its occupation basis and
sign convention before its CAR and sector maps are bound. A Clifford spin group
or a bosonic construction is not a substitute for these quantum-spin or
fermionic objects. Such subsequent constructions are not prerequisites for
defining the earlier site-spin matrices.

For the source's operator norm, use the Euclidean operator interpretation, such
as `Matrix.toEuclideanCLM`, or the explicitly selected
`Matrix.Norms.L2Operator` scope. An unspecified matrix norm can instead denote
an elementwise or different induced norm. No theorem may identify those norms
without the appropriate mathematical statement.

## 3. Capability, lifecycle and order

Global checker capability and each source's lifecycle are distinct, monotone
facts. The capability is recorded once in `phase.tsv`; each source's lifecycle
and its review reference live in that source's `sources.tsv` row. The source's
coverage label is derived from its lifecycle, rather than independently edited.
A new earlier-stage source may coexist with a completed later-stage
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

Pre-R4 empty relations do not need separate physical files. Their exact schemas
are declared in `Checker/RegistryLayout.lean`: slices, dependencies, bindings,
claim context, axioms, claim-to-axiom relations, statement modules and statement
imports. Only bootstrap, census and vocabulary phases admit an absent table as
an empty semantic view. If present, its schema and emptiness remain checked.
Skeleton and proof phases require all eight physical tables and their existing
membership, binding and semantic obligations. Absence never grants R4 acceptance.

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
are derived from the actual canonical corpus. The independently reviewed physical
page count, census OID and review reference remain frozen anchors in `sources.tsv`;
the checker recomputes the corpus digest and checks the page count against them.
Active, target, equation and empty-page counts are views, not separately edited
expectations. A source item's uniform publication format tag is supplied by its
schema and is not an individual mathematical review attestation. Classification
repairs do not rewrite original equation-item identity.

Historical Git snapshots retain their original file names, bytes and genuine
absence. Explicit historical readers preserve the older source state tables and
recorded counts, including invalid values needed for rejection. Current readers
require the compact source and item schemas and reject mixed old/new state.
Semantic views do not assert physical historical existence or rewrite ledger
prefixes. Only an explicitly owned regression-fixture factory may instantiate
the older test schema; that does not migrate a historical Git tree.

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

### Reviewed R3 extensions before statement freeze

An ordinary R3 change may replace an existing `mathlib_only` basis with
`project_vocabulary` only while both revisions have vocabulary capability and
the same valid pre-freeze source lifecycle. It retains the exact active source
claim, source metadata, lifecycle attestation and all seven correction ledgers.
The new independent review reference must be valid, fresh and non-placeholder.
The previously unused claim must acquire valid vocabulary admissions, including
a newly registered primary definition with exact type and value fingerprints.
Existing declarations, admissions, modules and imports retain their normal
monotonicity and identity checks. Review-reference-only changes, downgrades,
frozen-source changes, removed uses and concurrent source events do not qualify.

The actual ordinary transition runs native registry coverage and fresh semantic
vocabulary inspection whenever this exception is used. A plausible fingerprint
or a registry row alone is insufficient. This R3 admission records a reviewed
need for an existing definition; it does not claim that an unimplemented R4
primary already consumes that admission. R4 performs its separate actual-use
checks. The exception neither permits a partial production binding in vocabulary
phase nor changes any R4 freeze or proof rule.

### Spin construction interface

The first source-order need for a new spin operation is the site-spin notation
in CL-TASAKI2020-0014, also used by the early Heisenberg expressions. The concrete
construction is fixed by the single-spin basis and ladder formulas in
0041/0042 and the product-basis site action in 0097/0102. These source locations
supply the operator coefficients; they do not license importing a later
commutator or Casimir proof as an unregistered assumption. When R4 records an
actual later setup dependency, its independently reviewed `required_by` row
belongs to that later setup and points to the earlier consumer. Do not reverse
the row convention or add unused forward dependencies.

Use positive doubled spin `n : {n : Nat // 0 < n}`, so
`S = (n.val : ℝ) / 2`. The local coordinate space is
`EuclideanSpace ℂ (Fin (n.val + 1))`, ordered by magnetic quantum number
`σ_i = S - i.val`. For row `i` and column `j`, the raising matrix has entry

```text
P(i,j) = sqrt(S*(S+1) - σ_j*(σ_j+1))  if i.val + 1 = j.val,
         0                            otherwise.
```

The lowering matrix is `P.conjTranspose`. The three local components, in axis
order `0 ↔ 1`, `1 ↔ 2`, `2 ↔ 3`, are
`(P + P.conjTranspose)/2`,
`(P - P.conjTranspose)/(2*Complex.I)` and
`Matrix.diagonal (fun i => (σ_i : ℂ))`, with the stated real magnetic values
embedded in the complex scalars.
Use scalar multiplication for these matrix quotients. The finite index bounds
give the zero entries at the two ladder endpoints; spin zero is not admitted
by the source parameter type.
In the pinned Lean implementation, form the scalar two as `(1 + 1 : ℝ)` or
`(1 + 1 : ℂ)`; the intended operator declaration then needs no compiler-created
numeric proof declaration. This does not change the scalar or the source formula.

A single necessary composition, rather than aliases of the existing graph or
Euclidean APIs, has the following interface:

```lean
noncomputable def LatticeSystem.spinAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : {n : Nat // 0 < n}) (x : V) :
    Fin 3 → Matrix (V → Fin (n.val + 1)) (V → Fin (n.val + 1)) ℂ
```

For configurations `σ, τ`, its entry is the selected local component at
`(σ x, τ x)`, multiplied by the Kronecker deltas
`σ y = τ y` at all `y ≠ x`. This is the fixed product-basis coordinate
construction. Finiteness is imposed on this finite quantum system, not on the
general graph API. The corresponding Hilbert space is the Euclidean space on
the same configuration index; a plain function-space norm is not its norm.

The production implementation belongs in the separate registered leaf
`LatticeSystem.Vocabulary.Spin`, importing the required pinned complex,
square-root and matrix APIs and reached by the vocabulary umbrella. Register the fresh
`VO-LS-` identity in registry order, exact type/value OIDs, ordered direct
imports and the reviewed use for 0014. Its old source disposition and wording
remain fixed; the ordinary R3 review advance owns the changed basis and review
reference. Inspect the actual environment and run the mathematical default
build, current gates and ordinary transition. No-op source reclassification is
not a registration route. Self-adjointness, spin commutation, Casimir and
spectral identities remain separately bound assertions; the R3 definition is
not a proof of them. The informal introductory Hamiltonian sum does not fix
ordered-pair multiplicity or coefficients for a later exact model.

The source-order operation in 0015 is the total-spin triple. In the same
finite system and product basis, `LatticeSystem.totalSpin n axis` is the sum
`∑ site, spinAt n site axis`, as defined in (2.2.7). It is a sum rather than
an average, with no nonempty-site assumption; the empty sum is zero. It belongs
to the existing spin leaf and has its own reviewed vocabulary admission for
0015. This composition does not implement the total-spin square, its spectrum,
ladder operators or rotation operators, and does not certify their identities.
Its `explicit_finite_volume` scope is witnessed by the finite model carrier
`V` itself. That scope admits an explicit `Fintype` carrier or `Finset` volume
data; it does not impose finiteness on the general graph abstraction.

### Fermionic full-Fock coordinate operators

The one-particle spaces in 0016/0017 reuse `EuclideanSpace`; they do not
require project aliases. For 0018/0019 the finite-mode Fock coordinate space is
`EuclideanSpace ℂ (Finset M)`. In the spinful application `M = V × Fin 2`,
with `0` for up and `1` for down. The empty occupation is the vacuum, represented
by the existing `EuclideanSpace.single ∅ 1`. A fixed-particle sector uses the
occupations of that cardinality. Creation and annihilation act on the full
space, including the vacuum; they are not endomorphisms of one fixed sector.
The Euclidean norm supplies the one-particle and Fock norms. Neither the default
function-space norm nor an unspecified matrix norm is their substitute.

Choose and retain a linear order on the modes. It is a coordinate choice, not
an order prescribed by the source. The occupation vector for an increasing
sequence `a₁ < … < aₖ` has the creation-product convention
`c†(a₁) … c†(aₖ) |vac⟩`. The matrix row is the output occupation and the
column is the input. With `S` the input and `a` the created mode,
`fermionCreationAt a` has entry

```text
(-1) ^ #{b ∈ S | b < a}  if a ∉ S and row = insert a S,
0                       otherwise.
```

`fermionAnnihilationAt a` is its conjugate transpose in this same basis.
The two raw coefficient definitions need only `[LinearOrder M]`; the
finite-occupation count does not require the whole mode type to be finite.
Their use as full Euclidean Fock operators has the finite-carrier condition.
The raw matrices alone make no claim about an infinite Hilbert completion,
operator norm or basis independence.

Finite matrix multiplication and summation use `[Fintype M]`.
`fermionNumberAt a` is creation times annihilation, and
`totalFermionNumber` sums these over all modes, as in (9.2.29)/(9.2.33).
For arbitrary, unnormalized `φ : EuclideanSpace ℂ M`, the general smeared
operators in (9.2.46) are
`fermionCreation φ = ∑ a, φ a • fermionCreationAt a` and
`fermionAnnihilation φ = ∑ a, star (φ a) • fermionAnnihilationAt a`.
The complex conjugation on the latter coefficients is essential.

The fixed-spin operations `spinFermionCreation σ φ` and
`spinFermionAnnihilation σ φ` in (9.2.62) take
`φ : EuclideanSpace ℂ V` and sum only modes `(site, σ)`.
They require finite `V` and an explicitly chosen order on `V × Fin 2`,
shared with the underlying mode operators. No normalization assumption is
added, and no graph API acquires an order or global finiteness restriction.

These eight operations belong in the registered `LatticeSystem.Vocabulary.Fermion`
leaf. Reuse the pinned matrix, finite-set and Euclidean APIs. The raw creation
and annihilation coefficients have finiteness scope `none`; finite products
and sums have `explicit_finite_volume`.
The three site-mode operations are admitted by 0018, the fixed-spin pair by
0019, total number by 1617 and the general smeared pair by 1639.
Each changed basis review owns a new definition it needs. These registrations
do not reclassify those source records or constitute R4 dependency edges.
General CAR, adjoint/linearity identities, particle-sector maps and equivalence
with the antisymmetric wave-function representation retain their independent
exact-statement and proof obligations. Concrete occupation-entry checks do not
replace those obligations.

### Partial traces and reduced-density definition

The existing `LatticeSystem.partialTraceRight` sums the right coordinate and
returns a left-coordinate matrix; `partialTraceLeft` does the converse. Only
the traced index needs `Fintype` for each raw operation. Do not add global
finiteness to the other coordinate merely because the source application uses
two finite-dimensional factors.

For CL-TASAKI2020-2487/2488, both source factors are finite complex Hilbert spaces.
Choose their orthonormal bases explicitly; `OrthonormalBasis.tensorProduct`
gives the product basis. `LinearMap.toMatrix` and `Matrix.toLin` are the
coordinate/operator interfaces. The existing
`InnerProductSpace.toMatrix_rankOne` and
`InnerProductSpace.symm_toEuclideanLin_rankOne` give the rank-one matrix with
entries `ψ p * star (ψ q)`. The source inner product is linear in its second
argument.

The source input is normalized in the Hilbert norm. A usable composition is

```lean
noncomputable def LatticeSystem.reducedDensityMatrices
    {L R : Type*} [Fintype L] [Fintype R]
    (ψ : {ψ : EuclideanSpace ℂ (L × R) // ‖ψ‖ = 1}) :
    Matrix L L ℂ × Matrix R R ℂ
```

Its body uses a local
`A := Matrix.vecMulVec (fun p => ψ.val p) (fun p => star (ψ.val p))`
and returns `(partialTraceRight A, partialTraceLeft A)`, in that order.
The matrix calculation also makes sense for an arbitrary vector; its use as
the source's reduced-density pair retains the normalization subtype.
Normalization of a plain `(L × R) → ℂ` by its default norm would select the
wrong function-space norm. Coordinate normalization can instead be written
explicitly as `∑ p, Complex.normSq (ψ p) = 1`.

This one composed declaration may be placed in a registered reduced-density
leaf importing the existing quantum vocabulary and Euclidean APIs. The pure
outer product and coordinate conversions need no extra renamed wrappers.
The existing project-vocabulary basis of 2487/2488 permits the required fresh
admission through the ordinary registration rules after the source correction
is in its base. Keep source correction and the new production definition as
separate transitions.

The two outputs in (A.1.19) are a definition, not an extra assertion requiring a
new proof. Its future primary binding is a `definition_value` with no proof
metadata. The normalized-domain claim retains its own setup role and required
context. The definition alone does not certify basis independence, positivity,
unit trace, entropy or Schmidt identities. Those properties must not be added
as proof obligations of this definition or reported as already proved.
Current vocabulary-phase acceptance is distinct from constructing and freezing
the later R4 primary.

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
