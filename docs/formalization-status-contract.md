---
layout: default
permalink: /formalization-status-contract/
title: Formalization status data contract
---

# Formalization status data contract

Status: accepted prototype contract for Issue #5230. The version 1 catalogue has
`catalog_state: "prototype"` and is deliberately non-authoritative until the
governance cutover in Issue #5228.

## Decision

The project will maintain formalization status as versioned, source-first JSON
records under `formalization-status/v1/`. A dependency-free validator enforces
the contract. Human source pages, topic indexes, status summaries, and the
published machine aggregate will eventually be generated from those records.

During the prototype and catalogue-migration stages, the complete legacy
catalogue tree under `docs/formalization/legacy/` remains the authority named by
current project governance. The concise `docs/index.md` landing page is not a
status ledger. The prototype is evidence that the contract can represent
existing content; it is not a second status ledger. Issue #5228 must explicitly
change the authority chain after the catalogue is complete, publication is
deployed, and an audit finds no material discrepancy.

## Existing roles and consumers

The former monolithic `docs/index.md` combined several roles whose update and
consumption patterns differ. Issue #5227 moved them into the staged hierarchy:

| Former role | Information carried | Human consumers | Machine or workflow consumers | Problem |
|---|---|---|---|---|
| Landing page | Project purpose, scope, links, API-doc status | Site visitors, contributors | Jekyll Pages | Buried by a multi-thousand-line catalogue |
| Roadmap | Phase state, completed work, cumulative PR narrative | Maintainer | Agents selecting or reviewing work | Individual table cells have become historical logs |
| Theorem catalogue | Display name, statement summary, source location, Lean name, file | Readers and reviewers | Agents checking documentation coverage | Names are sometimes abbreviated or grouped and fields are embedded in prose |
| Status register | Proved, conditional, axiom, in-progress, and planned state | Readers | Review and audit agents | Vocabulary and axiom meaning are not closed or structurally checked |
| Capstone register | Which public results justify otherwise-unused declarations | Reviewers | Tier-1/tier-2 audits, currently by reading the Markdown | Capstone identity is inferred from prose rather than declared |
| Citation/provenance record | Edition, section, equation/theorem, pages, cross-check sources | Readers and mathematical reviewers | Documentation audits | Citation components are not independently addressable |
| Axiom/open-item register | Deferred mathematics, implementation gaps, completed TODOs | Maintainer | Review agents | Completed and current items coexist; dependencies are not linked to declarations |
| Change history | Deleted proof routes, PR-by-PR progress, stale markers | Maintainer investigating history | Occasional audits | Historical evidence competes with current status |

Other status-bearing surfaces are intentionally not replaced wholesale:

- `tex/proof-guide.tex` is authoritative for mathematical narrative and proof
  exposition. It also repeats citations, declaration names, and status claims
  that must be checked against the catalogue after cutover.
- Lean source is authoritative for declarations, declaration kinds, modules,
  statements, and actual axiom dependencies.
- `README.md` is a concise project introduction and points readers to the
  published project page. It is not a theorem-status database.
- `docs/refactoring-conventions.md`, `CLAUDE.local.md`, and agent instructions
  currently require the complete legacy catalogue tree to be consulted for
  documentation and capstone checks. Issue #5228 owns changing those consumers
  to validated structured records.
- `.github/workflows/lean_action_ci.yml` currently owns the Lean CI and records
  that doc-gen4 is disabled. Issue #5229 owns status-site generation and Pages
  publication; this contract does not edit workflows.
- Links in Lean comments, README, the proof guide, Jekyll configuration, and
  external sites are public-link consumers. Issue #5227 must preserve or
  redirect their relevant paths and anchors.

## Authority boundary

After Issue #5228 completes the cutover, authority is divided as follows:

| Subject | Authority after cutover | Derived or explanatory surfaces |
|---|---|---|
| Existence, kind, statement, and namespace of a Lean declaration | Lean source | Catalogue validation and generated pages |
| Formalization status, capstone flag, source-item association, topics, and declared axiom dependencies | Validated `formalization-status/v1/` records | Human source/topic pages and machine aggregate |
| Bibliographic identity and locator | `sources.json` and `source-items.json` | Citation text in generated pages |
| Mathematical motivation, derivation, and proof explanation | `tex/proof-guide.tex` and hand-written explanatory docs | Links from generated pages |
| Current and future project work | Tracking GitHub Issues and their synchronized mirrors | Roadmap summaries |
| Historical PR narrative and deleted approaches | Git history and designated history documents | Optional history views |

Generated files must contain a visible generated-file notice and must never be
edited by hand. Their generator input and generator version must be recorded in
the output. A mismatch is fixed in canonical input or the generator, not in a
generated view.

Until cutover, the first row above remains true, while formalization status and
capstone authority remain in the losslessly partitioned
`docs/formalization/legacy/` catalogue. Neither the landing page nor the JSON
prototype is authoritative. The manifest therefore requires `catalog_state`
and version 1 permits only `prototype` or `authoritative`.

## Directory and sharding model

```text
formalization-status/v1/
  schema.json
  manifest.json
  sources.json
  source-items.json
  topics.json
  records/
    <source-id>-<chapter-or-unit>.json
```

The manifest explicitly lists every registry and record shard. Directory scans
are forbidden as catalogue input: unlisted JSON is an error, and listed files
are processed in manifest order after that order is checked lexicographically.
This makes aggregate generation deterministic and prevents accidental files
from changing publication output.

The primary organization is source-first for literature-origin records.
`source_relations` gives typed edges to source items: `formalizes`, `presents`,
`attributes`, `supports`, or `cross_checks`. A literature-origin record has
exactly one `formalizes` or `presents` edge. Project-original foundations may
have no bibliographic edge and live in a shard whose `source_id` is `null`.
An implemented project-original record uses `not_applicable` source coverage;
an in-progress one uses `partial` under the general in-progress invariant.
Topic navigation is a generated projection over the canonical `topic_ids`;
there are no hand-maintained topic copies of records.

Relation semantics and ordering are closed:

| Relation | Meaning | Primary? | Order rank |
|---|---|---|---|
| `formalizes` | The declaration directly formalizes this source item | Yes | 0 |
| `presents` | This source presents or derives the selected result, or supplies the project's presentation or numbering, without a claim of direct formalization | Yes | 0 |
| `attributes` | This source explicitly attributes the result to an original work; it does not assert proof support | No | 1 |
| `supports` | This source supplies a proof, input, or supporting formulation | No | 2 |
| `cross_checks` | This source independently verifies the statement or convention | No | 3 |

Every literature-origin record has exactly one rank-0 relation: use
`formalizes` for a direct source formalization or `presents` when the selected
source presents the result used by the project but the declaration does not
directly formalize that source item. `attributes`,
`supports`, and `cross_checks` never satisfy that cardinality. Relations are
stored in canonical primary-first order by `(rank, source_item_id)`; the
validator rejects any other order. This retains readable provenance order while
keeping byte-stable records.

Shards are normally one source chapter, paper, or coherent source unit. Split a
large chapter by section only when reviewability requires it. Moving a record
between shards is non-semantic because its stable record ID does not change.

## Human publication topology

The stable canonical human route for a record is
`/lattice-system/formalization/records/<record-id>/`. The generator creates that
page only in the staged Jekyll tree; `docs/formalization/records/` is a reserved
generated-output root and must not contain committed placeholders. Each detail
page renders the complete record exactly once, including every canonical field
and every typed source relation in canonical order. The familiar human status
label is derived from the three machine dimensions and is explicitly display
data, not a fourth stored status field.

Source, topic, project-original, and status pages are compact projections. They
contain exact counts and ordered links to canonical record routes, but never a
second full record definition list. Missing source and topic pages are created
dynamically from the registries during staging, so adding future sources and
topics does not require committed marker placeholders. Existing hand-written
source/topic context remains outside its unique empty generated marker.
The route segments `index` and `foundations` are reserved for source IDs, and
`index` is reserved for topic IDs, because those names own the fixed index and
project-original pages. The semantic validator rejects those registry IDs
before generation; the generator independently rejects them at the output
boundary.

Every projection row has the exact record ID, canonical detail URL, and escaped
summary. Source membership is existential over typed relations to that source;
multiple relations still produce one row. Topic membership is the exact
`topic_ids` projection. Status membership is derived from the same closed human
label function used on detail pages. Rows are ordered by stable record ID. The
explicit fragment `record-<record-id>` remains on source and topic rows so the
four accepted prototype records retain their already published fragment
targets, while the full detail moves to the canonical record route.

The staged and rendered checkers require a bijection among catalogue record
IDs, generated filenames, permalinks, rendered directories, and full record
articles. They reject a full article outside its canonical detail page and
also reject stripped-identity definition lists, typed-field attributes, or
unknown record-like containers on projections. They reject an
extra or missing output, a path or permalink collision, a wrong projection
link, or any missing/extra/reordered projection member. These human-rendering
rules do not alter the version 1 manifest, canonical records, or machine API.

## Registry model

### Sources

A source is a bibliographic work. Stable ID, authors, and year are required.
Title, edition, publisher or journal metadata, and a persistent URL are recorded
when verified. A URL is optional and must use HTTPS when present. Optional
fields allow older sources to be represented without inventing metadata.

### Source items

A source item is a locatable unit within one source: theorem, proposition,
lemma, definition, equation group, exercise, section, or externally attributed
result. It has a stable ID and structured locators:

- `section` may be `null` for a whole article or otherwise unsectioned item;
- `item_kind` and `item_number` identify a numbered result or equation group;
- `pages` preserves printed pagination and may be `null` when unavailable;
- `equations` is an array because a result may span several equations;
- `title` gives a concise human label.

`item_number` may be `null` for unnumbered material. `equations` may be empty
when no equation locator applies. Locator strings reproduce the source's
printed form, are not parsed numerically, and preserve presentation order; for
example, `(4.1.9)` precedes `(4.1.10)` rather than lexical string order.

### Topics

Topics provide a controlled cross-navigation vocabulary. A topic has a stable
ID, label, and description. Topic IDs do not encode a documentation path.
Generated topic pages group records by these IDs.

## Declaration record

Each declaration record contains exactly these fields:

- `id`: stable catalogue identity, independent of Lean and file names;
- `lean_name`: fully qualified Lean constant name;
- `declaration_kind`: a closed Lean declaration-kind vocabulary;
- `implementation_state`, `source_coverage`, and `trust_state`: three
  orthogonal closed status dimensions defined below;
- `capstone`: an explicit Boolean, never inferred from references or prose;
- `summary`: short human-readable statement summary;
- `module`: fully qualified Lean module name;
- `source_path`: repository-relative `.lean` path defining the declaration;
- `origin`: `literature` or `project_original`;
- `source_relations`: zero or more typed provenance edges;
- `topic_ids`: one or more controlled topic IDs;
- `axiom_dependencies`: fully qualified non-standard axioms on which the
  declaration depends, sorted and duplicate-free;
- `proof_guide_anchor`: stable explanatory anchor or `null` while no suitable
  anchor exists.

The record ID is lowercase ASCII kebab case. It should describe the result,
usually with a source prefix, for example
`tasaki-2020-theorem-3-1-finite-dimensional-core`. It is immutable after
publication. A Lean rename changes `lean_name`, `module`, and `source_path` but
not `id`. If the mathematical identity changes materially, create a new ID and
retain an explicit supersession mapping in the next schema revision rather
than silently recycling the old ID.

Lean names must be fully qualified and begin with `LatticeSystem.`. Valid Lean
identifier segments may contain Unicode letters and apostrophes. Shorthand,
wildcards, brace families, and slash paths are rejected; generated Lean
`#check` remains the definitive name-resolution check. Supported declaration
kinds are `abbrev`, `axiom`, `class`, `definition` (`def` in source),
`inductive`, `instance`, `lemma`, `opaque`, `structure`, and `theorem`. The
module must match the source path (`LatticeSystem/Quantum/Foo.lean` becomes
`LatticeSystem.Quantum.Foo`). Source paths must exist, remain inside
`LatticeSystem/`, and may not contain `..`.

## Orthogonal status dimensions

| Dimension | Values | Meaning |
|---|---|---|
| `implementation_state` | `implemented`, `in_progress` | Whether the named Lean declaration is the intended implemented endpoint |
| `source_coverage` | `complete`, `conditional_reduction`, `partial`, `not_applicable` | How much of the cited source item the declaration represents; `not_applicable` is for project-original foundations |
| `trust_state` | `axiom_free`, `depends_on_documented_axioms`, `documented_axiom` | Whether project axioms occur in the declaration's trusted dependency boundary |

The dimensions are independent and machine-decidable. Ordinary theorem
hypotheses do not make a result “conditional.” For example,
`horsch_vonderLinden_lowLying` is an implemented, axiom-free proved theorem;
its `conditional_reduction` coverage records that it formalizes the
finite-dimensional core rather than Tasaki's separate long-range-order
estimate. `conditional_reduction` describes source coverage, not proof trust.

Human views derive familiar labels without storing an overlapping `status`:

| Machine combination | Human label |
|---|---|
| implemented theorem/lemma + axiom-free | proved |
| implemented theorem/lemma + documented-axiom dependencies | proved with documented axioms |
| implemented axiom + documented-axiom trust | documented axiom |
| implemented definition-like declaration | definition only |
| in-progress implementation | in progress |

Every documented axiom is an implemented `axiom` whose dependency list is
exactly itself. `axiom_free` requires an empty list;
`depends_on_documented_axioms` requires a non-empty list. In-progress records
are non-capstones with partial coverage. Planning stays in tracking Issues and
is not represented as a declaration record.

## Capstones and axiom dependencies

A capstone is a declaration that represents a review/audit endpoint for a
source result or major project result. It is a property of the catalogue record
and has no naming convention. A capstone must be implemented and have complete
or conditional-reduction source coverage.

Every project axiom dependency uses a fully qualified name. The list excludes
Lean's standard logical foundations such as `propext`, `Classical.choice`, and
`Quot.sound`; generated reports may show those separately. A documented axiom
lists itself, allowing the same dependency graph operation to identify its
downstream users. Each dependency must resolve to another catalogue declaration
whose kind is `axiom` and whose trust state is `documented_axiom`; nonexistent
or non-axiom dependencies are rejected. Lists are sorted and duplicate-free.

The Python validator checks source presence and declaration syntax. A stronger
Lean check generated from the records imports each module and issues both
`#check` and `#print axioms` for each declaration. Issues #5229 and #5228 must
make comparison of recurring generated `#print axioms` output with declared
dependencies a CI/audit gate before authoritative cutover and continue it after
cutover. This is a recurring consistency check, not a one-time migration audit.

## Manifest, deterministic output, and canonical JSON

All JSON files are UTF-8 without a byte-order mark, use LF line endings, end in
one newline, use two-space indentation, sort object keys lexicographically, and
contain no insignificant trailing spaces. Arrays whose order is not semantic
are sorted and duplicate-free. The validator reparses and reserializes every
file to enforce byte-for-byte canonical JSON.

Strings rendered inline in generated human views are non-empty, single-line
text. The schema and semantic validator reject CR, LF, C0/C1 control
characters, and DEL in record summaries, source metadata, source-item locator
strings and titles, equations, and topic labels/descriptions. Stable IDs,
enums, Lean names, and module/path patterns already impose stricter grammars.

`manifest.json` declares:

- `schema_version: 1`;
- `catalog_state` (`prototype` until #5228, then `authoritative`);
- the registry paths;
- an explicit sorted `record_shards` list;
- optional paired fixed `cutover_baseline` and `cutover_certificate` paths,
  which can only name `cutover-baseline.json` and
  `cutover-certificate.json` and are mandatory in authoritative state;
- the stable human and machine publication roots.

The deterministic aggregate records `catalog_state`, `generated_by`,
`generator_version`, `input_sha256`, `records`, `schema_version`,
`source_items`, `sources`, and `topics`; every aggregate array is sorted by
stable ID. `input_sha256` hashes the canonical manifest first, followed by its
listed canonical inputs (schema, registries, then explicitly listed shards),
followed by the cutover baseline and certificate when owned, all with path
framing. Present/absent and order regressions are tested independently. The
generated aggregate is not a manifest input, so no
self-reference arises. Including the manifest ensures `catalog_state`, shard
ownership, and publication-root changes alter the digest. Repeated generation
from unchanged inputs must produce identical bytes. Prototype records are included only when
`catalog_state` is `prototype`; consumers must expose that state and must not
treat the aggregate as authoritative.

Validation has two required layers. JSON Schema draft 2020-12 is the portable
structural contract: types, required and unknown fields, enums, patterns, and
representable conditional implications. The dependency-free Python validator
evaluates the schema subset used by this catalogue against every canonical
instance and generated aggregate. Its separate semantic and canonical checks
cover byte format, manifest ownership, ordered locators, safe repository paths,
Lean source declarations, provenance cardinality, cross-record axiom
resolution, and deterministic output. Neither layer replaces the other. The
startup parity check is deliberately narrower than structural validation: it
guards constants and conditional rules duplicated by semantic code or the
generator, while closed vocabularies and patterns are derived from the schema.

## Cutover baseline and staged governance draft

The optional `cutover-baseline.json` is historical coverage evidence, not a
second status database. It reconstructs exactly 2,052 catalogue rows from
`docs/index.md` at commit
`6519099024bf156b87ac0c807c6633c513792581`. Every row stores its ordinal,
former source line, exact UTF-8 row SHA-256, one closed outcome, and sorted
mapped record IDs. It also stores the exact backtick declaration references
extracted from the former first table cell. A `mapped` row maps one or more
exact structured records and has no disposition; normal mappings must bind the
record's exact Lean leaf name to one of those references, including the audited
unambiguous single brace or slash groups, comma-separated cells, and
multiple-backtick references. A single reference containing more than one
group is never assigned Cartesian, zipped, paired, or cyclic semantics by the
checker. The exact
first-cell text, text outside backticks (including literal `etc.`), and derived
closed grouping-syntax tags are also pinned. Mechanically expandable groups
require equality between the complete expanded leaf set and the coverage set;
mapping only the first member is rejected. A row may bind exact retired
declaration evidence: its complete expected legacy set must equal the
disjoint union of current mapped leaves and certified retired leaves. Mixed
rows remain `mapped` and must retain at least one current record. A pure-retired
row uses the closed `retired` outcome, no current record IDs, and the
`retired_declarations` disposition. A `not_a_declaration` row
maps none and uses only the closed
`non_declaration` disposition. Such a row is accepted only when its exact
legacy cell has no declaration reference and its ordinal occurs in the paired
certificate. A free-form explanation or `waived` disposition cannot turn a
declaration-bearing row into a non-record. This permits grouped Markdown rows to expand without
pretending that every historical table entry was one Lean declaration.

The baseline also stores sorted, disjoint `cutover_record_ids` and
`non_legacy_record_ids`. The former is exactly the union of all row mappings
and the latter. Normally a record already present in the prototype maps to its
legacy row; prototype age is not an exemption. At cutover every cutover ID must
exist in the validated catalogue. After cutover, new records may be added
without rewriting historical evidence, but deletion of any cutover ID remains
an error. The cutover checker and validator share the exact pinned-row
reconstruction while retaining separate manifest/catalogue entry points.
The validator names the four records published by the accepted prototype and
requires each to occur in a legacy-row mapping rather than the non-legacy set.

For grouping syntax such as plain `etc.`, wildcards, legacy abbreviations,
multiple groups in one reference, declaration signatures with arguments, or
prose/symbolic backtick tokens that cannot be expanded deterministically as
Lean identifiers, the certificate stores the row
ordinal, exact row hash, and the complete sorted fully qualified expected Lean
names. Those names must equal the mapped and certified-retired declarations
bidirectionally and must also equal an independently audited, code-pinned set
for that ordinal. The baseline and certificate therefore cannot self-certify a
different interpretation by changing both mappings and expected names together.
An exceptional ordinal absent from the code-pinned evidence is rejected. Future
migration PRs must deliberately extend that reviewed table as they add audited
non-mechanical mappings. Such an exception is rejected for a nongrouped row,
and unused or missing exceptional entries are errors.

Retirement is not a free-form escape from coverage. Each certificate entry
binds one exact row hash, ordinal, legacy leaf, former fully qualified Lean
name, former `LatticeSystem/**/*.lean` path, and a
40-hex deletion commit plus a nonempty reason. The validator proves that the
commit is in current history, changes that exact path, the parent version
declares the exact fully qualified name, the commit version removes it (or the
file), and the current Lean tree and current catalogue no longer declare it.
The shared source inventory tracks nested namespaces, leading attributes, and
declaration modifiers rather than relying on terminal-name substring scans.
Optional sorted replacement record IDs must exist. Entries are sorted and unique
by ordinal/leaf; wrong-row, survivor, fabricated-history, overlapping-current,
missing, extra, and unused retirement evidence is rejected. This model applies
uniformly to any number of absent historical leaves, including mixed rows whose
other declarations survive.

The paired certificate hashes the exact canonical baseline bytes, the sorted
cutover-ID projection, and the complete ordinal/outcome/disposition/mapping/row
hash projection. It also freezes the sorted non-record and exceptional-mapping
ordinal/name evidence and the complete deletion-history evidence. While the catalogue remains a prototype, introducing
this pair
is a freeze gate: the current record-ID set must equal `cutover_record_ids`, so
an omitted current record is rejected. The atomic cutover PR must pin the
canonical certificate's SHA-256 in the validator while changing state to
`authoritative`. Thereafter the certificate fingerprint is independent of the
editable baseline fields: shrinking cutover IDs, remapping rows, or replacing
the certificate fails. Authoritative catalogues may add post-cutover records,
but must retain every certified cutover ID. Changing the pinned fingerprint is
an explicit new audited cutover, not routine catalogue maintenance.

JSON Schema keeps both manifest evidence fields structurally optional because
prototype catalogues before the freeze own neither file. Runtime semantics
require the pair together and require both in authoritative state; schema
conditional tests and runtime state-transition tests cover that deliberate
division.

The post-cutover authority and theorem-PR rules are staged here for review but
do not take effect while `catalog_state` is `prototype`:

1. Lean source owns declaration existence, kind, statement, namespace, and
   actual axiom closure.
2. Validated manifest-owned records own formalization status, capstone identity,
   provenance, topics, and declared non-standard axiom dependencies.
3. Generated human and machine views are publication artifacts and are never
   edited as status input.
4. `tex/proof-guide.tex` and hand-written explanatory pages own mathematical
   motivation and proof narrative; they may repeat names and citations for
   exposition, but do not own progress state.
5. Tracking Issues and synchronized mirrors own current/next work. Designated
   history pages and Git history own historical narrative.

After the atomic authority flip, every theorem PR updates its canonical record
and registries/shards when needed, runs schema, exact Lean-axiom, cutover,
generation, and rendered-view gates, and updates the proof guide for the
required mathematical exposition. Generated views remain uncommitted. Until
that flip, theorem PRs continue to update the complete legacy catalogue and
the proof guide under the existing repository rules.

## Publication contract for Issue #5229

Issue #5229 will implement, but may not silently alter, this interface:

- Pull requests validate canonical inputs and build the complete publication
  artifact without deploying it.
- Merges to `main` deploy through exactly one Pages deployment owner with
  deployment permissions scoped to that job.
- The stable human root is `/lattice-system/formalization/`.
- The stable versioned machine aggregate is
  `/lattice-system/formalization-status/v1/catalog.json`.
- The versioned schema is
  `/lattice-system/formalization-status/v1/schema.json`.
- A convenience pointer such as
  `/lattice-system/formalization-status/latest/catalog.json` may be additive,
  but versioned clients must not depend on it.
- Human source pages are source-first; topic pages are generated indexes over
  the same records. They display schema version, input SHA-256, catalogue state,
  and the deploy revision supplied separately by CI. Deploy revision is runtime
  publication metadata and is not part of the canonical aggregate digest.
- Build output is reproducible from the checked-in records and repository
  scripts. CI must not fetch an undeclared generator dependency.
- The job records wall-clock cost and artifact size. Status publication must be
  evaluated separately from doc-gen4 and must not restore or invoke doc-gen4.

The published machine path is an API contract. Removing fields, changing field
meaning, weakening ID stability, or changing status-dimension semantics requires a new
major directory (`v2`). Adding optional output fields may be additive, but
checked-in canonical input remains strict: the schema and validator must be
updated together before a new field appears.

## Versioning and compatibility

Within `v1`, these are additive changes:

- adding sources, source items, topics, shards, or records;
- adding a new optional generated-view field whose absence has defined meaning;
- adding publication formats that do not change existing stable URLs.

These are breaking changes and require `v2`:

- deleting or reusing a published stable ID;
- changing the meaning of a status dimension, capstone, or axiom dependency;
- making a required field optional or changing its type;
- changing source-item identity so that a record refers to different
  mathematics;
- removing or repurposing a stable machine URL.

Corrections to spelling, summaries, locators, Lean names after a code rename,
and module paths are compatible when stable identity and mathematical meaning
remain unchanged. Reviews must call out citation corrections explicitly.

## Validation and review gates

`python3 scripts/validate_formalization_status.py` uses only the Python standard
library and checks:

- canonical JSON encoding and explicit manifest ownership;
- generic evaluation of the used JSON Schema subset and strict object keys;
- version, orthogonal status dimensions, stable-ID, uniqueness, and array rules;
- fully qualified Lean names, module/path correspondence, namespace-aware
  source declaration syntax, and an authoritative generated Lean assertion
  that each imported declaration belongs to its recorded defining module;
- source, source-item, topic, typed provenance, and source-origin integrity;
- implementation/coverage/trust, kind, capstone, and resolved-axiom invariants;
- representative prototype coverage across at least two Tasaki chapters and
  a typed non-Tasaki relation, with a proved capstone and a documented axiom;
- deterministic aggregate generation and input digest.
- inline-render safety for every human-view field, including newline and
  control-character regressions.
- optional strict cutover-baseline structure, exact pinned hashes and row
  outcomes, mapping/non-legacy disjointness and reachability, and immutable
  cutover-record retention; authoritative state requires that evidence.

The current prototype exercises non-Tasaki data through the Nielsen--Chuang
cross-check of the Tasaki Pauli presentation, Tasaki's attribution of Theorem
4.2 to Shastry, and a source-first Shastry 1992 record whose primary `presents`
edge is narrowly located to the static-susceptibility argument on pages
L249--L253. That record has `partial` source coverage: it documents the Lean
axiom's provenance without claiming that the whole article, or every detail of
its argument, has been formalized. Tanaka--Takeda--Idogaki supplies a supporting
rigorous formulation. The prototype does not claim comprehensive coverage of
either non-Tasaki paper.

`--emit-aggregate PATH` writes the canonical aggregate to a repo-local scratch
path for reproducibility checks. `--emit-lean-check PATH` writes a temporary
Lean file importing the referenced modules, asserting each declaration's
defining module through `Lean.Environment.getModuleIdxFor?`, and running
`#check` and `#print axioms` for every name. `--self-test` runs committed dependency-free
positive, negative, name-grammar, status-exclusivity, equation-order,
dependency-resolution, schema-evaluation, parity, and path-escape regressions. Generated scratch belongs
under `.self-local/tmp/` and is not committed.

A catalogue-changing PR must run the validator with `--self-test`, parse every
JSON file with `python3 -m json.tool`, run the generated Lean checks, run
`git diff --check`, and inspect changed public links. The validator's built-in
schema evaluator is mandatory. CI may additionally use an already-declared
general JSON-Schema engine, but no dependency may be installed implicitly;
#5229 must make any additional engine an explicit dependency decision.

## Migration map

| Issue | Inputs from this contract | Owned result | Exit condition relevant to the next issue |
|---|---|---|---|
| #5227 | Source-first model, topic projection, authority boundary, stable human root | Split human hierarchy, preserve/redirect relevant existing links and anchors, and move interim Markdown authority losslessly to the legacy catalogue tree | Human navigation reaches the complete legacy catalogue without duplicating status truth |
| #5229 | Manifest, validator, deterministic aggregate, stable URLs, CI publication contract | PR build/validation, recurring `#print axioms` comparison, and `main` deployment of human and machine artifacts | One deployment owner; stable artifacts published with digest/revision metadata; cost recorded; doc-gen4 remains disabled |
| #5228 | Closed statuses, explicit capstones, ID/rename rules, authority table, all generated/audit surfaces | Full catalogue migration, discrepancy audit, consumer/governance cutover | Prototype becomes authoritative only after complete coverage and audited agreement |

The migration is deliberately staged and reversible. #5227 and #5229 may use
the prototype as fixture data but must label it non-authoritative. #5228 imports
the complete catalogue, resolves discrepancies against Lean and the existing
index, changes `catalog_state`, and updates governance consumers in one reviewed
cutover.

## Non-goals and cost boundary

This contract does not split the full index, deploy Pages, rewrite the proof
guide, change Lean proofs, restore doc-gen4, or introduce a dependency. The
prototype validator uses only an already available Python 3 runtime and Lean
through the existing `lake` environment. CI generation must stay materially
cheaper than doc-gen4; #5229 must measure rather than assume that property.
