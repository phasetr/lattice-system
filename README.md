# LatticeSystem

LatticeSystem is a from-scratch, multi-source formalization of mathematical
physics. The current production capability is `vocabulary`; the first source,
Hal Tasaki's *Physics and Mathematics of Quantum Many-Body Systems*, is recorded
as `vocabulary_reviewed`. The production Lean tree contains two partial-trace
definitions and no source-claim statements, proofs or intentional project axioms.

The recorded census and R3 vocabulary review do not establish that every
normalized claim faithfully represents the printed source. Bounded corrections
have been integrated, but the full rendered-source audit, exact-statement
skeleton and source-claim proofs remain incomplete.

## Authority and current state

[DESIGN.md](DESIGN.md) defines the contracts and acceptance boundaries.
`registry/phase.tsv` records global checker capability;
`registry/source-progress.tsv` records each source's lifecycle. Registries
record identities, classifications, provenance and review relations. The Lean
environment establishes which declarations exist and their types.

The current work and single next action are maintained in
[Issue #5479](https://github.com/phasetr/lattice-system/issues/5479), checked
against the actual branch, commit and registries. Open PRs do not change the
production contract until integrated. Completed correction details belong in
the permanent correction ledgers and their reviewed evidence, rather than a
second progress history here.

The current TASAKI2020 registry records:

| Measure | Count |
| --- | ---: |
| Physical PDF pages | 534 |
| Active claim records | 3,250 |
| Formalization targets | 3,224 |
| Active `out_of_scope` records | 26 |
| Historical tombstones | 23 |
| Reviewed source items | 3,076 |
| Distinct equation source-label/page pairs | 1,392 |
| Pages with no active claim | 63 |
| Mathlib-only formalization targets | 3,222 |
| Targets requiring project vocabulary | 2 |
| Registered vocabulary declarations | 2 |
| Claim-to-vocabulary links | 4 |

A formalization target is active and not `out_of_scope`. Equation-pair counts
use active claims with subkind `equation`; classification repairs preserve the
original equation source items. Per-source counts and census fingerprints are
recorded in `registry/source-invariants.tsv`.

## Implemented Lean vocabulary

The three registered production modules are the root `LatticeSystem`, the
`LatticeSystem.Vocabulary` umbrella, and
[`LatticeSystem.Vocabulary.Quantum`](LatticeSystem/Vocabulary/Quantum.lean).
The leaf defines exactly these operations on complex matrices:

| Declaration | Finite index required | Input and result |
| --- | --- | --- |
| `LatticeSystem.partialTraceRight` | `[Fintype Right]` | `Matrix (Left × Right) (Left × Right) ℂ` → `Matrix Left Left ℂ` |
| `LatticeSystem.partialTraceLeft` | `[Fintype Left]` | `Matrix (Left × Right) (Left × Right) ℂ` → `Matrix Right Right ℂ` |

Each operation sums over the indicated index; the other index has no `Fintype`
assumption. Their type and declaration OIDs and ordered direct imports are
registered and checked against the elaborated environment. The two target
claims requiring project vocabulary are `CL-TASAKI2020-2487` and
`CL-TASAKI2020-2488`.

R3 basis and use relations record the need for existing vocabulary. They do
not certify a closed typed physics contract, source fidelity, statement binding
or proof. Graph-based modeling is a design requirement for later work; no
production graph, Hamiltonian or state API has been added. Production bindings,
statement modules, contexts, axioms, dependencies and implementation slices
remain header-only. The separate `Checker/` metaprograms and runtime fixtures
exercise future skeleton contracts without adding production source claims.

## Source corrections and public catalog

The six permanent correction ledgers record reviewed events, normalization
reviews, corrections, successors, item additions and content amendments.
[DESIGN §7](DESIGN.md#7-atomic-claim-registry) defines their immutable history,
source-atomic identity, item ownership and pre-R4 eligibility. Ordinary changes
use the frozen base-diff path; a new correction event uses the dedicated guard
only when its exact recorded base matches the verified merge base. A later
change cannot reopen that exception. Each source correction needs its own
source review and acceptance.

The [public catalog](docs/index.md) is generated from stable source-item and
claim metadata. It shows labels, locators, classifications, vocabulary use and
binding/proof status. It omits normalized source claim text, private paths,
source fingerprints and content OIDs. `vocabulary_ready`, `not_bound`,
`not_recorded` and `not_assessed` are distinct from source or proof acceptance.
Generate and check the complete catalog with
`scripts/generate-public-docs.py`; generated files are not edited by hand.

## Checks

The current production full checker and build entrypoints are:

```sh
BASE_REF=origin/rewrite-main scripts/check-all.sh
lake build
```

`check-all.sh` runs structural and registry checks, the applicable vocabulary
and skeleton semantic gates, generator tests and drift checks, checker runtime
fixtures, and the base-diff selector. The workflow `rewrite-ci` runs on pushes
and pull requests, with required job context `verify`. Its existing hosted
entrypoint and branch protection remain in force; unmerged CI changes are not
the current production procedure.

These checks use the declared toolchain and dependencies. Structural checks,
builds and OID comparisons do not prove source fidelity, absence of omissions
or mathematical correctness. Source, implementation and verification reviews
must state their exact revision, scope and any untested boundary.

## Reset boundary

The legacy anchor is `01bcb49d49db92c225cfa74b74d409dd0a9c4edc`.
Legacy Lean, documentation, APIs, proofs and scripts are not reused. Only
`lean-toolchain` and `lake-manifest.json` are byte-preserved from that anchor.
Private reference material remains outside the tracked rewrite tree.

## Hard merge gate

Every rewrite PR requires the user's explicit permission to merge the exact PR
number at its current exact head SHA. Green CI, review approval, prior consent,
or permission for another SHA is not merge authority. Any head change expires
permission. Auto-merge, merge queue, direct push to the protected trunk and
force push are forbidden. Agents must leave the `USER ONLY` box unchecked.
