# LatticeSystem

This branch is a from-scratch, multi-source implementation of mathematical
physics claims. R3 is complete for the first source, Hal Tasaki's quantum
many-body systems book: the production tree contains
the two partial-trace vocabulary definitions required by the frozen corpus,
but **zero source-claim theorem statements or proofs**. The former
implementation is not an API or source for this rewrite.

The canonical plan and gates are in [DESIGN.md](DESIGN.md). Machine-readable
progress begins in `registry/`. Its global checker capability is `vocabulary`,
while each source advances independently through `source-progress.tsv`;
`TASAKI2020` is `vocabulary_reviewed`. Its corrected corpus ledger contains all
534 physical PDF pages, 3,176 active atomic claims, 3,166 formalization
targets, 1,401 unique equation-label/page pairs, and 63 pages with no claim.
Eight superseded records preserve the provenance of compound or duplicate
claims, while ten active records are explicitly classified `out_of_scope`. The only
production Lean tree is limited to the registered vocabulary modules and their
root. Checker cases are generated only under isolated system temporary roots;
the repository contains no tracked fixture tree.

The complete R3 review classifies all 3,166 formalization targets: 3,164 are
`mathlib_only`, while claims `CL-TASAKI2020-2487` and
`CL-TASAKI2020-2488` require project vocabulary. The registered vocabulary is
exactly `partialTraceRight` and `partialTraceLeft`, with four claim-to-vocabulary
links recording the complete relation. Their type and declaration OIDs are
frozen, and the static registry, import graph, and Lean-environment checks pass.

Tracks and sources have stable positions, bibliographic metadata, fingerprints,
independent lifecycle, and per-source frozen census invariants. Global claim
order is `(track position, source position, claim order key)`, so additional
books and papers can be registered without weakening completed-source gates.
The reviewed correction event is recorded by three permanent ledgers for the
event, its 23 actions, and the 23 ordered successor relations. The dedicated
transition checker derives the corrected counts and census OID from the corpus
and rejects unmanifested registry drift, contentless surrogates, axiom or R4
artifacts, and incomplete successor propagation.
CI selects this exceptional transition only while the event is new and its
recorded base equals the actual merge base. Later pull requests automatically
use the ordinary immutable base-diff path.
The public catalog at [docs/index.md](docs/index.md) is generated from reviewed
source items and includes source/section labels, claim summaries, Lean binding
status, vocabulary, axioms, and links without publishing private source data.

## Local checks

```sh
scripts/check-all.sh
lake build
```

These commands use the already pinned toolchain and dependencies. They enforce
the frozen census shape but cannot independently establish that human readers
identified every mathematical claim or that a claim is mathematically correct.

## Reset boundary

The legacy anchor is
`01bcb49d49db92c225cfa74b74d409dd0a9c4edc`. The reset is intentionally one
atomic PR: old Lean, documentation, TeX, status data, scripts, and workflows
are deleted rather than archived or shimmed. Only the dependency pins are
byte-preserved. `.self-local/refs` is private reference material and is not
part of the tracked rewrite tree.

## Hard merge gate

Every rewrite PR requires the user's explicit permission to merge the exact PR
number at its current exact head SHA. Green CI, review approval, prior consent,
or permission for another SHA is not merge authority. Any head change expires
permission. Auto-merge, merge queue, direct push to the protected trunk, and
force push are forbidden. The agent must never check the `USER ONLY` box.
