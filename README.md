# LatticeSystem

This branch is a from-scratch, multi-source implementation of mathematical
physics claims. R3 is complete for the first source, Hal Tasaki's quantum
many-body systems book: the production tree contains
the two partial-trace vocabulary definitions required by the frozen corpus,
but **zero source-claim theorem statements or proofs**. The former
implementation is not an API or source for this rewrite.

The recorded census, lifecycle, and vocabulary review do not certify that
normalized claim statements match the printed source. The full rendered-source
re-audit and reviewed content corrections remain incomplete.

The canonical plan and gates are in [DESIGN.md](DESIGN.md). Machine-readable
progress begins in `registry/`. Its global checker capability is `vocabulary`,
while each source advances independently through `source-progress.tsv`;
`TASAKI2020` is `vocabulary_reviewed`. Its corrected corpus ledger contains all
534 physical PDF pages, 3,182 active atomic claims, 3,171 formalization
targets, 1,401 unique equation-label/page pairs, and 63 pages with no claim.
Eight superseded records preserve the provenance of compound or duplicate
claims, while eleven active records are explicitly classified `out_of_scope`. The only
production Lean tree is limited to the registered vocabulary modules and their
root. Checker cases are generated only under isolated system temporary roots;
the repository contains no tracked fixture tree.

The complete R3 review classifies all 3,171 formalization targets: 3,169 are
`mathlib_only`, while claims `CL-TASAKI2020-2487` and
`CL-TASAKI2020-2488` require project vocabulary. The registered vocabulary is
exactly `partialTraceRight` and `partialTraceLeft`, with four claim-to-vocabulary
links recording the complete relation. Their type and declaration OIDs are
frozen, and the static registry, import graph, and Lean-environment checks pass.

Tracks and sources have stable positions, bibliographic metadata, fingerprints,
independent lifecycle, and per-source frozen census invariants. Global claim
order is `(track position, source position, claim order key)`, so additional
books and papers can be registered without weakening completed-source gates.
Reviewed correction events are recorded by permanent ledgers. The normalization
event retains its 36 statement-readiness reviews, 22 corrective actions,
23 ordered successor relations, and one event-owned source-item addition.
A separate content-fidelity event records one review and one correction to
equation (4.1.42), preserving its claim identity and the census counts. The dedicated
transition checker derives the corrected counts and census OID from the corpus
and rejects cross-source ownership, unmanifested registry drift, contentless
surrogates, axiom or R4 artifacts, and incomplete successor propagation.
Historical event-owned rows are frozen exactly, while a later independently
reviewed event may append rows with its own contiguous positions.
The sixth ledger, `claim-content-amendments.tsv`, now records that one
reviewed pre-R4 content correction, including actual old and new content hashes,
the frozen source-page hash, and event ownership. The reviewed source unit
recovers the complex spectral estimate and its surrounding conditions;
it does not certify a proof, other claims, or the complete source corpus.
The broader rendered-source re-audit and further corrections remain incomplete.
The same permanent protocol supports independently reviewed additions of
previously omitted atomic claims, with fresh IDs, frozen page provenance,
item and vocabulary ownership, and derived census invariants. This capability
does not itself add a source claim or certify source coverage.
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
`01bcb49d49db92c225cfa74b74d409dd0a9c4edc`. The rewrite excludes the old Lean,
documentation, TeX, status data, scripts, and workflows, including archives
and compatibility shims. Only `lean-toolchain` and `lake-manifest.json` are
byte-preserved from that anchor. Private reference material remains outside
the tracked rewrite tree.

## Hard merge gate

Every rewrite PR requires the user's explicit permission to merge the exact PR
number at its current exact head SHA. Green CI, review approval, prior consent,
or permission for another SHA is not merge authority. Any head change expires
permission. Auto-merge, merge queue, direct push to the protected trunk, and
force push are forbidden. The agent must never check the `USER ONLY` box.
