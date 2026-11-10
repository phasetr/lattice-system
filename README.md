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
534 physical PDF pages, 3,190 active atomic claims, 3,179 formalization
targets, 1,401 unique equation-label/page pairs, and 63 pages with no claim.
Eight superseded records preserve the provenance of compound or duplicate
claims, while eleven active records are explicitly classified `out_of_scope`. The only
production Lean tree is limited to the registered vocabulary modules and their
root. Checker cases are generated only under isolated system temporary roots;
the repository contains no tracked fixture tree.

The vocabulary reviews classify all 3,179 formalization targets: 3,177 are
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
A setup-unit event records seven statement-readiness reviews, one amendment
that makes the local model conditions explicit, and one previously omitted
atomic claim about the sublattice cardinalities. It introduces a fresh claim and
source item without a predecessor or successor, deriving the revised census
invariants from the corpus. A symmetry/order-operator event records seven
statement-readiness reviews and three identity-preserving amendments restoring
the eigenphase factor, finite-system Taylor context, and distinct component
conditions. A theorem-core event records six statement-readiness reviews,
one amendment to the rotation conditions, and a separately omitted finite-volume
positivity assertion. A ferrimagnetic statement/model event records ten
statement-readiness reviews and adds the omitted squared-order symmetry
assertion to an existing source item, preserving all nine existing claim records
and the item's metadata and first relation. Its printed proof context remains
outside that statement/model scope. A proof-context event records two local
context normalizations. Its J>0 guard on the intermediate chain is interpretive
and unprinted. The separate balanced case preserves the main theorem's range,
and every original chain term remains unchanged. This scoped normalization
does not certify the printed proof, a Lean proof, or the full source audit.
An infrared-bound model/Fourier setup event records eleven statement-readiness
outcomes: two context amendments, two omitted orthogonality assertions in one
genuine named footnote item, and seven unchanged records. Each new assertion
has its own creation correction and review; the first claim's correction owns
the shared item. The unit includes the immediate explanation after equation
(4.1.23) and ends before (4.1.24), without certifying the later bound or proofs.
An infrared-bound statement/application event records fourteen statement-readiness
outcomes: one context amendment, three previously omitted assertions, and ten
unchanged records. It restores the bound's admissible energy constant and
nonordering-momentum domain, and records full-integral finiteness, the reported
numerical bound positivity, and the one-dimensional integral divergence. The
three additions retain their separate sentence or named-footnote provenance.
The unit includes the attached application footnotes and ends before the printed
derivation; it does not certify numerical evaluation, proofs, or R4 readiness.
The sixth ledger, `claim-content-amendments.tsv`, records eleven reviewed pre-R4
amendments, including actual old and new content hashes,
frozen source-page hashes, and event ownership. The reviewed units cover the
complex spectral estimate, opening model setup, symmetry/order-operator unit,
Theorem 4.1 core, ferrimagnetic statement/model block, the separately bounded
ferrimagnetic proof-context unit, infrared-bound model/Fourier setup, and the
infrared-bound statement/application unit; they do not certify proofs, other source
units,
or the complete source corpus. The broader
rendered-source re-audit and further corrections remain incomplete. The same
permanent protocol supports independently reviewed additions with fresh IDs,
frozen page provenance, and explicit item and vocabulary ownership.
Multiple independently created omissions may share one genuinely new item:
the position-1 claim's correction owns the item, while every member retains
its own same-event creation review and unique item relation. Split-created
items retain single-correction ownership, and historical metadata stays frozen.
This capability does not add a production claim or certify another source unit.
CI selects this exceptional transition only while the event is new and its
recorded base equals the actual merge base. Later pull requests automatically
use the ordinary immutable base-diff path.
R4 checker infrastructure registers statement-module imports and reviewed
claim contexts, and compares typed declarations, proof-hole ownership and
actual axiom use with their registries. Its runtime cases exercise these
contracts without adding production statements. The production binding and
statement tables are header-only; capability and source lifecycle remain at
vocabulary, and source fidelity and skeleton construction remain incomplete.
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
