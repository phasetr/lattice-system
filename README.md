# LatticeSystem

This branch is a from-scratch implementation of the claims in Hal Tasaki's
quantum many-body systems book. It currently contains **zero mathematical
definitions, theorems, or proofs**. The former implementation is not an API or
source for this rewrite.

The canonical plan and gates are in [DESIGN.md](DESIGN.md). Machine-readable
progress begins in `registry/`; its current phase is `census`. The reconciled
R2 ledger contains all 534 physical PDF pages, 3,172 active atomic claims,
1,401 unique equation-label/page pairs, and 63 pages with no claim. The only
production Lean source is an empty module root. A negative checker fixture also
uses a `.lean` suffix but is not a production module.

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
