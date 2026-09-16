# lattice-system

This repository is the scratch reimplementation of Hal Tasaki's *Physics and Mathematics of Quantum
Many-Body Systems* in Lean 4 and mathlib.

The previous implementation is frozen at
[`01bcb49d49db92c225cfa74b74d409dd0a9c4edc`](https://github.com/phasetr/lattice-system/tree/01bcb49d49db92c225cfa74b74d409dd0a9c4edc).
No Lean source, theorem, test, API, status catalogue, script, documentation, or TeX artifact from that
implementation is carried into this rewrite. The anchor may be consulted only for failure lessons and
mathematical ideas; the implementation inputs are Tasaki's source and mathlib.

## Current status

The repository is at the atomic reset/bootstrap phase. It currently contains no mathematical
implementation or proof. Machine-readable source census and status data have only empty bootstrap shapes;
their validators and generated status views are planned work and are not yet implemented.

The authoritative plan is [DESIGN.md](DESIGN.md). Work proceeds in this order:

1. whole-book two-pass census and hash lock;
2. scratch source vocabulary/type layer;
3. whole-book typed assertion skeleton freeze;
4. front-to-back proof discharge.

## Hard merge gate

For every pull request in the rewrite program, including PR #5480, merge is forbidden until the user
currently and explicitly confirms the target PR number and its current exact head SHA and authorizes merging
that head. There is no phase or branch exception. CI GREEN, review APPROVE, design approval, past approval,
and approval for another PR are not merge authority. A head change invalidates approval. Auto-merge, merge
queue use, direct push, and force push to the protected trunk are forbidden. Agents must not check the
merge-confirmation checkbox themselves.

## Build

```sh
lake build
```

The existing `lean-toolchain` and `lake-manifest.json` pins are preserved unchanged.
