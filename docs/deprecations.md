---
layout: page
title: Deprecation window
permalink: /deprecations/
---

# Deprecation window

This page tracks declarations marked `@[deprecated]` in the
public lattice-system API, the date deprecation began, the
recommended replacement, and the planned removal window.

Per the project's [refactoring conventions](refactoring-conventions.html)
§3, the deprecation window is **at least one minor release of
the project** (i.e., one feature-cluster of subsequent PRs).

The current minimum deprecation window is **6 months** from the
`since` date. After that window the deprecated declarations may
be removed in a subsequent PR; users should migrate to the
recommended replacement before then.

---

## Currently deprecated

| Declaration | Since | Recommended replacement | Earliest removal | Tracked in |
|---|---|---|---|---|
| `LatticeSystem.Quantum.marshallSignChainConfig` | 2026-04-22 | `marshallSignOf` with the chain parity indicator `fun x : Fin (2*K) => decide (x.val % 2 = 0)` (bridged via `marshallSignChainConfig_eq_marshallSignOf`) | 2026-10-22 | [#283](https://github.com/phasetr/lattice-system/issues/283) (PR #333) |
| `LatticeSystem.Quantum.marshallSignSquareConfig` | 2026-04-22 | `marshallSignOf` with the 2D parity indicator `fun p => decide ((p.1.val + p.2.val) % 2 = 0)` (bridged via `marshallSignSquareConfig_eq_marshallSignOf`) | 2026-10-22 | [#283](https://github.com/phasetr/lattice-system/issues/283) (PR #333) |
| `LatticeSystem.Quantum.marshallSignCubicConfig` | 2026-04-22 | `marshallSignOf` with the 3D parity indicator `fun p => decide ((p.1.1.val + p.1.2.val + p.2.val) % 2 = 0)` (bridged via `marshallSignCubicConfig_eq_marshallSignOf`) | 2026-10-22 | [#283](https://github.com/phasetr/lattice-system/issues/283) (PR #333) |

---

## Removal policy

When the earliest-removal date passes, the deprecated declaration
is eligible for removal. Removal proceeds as a separate
*deprecation-removal* PR with the following checklist:

- [ ] The deprecation has been in place for ≥ 6 months *and* at
  least one minor release.
- [ ] All call sites in the project source have migrated to the
  recommended replacement.
- [ ] The companion theorems on the deprecated name (e.g.,
  `marshallSignChainConfig_const_zero`) have been either
  re-stated against the replacement or removed.
- [ ] The `#guard_msgs` deprecation-warning capture test for the
  removed declaration is also removed.
- [ ] `docs/index.md` and this `deprecations.md` page are updated
  to drop the entry.

The companion theorems on a deprecated name (e.g.,
`marshallSignChainConfig_neelChainConfig`,
`marshallSignChainConfig_const_zero`,
`marshallSignChainConfig_flipConfig`) are **not** themselves
deprecated. They serve as the migration scaffolding: when the
deprecated definition is eventually removed, these theorems are
either re-proved against the generic form or merged into the
generic API.

---

## Test discipline

Every deprecation **must** carry at least one `#guard_msgs` test
in the corresponding `LatticeSystem/Tests/<Module>.lean` file
(method F per [refactoring conventions](refactoring-conventions.html)
§1). The test pins the exact deprecation-warning text, so any
accidental change to the warning message (or premature removal
of the deprecation) is caught at build time.

Existing `#guard_msgs` deprecation tests:

| Declaration | Test location |
|---|---|
| `marshallSignChainConfig` | `Tests/NeelState.lean` (end of file, F-method block) |
| `marshallSignSquareConfig` | `Tests/NeelState.lean` (end of file, F-method block) |
| `marshallSignCubicConfig` | `Tests/NeelState.lean` (end of file, F-method block) |

---

## Remaining linter suppressions

The 7 `set_option linter.flexible / unusedTactic / unusedSimpArgs`
suppressions that appeared in `SpinOneBasis.lean`, `SpinOneDecomp.lean`,
and `SpinHalfRotation/Conjugation.lean` were removed in PR #395
(tracking issue #377).

The following `set_option linter.* false` suppressions remain:

| Module | Theorem / block | Suppressed linters | Reason |
|---|---|---|---|
| `Quantum/NeelState/MarshallSign.lean` | (block after deprecated defs) | `deprecated` | Internal companion theorems on the deprecated names |
| `Tests/NeelState.lean` | (file-level inside backward-compat tests) | `deprecated` | Tests intentionally exercise deprecated names; deprecation warnings are independently captured by `#guard_msgs` blocks |

The `lake build` is **zero warnings and zero errors** as of 2026-04-25.

**Second-pass audit (#390, 2026-04-25)**: a re-scan of the codebase
confirmed that no additional untracked `set_option linter.*` blocks
exist beyond those listed in this table.

---

## See also

- [refactoring conventions](refactoring-conventions.html) §3 (dedup + deprecation)
- [Phase 3 tracking issue #283](https://github.com/phasetr/lattice-system/issues/283)
- [Phase 4 tracking issue #284](https://github.com/phasetr/lattice-system/issues/284)
