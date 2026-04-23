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

For transparency, the following `set_option linter.* false`
suppressions remain in source files as of 2026-04-23. Each is
per-theorem (not file-level) and carries a comment justifying
the suppression. They exist because refactoring the underlying
proof requires interactive `simp?` investigation per
`fin_cases` sub-case, which is best performed in a focused Lean
session.

| Module | Theorem | Suppressed linters | Reason |
|---|---|---|---|
| `Quantum/SpinHalfRotation/Conjugation.lean` | `spinHalfRot3_eq_exp` | `flexible`, `unusedTactic`, `unusedSimpArgs` | Per-sub-case `simp [...]` after `fin_cases i <;> fin_cases j` |
| `Quantum/SpinHalfRotation/Conjugation.lean` | `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp` | `flexible`, `unusedTactic` | Same |
| `Quantum/SpinHalfRotation/Conjugation.lean` | `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown` | `flexible`, `unusedTactic` | Same |
| `Quantum/SpinOneBasis.lean` | `spinOneOpPlus_eq_add` | `flexible` | Per-sub-case `simp [...]` after `fin_cases` over a 3×3 matrix |
| `Quantum/SpinOneBasis.lean` | `spinOneOpMinus_eq_sub` | `flexible` | Same |
| `Quantum/SpinOneDecomp.lean` | `spinOneUnit02_eq_polynomial` | `flexible` | Same |
| `Quantum/SpinOneDecomp.lean` | `spinOneUnit20_eq_polynomial` | `flexible` | Same |
| `Quantum/NeelState/MarshallSign.lean` | (block after deprecated defs) | `deprecated` | Internal companion theorems on the deprecated names |
| `Tests/NeelState.lean` | (file-level inside backward-compat tests) | `deprecated` | Tests intentionally exercise deprecated names; deprecation warnings are independently captured by `#guard_msgs` blocks |

The `lake build` is **zero warnings** even with these suppressions —
they pre-empt warnings the linter would otherwise emit. The
Phase 4 completion criterion (no `set_option linter.* false` in
source files) targets eventual removal of these via interactive
proof refactoring.

**Tracking issue**: [#377](https://github.com/phasetr/lattice-system/issues/377)
follows the removal of these 7 suppressions in a focused
Lean-interactive session.

---

## See also

- [refactoring conventions §3 (dedup + deprecation)](refactoring-conventions.html#3-dedup-conventions)
- [Phase 3 tracking issue #283](https://github.com/phasetr/lattice-system/issues/283)
- [Phase 4 tracking issue #284](https://github.com/phasetr/lattice-system/issues/284)
