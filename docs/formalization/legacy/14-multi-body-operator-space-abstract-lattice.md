---
layout: page
title: "Legacy catalogue: Multi-body operator space (abstract lattice)"
permalink: /formalization/legacy/14-multi-body-operator-space-abstract-lattice/
---

# Legacy catalogue: Multi-body operator space (abstract lattice)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:506:524 -->
### Multi-body operator space (abstract lattice)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2, pp. 21-26 (tensor-product Hilbert space and site-local
operators). The lattice `Λ` is an arbitrary finite set with decidable
equality; specializing to `Λ = Fin N` recovers an `N`-site chain.

| Lean name | Statement | File |
|---|---|---|
| `ManyBodyOp Λ` | `Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ` | `Quantum/ManyBody.lean` |
| `onSite i A` | site-embedded operator at `i : Λ` | `Quantum/ManyBody.lean` |
| `onSite_isHermitian` | `A.IsHermitian → (onSite i A).IsHermitian` | `Quantum/ManyBody.lean` |
| `onSite_add`, `onSite_sub`, `onSite_zero`, `onSite_smul`, `onSite_one` | linearity of the site embedding and `onSite i 1 = 1` | `Quantum/ManyBody.lean` |
| `onSite_mul_onSite_of_ne` | distinct-site commutation (Tasaki (2.2.6), `x ≠ y`, S = 1/2) | `Quantum/ManyBody.lean` |
| `basisVec` / `onSite_mulVec_basisVec` | tensor-product basis states and their action under site operators (Tasaki (2.2.1)/(2.2.4)) | `Quantum/ManyBody.lean` |
| `onSite_mul_onSite_same` | same-site product `onSite i A · onSite i B = onSite i (A · B)` (Tasaki (2.2.6), `x = y`) | `Quantum/ManyBody.lean` |
| `onSite_commutator_same` | same-site commutator `[onSite i A, onSite i B] = onSite i [A, B]` | `Quantum/ManyBody.lean` |
| `Matrix.IsHermitian.mul_of_commute` | commuting Hermitians multiply Hermitian (generic; relocated to the matrix-analysis layer in PR #4342) | `Math/MatrixAnalysis/HermitianSum.lean` |

<!-- legacy-source:end:506:524 -->

---

[← Time-reversal map for `S = 1/2` (Tasaki §2.3)](/lattice-system/formalization/legacy/13-time-reversal-map-for-tasaki-2-3/) · [Catalogue](/lattice-system/formalization/legacy/) · [Generic matrix-analysis helpers (`Math/MatrixAnalysis/`) →](/lattice-system/formalization/legacy/15-generic-matrix-analysis-helpers/)
