---
layout: page
title: "Legacy catalogue: S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))"
permalink: /formalization/legacy/09-s-1-matrix-representations-tasaki-2-1-eq-2-1-9/
---

# Legacy catalogue: S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:353:364 -->
### S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.9), p. 15.

| Lean name | Statement | File |
|---|---|---|
| `spinOneOp{1,2,3}` | 3×3 matrix definitions (Tasaki (2.1.9)) | `Quantum/SpinOne.lean` |
| `spinOneOp{1,2,3}_isHermitian` | Hermiticity | `Quantum/SpinOne.lean` |
| `spinOneOp1_commutator_spinOneOp2` etc. | `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` (S = 1) | `Quantum/SpinOne.lean` |
| `spinOne_total_spin_squared` | `Σ (Ŝ^(α))² = 2 · I`, i.e. `S(S+1)` with `S = 1` | `Quantum/SpinOne.lean` |

<!-- legacy-source:end:353:364 -->

---

[← Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)](/lattice-system/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/) · [Catalogue](/lattice-system/formalization/legacy/) · [Spin-`S` operators (general S ≥ 0, parameterised by `N = 2S : ℕ`) →](/lattice-system/formalization/legacy/10-spin-operators-general-s-0-parameterised-by/)
