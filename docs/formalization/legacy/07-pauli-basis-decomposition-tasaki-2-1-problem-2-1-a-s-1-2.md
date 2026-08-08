---
layout: page
title: "Legacy catalogue: Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)"
permalink: /formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/
---

# Legacy catalogue: Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:325:336 -->
### Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a, p. 15.

| Lean name | Statement | File |
|---|---|---|
| `pauliCoeff{0,1,2,3}` | explicit coefficient functions | `Quantum/SpinHalfDecomp.lean` |
| `pauli_decomposition` | `A = Σᵢ cᵢ · σ^(i)` | `Quantum/SpinHalfDecomp.lean` |
| `spinHalf_decomposition` | same via `Ŝ^(α) = σ^(α) / 2` | `Quantum/SpinHalfDecomp.lean` |
| `pauli_linearIndep` | `{1, σ^x, σ^y, σ^z}` is linearly independent | `Quantum/SpinHalfDecomp.lean` |

<!-- legacy-source:end:325:336 -->

---

[← 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))](/lattice-system/formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28/) · [Catalogue](/lattice-system/formalization/legacy/) · [Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1) →](/lattice-system/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/)
