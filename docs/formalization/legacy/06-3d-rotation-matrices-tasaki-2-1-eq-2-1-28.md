---
layout: page
title: "Legacy catalogue: 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))"
permalink: /formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28/
---

# Legacy catalogue: 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:313:324 -->
### 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.27)-(2.1.28), p. 18 and Problem 2.1.f.

| Lean name | Statement | File |
|---|---|---|
| `rot3D{1,2,3}Pi` | 3×3 real orthogonal π-rotation matrices | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}Pi_sq` | `(R^(α)_π)² = 1` | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}Pi_mul_rot3D{2,3,1}Pi` | `R^(α)_π · R^(β)_π = R^(γ)_π` (cyclic, Problem 2.1.f) | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}Pi_comm_*` | distinct-axis `R^(α)_π` and `R^(β)_π` commute | `Quantum/Rotation3D.lean` |

<!-- legacy-source:end:313:324 -->

---

[← Z₂ × Z₂ representation (Tasaki §2.1 eqs. (2.1.27)-(2.1.34))](/lattice-system/formalization/legacy/05-z-z-representation-tasaki-2-1-eqs-2-1-27-2-1-34/) · [Catalogue](/lattice-system/formalization/legacy/) · [Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2) →](/lattice-system/formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/)
