---
layout: page
title: "Legacy catalogue: 3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11))"
permalink: /formalization/legacy/04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11/
---

# Legacy catalogue: 3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11))

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:297:304 -->
### 3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11))

| Lean name | Statement | File |
|---|---|---|
| `rot3D{1,2,3} θ` | 3×3 real rotation matrices by angle θ about each axis. Internal implementation record (private, not public API): `rot3D1`, `rot3D2`, `rot3D3` are `axisRot3D a θ` at `a = 0, 1, 2` for the private def `axisRot3D : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ`, and the two rows below are proved from the private theorems `axisRot3D_zero` and `axisRot3D_pi` in the same file. | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}_zero` | `R^(α)_0 = 1` | `Quantum/Rotation3D.lean` |
| `rot3D{1,2,3}_pi` | `R^(α)_π` from general formula matches explicit π-rotation | `Quantum/Rotation3D.lean` |

<!-- legacy-source:end:297:304 -->

---

[← Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))](/lattice-system/formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26/) · [Catalogue](/lattice-system/formalization/legacy/) · [Z₂ × Z₂ representation (Tasaki §2.1 eqs. (2.1.27)-(2.1.34)) →](/lattice-system/formalization/legacy/05-z-z-representation-tasaki-2-1-eqs-2-1-27-2-1-34/)
