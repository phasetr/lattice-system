---
layout: page
title: "Legacy catalogue: Spin-1/2 operators (Tasaki §2.1)"
permalink: /formalization/legacy/02-spin-1-2-operators-tasaki-2-1/
---

# Legacy catalogue: Spin-1/2 operators (Tasaki §2.1)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:244:258 -->
### Spin-1/2 operators (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.1), (2.1.7), (2.1.8), pp. 13-15.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfOp{1,2,3}` | `Ŝ^(α) := σ^(α) / 2` (Tasaki (2.1.7)) | `Quantum/SpinHalf.lean` |
| `pauliX_eq_two_smul_spinHalfOp1` etc. | `σ^(α) = 2 · Ŝ^(α)` (Tasaki (2.1.8)) | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_isHermitian` etc. | `Ŝ^(α)` is Hermitian | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_mul_self` etc. | `(Ŝ^(α))² = (1/4) · I` | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_anticomm_spinHalfOp2` etc. | anticommutation at `α ≠ β` | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_commutator_spinHalfOp2` etc. | `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` (Tasaki (2.1.1)) | `Quantum/SpinHalf.lean` |
| `spinHalf_total_spin_squared` | `Σ (Ŝ^(α))² = (3/4) · I`, i.e. `S(S+1)` with `S=1/2` | `Quantum/SpinHalf.lean` |

<!-- legacy-source:end:244:258 -->

---

[← Single-site Pauli operators](/lattice-system/formalization/legacy/01-single-site-pauli-operators/) · [Catalogue](/lattice-system/formalization/legacy/) · [Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26)) →](/lattice-system/formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26/)
