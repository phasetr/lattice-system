---
layout: page
title: "Legacy catalogue: Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))"
permalink: /formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26/
---

# Legacy catalogue: Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:259:296 -->
### Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.26), p. 17 (closed form) and eq. (2.1.23),
p. 16 (`Û_{2π} = -1` for half-odd-integer spin).

| Lean name | Statement | File |
|---|---|---|
| `spinHalfRot{1,2,3}` | `Û^(α)_θ := cos(θ/2) · 1 - 2i · sin(θ/2) · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_zero` | `Û^(α)_0 = 1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_adjoint` | `(Û^(α)_θ)† = Û^(α)_{-θ}` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_two_pi` | `Û^(α)_{2π} = -1` (Tasaki eq. (2.1.23)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_mul` | group law `Û^(α)_θ · Û^(α)_φ = Û^(α)_{θ+φ}` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_unitary` | unitarity `Û^(α)_θ · (Û^(α)_θ)† = 1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_pi` | `Û^(α)_π = -2i · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_pi_sq` | `(Û^(α)_π)² = -1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_pi_anticomm_spinHalfRot{2,3,1}_pi` | `{Û^(α)_π, Û^(β)_π} = 0` for `α ≠ β` (Tasaki (2.1.25)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_pi_conjTranspose` | `(Û^(α)_π)† = 2i · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_pi_mul_spinHalfRot{2,3,1}_pi` | `Û^(α)_π · Û^(β)_π = Û^(γ)_π` (Tasaki (2.1.29), S=1/2) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_pi_conj_spinHalfOp{1,2,3}` | axis invariance and sign flip at θ=π (Tasaki (2.1.15)/(2.1.21)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{2,3,1}` | `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) - sin θ · Ŝ^(γ)` (Tasaki eq. (2.1.16), even-ε cyclic triple) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{3,1,2}` | `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) + sin θ · Ŝ^(γ)` (Tasaki eq. (2.1.16), odd-ε triple) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{1,2,3}` | same-axis invariance `(Û^(α)_θ)† Ŝ^(α) Û^(α)_θ = Ŝ^(α)` (Tasaki eq. (2.1.15)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_half_pi_conj_spinHalfOp{2,3}` / `spinHalfRot2_half_pi_conj_spinHalfOp{3,1}` / `spinHalfRot3_half_pi_conj_spinHalfOp{1,2}` | `π/2`-rotation conjugation `(Û^(α)_{π/2})† Ŝ^(β) Û^(α)_{π/2} = -ε^{αβγ} Ŝ^(γ)` (Tasaki eq. (2.1.22), all 6 cases `α ≠ β`) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot3_eq_exp` | `Û^(3)_θ = exp(-iθ Ŝ^(3))` via `Matrix.exp_diagonal` + Euler (Problem 2.1.b, axis 3) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp` | `Û^(3)_φ Û^(2)_θ |ψ^↑⟩ = e^{-iφ/2} cos(θ/2) |ψ^↑⟩ + e^{iφ/2} sin(θ/2) |ψ^↓⟩` (coherent state, Problem 2.1.d) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown` | `Û^(3)_φ Û^(2)_θ |ψ^↓⟩ = -e^{-iφ/2} sin(θ/2) |ψ^↑⟩ + e^{iφ/2} cos(θ/2) |ψ^↓⟩` (rotation of spin-down, Problem 2.2.c auxiliary) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot3_half_pi_mul_spinHalfRot2_half_pi_mulVec_spinHalfUp` | specialization at θ = φ = π/2 (Problem 2.1.e) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfDotVec` / `spinHalfDotVec_isHermitian` | vector inner product `Ŝ · v := Σ_α v_α Ŝ^(α)` and its Hermiticity (cf. (2.1.19)) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot3_commute_spinHalfOp3_smul` | same-axis rotation commutes with `v · Ŝ^(3)` (cf. (2.1.20) along axis) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `hadamard` / `hadamard_mul_self` | the Hadamard basis-change matrix `W = (1/√2)·!![1,1;1,-1]` and `W·W = 1` | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `hadamard_mul_spinHalfOp1_mul_hadamard` | `W · Ŝ^(1) · W = Ŝ^(3)` (basis change between σ^x and σ^z) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `hadamard_mul_spinHalfOp3_mul_hadamard` | `W · Ŝ^(3) · W = Ŝ^(1)` (inverse basis change) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot1_eq_hadamard_conj` | `Û^(1)_θ = W · Û^(3)_θ · W` (axis 1 rotation as Hadamard conjugate of axis 3) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot1_eq_exp` | `Û^(1)_θ = exp(-iθ Ŝ^(1))` via Hadamard conjugation + `Matrix.exp_conj` (Problem 2.1.b, axis 1) | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `yDiag` / `yDiagAdj` / `yDiag_mul_yDiagAdj` / `yDiag_mul_spinHalfOp3_mul_yDiagAdj` | y-axis basis-change unitary `V` with `V·V† = 1` and `V·Ŝ^(3)·V† = Ŝ^(2)` | `Quantum/SpinHalfRotation/Conjugation.lean` |
| `spinHalfRot2_eq_yDiag_conj` / `spinHalfRot2_eq_exp` | `Û^(2)_θ = V·Û^(3)_θ·V†` and `Û^(2)_θ = exp(-iθ Ŝ^(2))` (Problem 2.1.b, axis 2) | `Quantum/SpinHalfRotation/Conjugation.lean` |

<!-- legacy-source:end:259:296 -->

---

[← Spin-1/2 operators (Tasaki §2.1)](/lattice-system/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/) · [Catalogue](/lattice-system/formalization/legacy/) · [3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11)) →](/lattice-system/formalization/legacy/04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11/)
