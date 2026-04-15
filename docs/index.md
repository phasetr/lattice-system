---
layout: default
title: Home
---

## lattice-system

A Lean 4 + Mathlib formalization project targeting general lattice models.
This project subsumes and generalizes the earlier
[ising-model](https://github.com/phasetr/ising-model) project, progressively
covering classical spin systems, quantum spin systems, Hubbard, BCS,
CAR algebras, and eventually lattice QCD.

## Scope

| Area | Stage | Typical references |
|---|---|---|
| Classical spin systems | Inherited from ising-model | Friedli-Velenik, Glimm-Jaffe |
| Quantum spin systems | Current focus | Tasaki, Nielsen-Chuang (cross-check) |
| Hubbard / BCS | Medium term | Tasaki 1998, Bru-Pedra |
| CAR-algebraic formulation | Medium-long term | Araki-Moriya, Bru-Pedra |
| Thermodynamic limit | Long term | Simon, Friedli-Velenik |
| Lattice QCD | Longest term | Aarts, Davies |

## Roadmap

| Phase | Scope | Status |
|---|---|---|
| P0 | Project skeleton, CI, documentation infrastructure | Done |
| P1a | Finite-volume quantum spin operator algebra (Pauli, `onSite`, commutativity) | Done |
| P1b | Finite-chain quantum Ising Hamiltonian, Hermiticity | Done |
| P1c (Tasaki §2.1) | Spin-1/2 operators `Ŝ^(α)` and the commutator algebra | Done |
| P1d (Tasaki §2.1) | Basis states `|ψ^↑⟩, |ψ^↓⟩`, raising/lowering `Ŝ^±` (S = 1/2) | Done |
| P1d' (Tasaki §2.1) | S = 1 matrix representations (eq. (2.1.9)) | Done |
| P1d'' (Tasaki §2.1) | Problem 2.1.a for S = 1/2 (Pauli basis of `M_2(ℂ)`) | Done |
| P1d''' (Tasaki §2.1) | Problem 2.1.a for `S ≥ 1` (polynomial basis of `M_{2S+1}(ℂ)`) | Not started |
| P1e (Tasaki §2.1) | S = 1/2 rotation `Û^(α)_θ` closed form, `Û_0`, adjoint, `Û_{2π}` | Done |
| P1e' | Rotation group law and unitarity | Done |
| P1e'' (Tasaki §2.1) | `Û^(α)_θ = exp(-iθŜ^(α))` via Mathlib matrix `exp` | Not started |
| P1e''' (Tasaki §2.1) | π-rotations: `Û^(α)_π = -2i·Ŝ^(α)`, anticommutation at distinct axes | Done |
| P1e'''' (Tasaki §2.1) | `Û^(α)_π · Û^(β)_π = Û^(γ)_π`; conjugations `(Û^(α)_π)†·Ŝ^(β)·Û^(α)_π = ±Ŝ^(β)` | Done |
| P1e''''' (Tasaki §2.1) | General θ transformation `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) - sin θ · ε^{αβγ} Ŝ^(γ)` (eq. (2.1.16)) | Done |
| P1e'''''' (Tasaki §2.1) | Z₂ × Z₂ representation (eqs. (2.1.27)-(2.1.34)) | Not started |
| P1d-S1 (Tasaki §2.1) | S = 1 basis states and `Ŝ^(3)`, `Ŝ^±` actions (eqs. (2.1.2)–(2.1.6) for S = 1) | Done |
| P1f (Tasaki §2.2) | Abstract lattice `Λ`, site operators `Ŝ_x^(α)`, distinct-site commutation (eq. (2.2.6), `x ≠ y`) | Done |
| P1f-same (Tasaki §2.2) | Same-site commutation `[Ŝ_x^(α), Ŝ_x^(β)] = i·ε^{αβγ} Ŝ_x^(γ)` (eq. (2.2.6), `x = y`) | Done |
| P1f' (Tasaki §2.2) | Total spin operator `Ŝ_tot^(α)` (eq. (2.2.7)) and Hermiticity | Done |
| P1f'-pm (Tasaki §2.2) | Total raising/lowering `Ŝ^±_tot = Σ_x Ŝ_x^±` (eq. (2.2.8)) | Done |
| P1f-mag (Tasaki §2.2) | Total magnetization `|σ| := Σ_x spinSign(σ_x)` (eq. (2.2.2)) | Done |
| P1f'' (Tasaki §2.2) | Global rotation `Û^(α)_θ = exp(-iθ Ŝ_tot^(α))` (eq. (2.2.11)) | Not started |
| P1f''' (Tasaki §2.2) | SU(2) / U(1) invariance (eqs. (2.2.12)-(2.2.13)) | Not started |
| P1f'''' (Tasaki §2.2) | Two-site inner product `Ŝ_x · Ŝ_y` raising/lowering decomposition (eq. (2.2.16)) | Done |
| P1f''''' (Tasaki §2.2) | SU(2) invariance of `Ŝ_x · Ŝ_y` and eigenvalues (eqs. (2.2.17)–(2.2.19)) | Not started |
| P1g | Gibbs state `ρ = e^{-βH}/Z`, expectation `⟨O⟩_β = Tr(ρO)` | Not started |
| P1h | Periodic boundary conditions, other quantum chains (Heisenberg) | Not started |
| P2 | Finite-volume Hubbard / BCS | Not started |
| P3 | CAR algebras, quasi-local C*-algebras, KMS states | Not started |
| P4 | Thermodynamic limit, phase transitions | Not started |
| P5 | Lattice QCD | Not started |

## Formalized theorems

All items below are formally proved with **zero `sorry`**. Full
mathematical statements and proof sketches are in
[`tex/proof-guide.tex`](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex).

### Single-site Pauli operators

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.8), p. 15. Cross-checked with Nielsen-Chuang
§2.1.3 Figure 2.2 (pp. 65-66, definitions), Ex. 2.19 (p. 70,
Hermiticity), Ex. 2.41 (p. 78, `(σ^α)² = I` and anticommutation),
Ex. 2.40 (p. 77, commutator, whence the cyclic products).

| Lean name | Statement | File |
|---|---|---|
| `pauliX/Y/Z_isHermitian` | `(σ^α)† = σ^α` | `Quantum/Pauli.lean` |
| `pauliX/Y/Z_mul_self` | `(σ^α)² = I` | `Quantum/Pauli.lean` |
| `pauliX_mul_pauliY` etc. | `σ^x σ^y = i·σ^z` (cyclic) | `Quantum/Pauli.lean` |
| `pauliX_anticomm_pauliY` etc. | `σ^α σ^β + σ^β σ^α = 0` (α ≠ β) | `Quantum/Pauli.lean` |

### Spin-1/2 operators (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.1), (2.1.7), (2.1.8), pp. 13-15.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfOp1/2/3` | `Ŝ^(α) := σ^(α) / 2` (Tasaki (2.1.7)) | `Quantum/SpinHalf.lean` |
| `pauliX_eq_two_smul_spinHalfOp1` etc. | `σ^(α) = 2 · Ŝ^(α)` (Tasaki (2.1.8)) | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_isHermitian` etc. | `Ŝ^(α)` is Hermitian | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_mul_self` etc. | `(Ŝ^(α))² = (1/4) · I` | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_anticomm_spinHalfOp2` etc. | anticommutation at `α ≠ β` | `Quantum/SpinHalf.lean` |
| `spinHalfOp1_commutator_spinHalfOp2` etc. | `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` (Tasaki (2.1.1)) | `Quantum/SpinHalf.lean` |
| `spinHalf_total_spin_squared` | `Σ (Ŝ^(α))² = (3/4) · I`, i.e. `S(S+1)` with `S=1/2` | `Quantum/SpinHalf.lean` |

### Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.26), p. 17 (closed form) and eq. (2.1.23),
p. 16 (`Û_{2π} = -1` for half-odd-integer spin).

| Lean name | Statement | File |
|---|---|---|
| `spinHalfRot1/2/3` | `Û^(α)_θ := cos(θ/2) · 1 - 2i · sin(θ/2) · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_zero` | `Û^(α)_0 = 1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_adjoint` | `(Û^(α)_θ)† = Û^(α)_{-θ}` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_two_pi` | `Û^(α)_{2π} = -1` (Tasaki eq. (2.1.23)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_mul` | group law `Û^(α)_θ · Û^(α)_φ = Û^(α)_{θ+φ}` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_unitary` | unitarity `Û^(α)_θ · (Û^(α)_θ)† = 1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi` | `Û^(α)_π = -2i · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi_sq` | `(Û^(α)_π)² = -1` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_pi_anticomm_spinHalfRot2_pi` (and cyclic) | `{Û^(α)_π, Û^(β)_π} = 0` for `α ≠ β` (Tasaki (2.1.25)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi_conjTranspose` | `(Û^(α)_π)† = 2i · Ŝ^(α)` | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1_pi_mul_spinHalfRot2_pi` (and cyclic) | `Û^(α)_π · Û^(β)_π = Û^(γ)_π` (Tasaki (2.1.29), S=1/2) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot1/2/3_pi_conj_spinHalfOp_*` | axis invariance and sign flip at θ=π (Tasaki (2.1.15)/(2.1.21)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{2,3,1}` | `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) - sin θ · Ŝ^(γ)` (Tasaki eq. (2.1.16), even-ε cyclic triple) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{3,1,2}` | `(Û^(α)_θ)† Ŝ^(β) Û^(α)_θ = cos θ · Ŝ^(β) + sin θ · Ŝ^(γ)` (Tasaki eq. (2.1.16), odd-ε triple) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_conj_spinHalfOp{1,2,3}` | same-axis invariance `(Û^(α)_θ)† Ŝ^(α) Û^(α)_θ = Ŝ^(α)` (Tasaki eq. (2.1.15)) | `Quantum/SpinHalfRotation.lean` |
| `spinHalfRot{1,2,3}_half_pi_conj_spinHalfOp_*` | `π/2`-rotation conjugation `(Û^(α)_{π/2})† Ŝ^(β) Û^(α)_{π/2} = -ε^{αβγ} Ŝ^(γ)` (Tasaki eq. (2.1.22), 6 cases) | `Quantum/SpinHalfRotation.lean` |

### Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a, p. 15.

| Lean name | Statement | File |
|---|---|---|
| `pauliCoeff0/1/2/3` | explicit coefficient functions | `Quantum/SpinHalfDecomp.lean` |
| `pauli_decomposition` | `A = Σᵢ cᵢ · σ^(i)` | `Quantum/SpinHalfDecomp.lean` |
| `spinHalf_decomposition` | same via `Ŝ^(α) = σ^(α) / 2` | `Quantum/SpinHalfDecomp.lean` |
| `pauli_linearIndep` | `{1, σ^x, σ^y, σ^z}` is linearly independent | `Quantum/SpinHalfDecomp.lean` |

### S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.9), p. 15.

| Lean name | Statement | File |
|---|---|---|
| `spinOneOp1/2/3` | 3×3 matrix definitions (Tasaki (2.1.9)) | `Quantum/SpinOne.lean` |
| `spinOneOp1/2/3_isHermitian` | Hermiticity | `Quantum/SpinOne.lean` |
| `spinOneOp1_commutator_spinOneOp2` etc. | `[Ŝ^(α), Ŝ^(β)] = i · Ŝ^(γ)` (S = 1) | `Quantum/SpinOne.lean` |
| `spinOne_total_spin_squared` | `Σ (Ŝ^(α))² = 2 · I`, i.e. `S(S+1)` with `S = 1` | `Quantum/SpinOne.lean` |

### Basis states and raising/lowering (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.4), (2.1.5), (2.1.6), p. 14.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfUp`, `spinHalfDown` | `\|ψ^↑⟩`, `\|ψ^↓⟩` as column vectors (Tasaki (2.1.6)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOp3_mulVec_spinHalfUp/Down` | `Ŝ^(3)` eigenvalue equations (Tasaki (2.1.4)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus`, `spinHalfOpMinus` | raising/lowering `Ŝ^±` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus_eq_add`, `spinHalfOpMinus_eq_sub` | `Ŝ^± = Ŝ^(1) ± i · Ŝ^(2)` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus/Minus_mulVec_spinHalfUp/Down` | raising/lowering actions (Tasaki (2.1.5)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus/Minus_conjTranspose` | `(Ŝ^±)† = Ŝ^∓` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus_commutator_spinHalfOpMinus` | `[Ŝ^+, Ŝ^-] = 2 · Ŝ^(3)` | `Quantum/SpinHalfBasis.lean` |

### Basis states and raising/lowering for S = 1 (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.2), (2.1.3), (2.1.6), p. 14 for the `S = 1`
case (`σ ∈ {-1, 0, +1}`).

| Lean name | Statement | File |
|---|---|---|
| `spinOnePlus/Zero/Minus` | column vectors `|ψ^{+1}⟩, |ψ^{0}⟩, |ψ^{-1}⟩` | `Quantum/SpinOneBasis.lean` |
| `spinOneOp3_mulVec_spinOnePlus/Zero/Minus` | `Ŝ^(3)` eigenvalue equations (Tasaki (2.1.2), S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus`, `spinOneOpMinus` | 3×3 raising/lowering `Ŝ^±` for S = 1 | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus/Minus_mulVec_*` | raising/lowering actions `Ŝ^± |ψ^σ⟩ = √(2 - σ(σ±1)) |ψ^{σ±1}⟩` (Tasaki (2.1.3), S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus/Minus_conjTranspose` | `(Ŝ^±)† = Ŝ^∓` for S = 1 | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}` | S = 1 π-rotation matrices `û_α` (Tasaki eq. (2.1.33)) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot3_eq` | `û_3 = 1 - 2·(Ŝ^(3))²` (Tasaki eq. (2.1.32), α = 3 case) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}_sq` | `(û_α)² = 1` for integer S (Tasaki eq. (2.1.31) integer case) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}_comm_*` | distinct-axis commutation `û_α · û_β = û_β · û_α` for integer S | `Quantum/SpinOneBasis.lean` |

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
| `onSite_mul_onSite_same` | same-site product `onSite i A · onSite i B = onSite i (A · B)` (Tasaki (2.2.6), `x = y`) | `Quantum/ManyBody.lean` |
| `onSite_commutator_same` | same-site commutator `[onSite i A, onSite i B] = onSite i [A, B]` | `Quantum/ManyBody.lean` |
| `Matrix.IsHermitian.mul_of_commute` | commuting Hermitians multiply Hermitian | `Quantum/ManyBody.lean` |

### Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 eqs. (2.2.7) and (2.2.8), p. 22.

| Lean name | Statement | File |
|---|---|---|
| `totalSpinHalfOp1/2/3 Λ` | `Ŝ_tot^(α) := Σ_{x ∈ Λ} onSite x Ŝ^(α)` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp1/2/3_isHermitian` | `Ŝ_tot^(α)` is Hermitian | `Quantum/TotalSpin.lean` |
| `spinHalfOp_onSite_comm_of_ne` | S = 1/2 named wrapper of `onSite_mul_onSite_of_ne` | `Quantum/TotalSpin.lean` |
| `spinHalfOp{1,2,3}_onSite_commutator_spinHalfOp{2,3,1}_onSite` | same-site commutator `[Ŝ_x^(α), Ŝ_x^(β)] = i · Ŝ_x^(γ)` (Tasaki (2.2.6), `x = y`) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus`, `totalSpinHalfOpMinus` | `Ŝ^±_tot := Σ_{x ∈ Λ} onSite x Ŝ^±` (Tasaki (2.2.8)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_eq_add`, `totalSpinHalfOpMinus_eq_sub` | `Ŝ^±_tot = Ŝ^(1)_tot ± i · Ŝ^(2)_tot` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus/Minus_conjTranspose` | `(Ŝ^±_tot)† = Ŝ^∓_tot` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{1,2,3}_commutator_totalSpinHalfOp{2,3,1}` | `[Ŝ_tot^(α), Ŝ_tot^(β)] = i · Ŝ_tot^(γ)` (total spin commutation) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_commutator_totalSpinHalfOpPlus/Minus` | `[Ŝ_tot^(3), Ŝ^±_tot] = ±Ŝ^±_tot` (Cartan ladder relations) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared` / `_isHermitian` | Casimir operator `(Ŝ_tot)² := Σ_α (Ŝ_tot^(α))²` and its Hermiticity | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared_commutator_totalSpinHalfOp{1,2,3}` | `[(Ŝ_tot)², Ŝ_tot^(α)] = 0` (Casimir invariance, cf. Tasaki (2.2.12)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared_commutator_totalSpinHalfOpPlus/Minus` | `[(Ŝ_tot)², Ŝ^±_tot] = 0` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_commutator_totalSpinHalfOpMinus` | `[Ŝ^+_tot, Ŝ^-_tot] = 2 · Ŝ_tot^(3)` | `Quantum/TotalSpin.lean` |
| `magnetization`, `spinSign` | total magnetization `|σ| := Σ_x spinSign(σ_x)` (Tasaki (2.2.2)) | `Quantum/TotalSpin.lean` |

### Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 eq. (2.2.16), p. 24.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfDot x y` | `Ŝ_x · Ŝ_y := Σ_{α} onSite x Ŝ^(α) · onSite y Ŝ^(α)` | `Quantum/SpinDot.lean` |
| `spinHalfDot_eq_plus_minus` | `Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^(3) Ŝ_y^(3)` (Tasaki (2.2.16)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_comm` | `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x` | `Quantum/SpinDot.lean` |
| `spinHalfDot_self` | `Ŝ_x · Ŝ_x = (3/4) · 1` (the S(S+1) = 3/4 identity for S = 1/2) | `Quantum/SpinDot.lean` |
| `spinHalfDot_isHermitian` | `Ŝ_x · Ŝ_y` is Hermitian | `Quantum/SpinDot.lean` |
| `spinHalfPairSpinSq` / `spinHalfPairSpinSq_eq` | `(Ŝ_x + Ŝ_y)² = 2·(Ŝ_x · Ŝ_y) + Ŝ_x · Ŝ_x + Ŝ_y · Ŝ_y` (Tasaki (2.2.18)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_commutator_totalSpinHalfOp{1,2,3}` | `[Ŝ_x · Ŝ_y, Ŝ_tot^(α)] = 0` for α ∈ {1, 2, 3} (SU(2) invariance, Tasaki (2.2.17)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_commutator_totalSpinHalfOpPlus/Minus` | `[Ŝ_x · Ŝ_y, Ŝ^±_tot] = 0` (ladder-operator version of SU(2) invariance) | `Quantum/SpinDot.lean` |
| `onSite_commutator_totalOnSite` | `[onSite x Sα, Σ_z onSite z Sβ] = onSite x [Sα, Sβ]` | `Quantum/TotalSpin.lean` |

### One-dimensional open-chain quantum Ising

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.3 eq. (3.3.1), p. 55 (transverse-field Ising on an open
chain). Our formalization uses the Pauli convention `σ = 2·S` and an
explicit bond coupling `J`.

| Lean name | Statement | File |
|---|---|---|
| `quantumIsingHamiltonian N J h` | `H = -J Σ σ^z_i σ^z_{i+1} - h Σ σ^x_i` | `Quantum/IsingChain.lean` |
| `quantumIsingHamiltonian_isHermitian` | `H` is Hermitian for real `J`, `h` | `Quantum/IsingChain.lean` |

## Links

- [API documentation (doc-gen4)](docs/)
- [GitHub repository](https://github.com/phasetr/lattice-system)
- [Mathematical guide (`tex/proof-guide.tex`)](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex)
- [ising-model (upstream project)](https://github.com/phasetr/ising-model)
- [Lean by Example](https://lean-ja.github.io/lean-by-example/)
