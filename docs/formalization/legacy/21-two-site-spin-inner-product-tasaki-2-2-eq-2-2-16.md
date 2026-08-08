---
layout: page
title: "Legacy catalogue: Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))"
permalink: /formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/
---

# Legacy catalogue: Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:1256:1300 -->
### Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 eq. (2.2.16), p. 24.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfDot x y` | `Ŝ_x · Ŝ_y := Σ_{α} onSite x Ŝ^(α) · onSite y Ŝ^(α)` | `Quantum/SpinDot.lean` |
| `spinHalfDot_eq_plus_minus` | `Ŝ_x · Ŝ_y = (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^(3) Ŝ_y^(3)` (Tasaki (2.2.16)) | `Quantum/SpinDot/CoreCommutators.lean` |
| `spinHalfDot_comm` | `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x` | `Quantum/SpinDot/CoreCommutators.lean` |
| `spinHalfDot_self` | `Ŝ_x · Ŝ_x = (3/4) · 1` (the S(S+1) = 3/4 identity for S = 1/2) | `Quantum/SpinDot/CoreCommutators.lean` |
| `spinHalfDot_isHermitian` | `Ŝ_x · Ŝ_y` is Hermitian | `Quantum/SpinDot/CoreCommutators.lean` |
| `totalSpinHalfSquared_eq_sum_dot` | `(Ŝ_tot)² = Σ_{x,y} Ŝ_x · Ŝ_y` | `Quantum/SpinDot/Core.lean` |
| `spinHalfPairSpinSq` / `spinHalfPairSpinSq_eq` | `(Ŝ_x + Ŝ_y)² = 2·(Ŝ_x · Ŝ_y) + Ŝ_x · Ŝ_x + Ŝ_y · Ŝ_y` (Tasaki (2.2.18)) | `Quantum/SpinDot/CoreCommutators.lean` |
| `spinHalfDot_commutator_totalSpinHalfOp{1,2,3}` | `[Ŝ_x · Ŝ_y, Ŝ_tot^(α)] = 0` for α ∈ {1, 2, 3} (SU(2) invariance, Tasaki (2.2.17)) | `Quantum/SpinDot.lean` |
| `spinHalfDot_commutator_totalSpinHalfOpPlus/Minus` | `[Ŝ_x · Ŝ_y, Ŝ^±_tot] = 0` (ladder-operator version of SU(2) invariance) | `Quantum/SpinDot.lean` |
| `spinHalfDot_mulVec_basisVec_parallel` | `Ŝ_x · Ŝ_y |σ⟩ = (1/4) |σ⟩` when `σ x = σ y` and `x ≠ y` (Tasaki (2.2.19) parallel case) | `Quantum/SpinDot/Core.lean` |
| `spinHalfDot_mulVec_basisVec_both_{up,down}` | `Ŝ_x · Ŝ_y |↑↑⟩ = (1/4) |↑↑⟩`, `Ŝ_x · Ŝ_y |↓↓⟩ = (1/4) |↓↓⟩` (Tasaki (2.2.19) triplet `m = ±1`) | `Quantum/SpinDot.lean` |
| `basisSwap` / `basisSwap_involutive` / `basisSwap_antiparallel` | site-swap of `σ` at `x, y`, involutive and preserves anti-parallelism | `Quantum/SpinDot/Core.lean` |
| `spinHalfDot_mulVec_basisVec_antiparallel` | `Ŝ_x · Ŝ_y |σ⟩ = (1/2) |swap σ⟩ - (1/4) |σ⟩` when `σ x ≠ σ y` (anti-parallel case) | `Quantum/SpinDot/Core.lean` |
| `spinHalfDot_mulVec_singlet` | singlet eigenvalue `Ŝ_x · Ŝ_y (|σ⟩ - |swap σ⟩) = -(3/4) (|σ⟩ - |swap σ⟩)` (Tasaki (2.2.19) singlet `S = 0`) | `Quantum/SpinDot/Core.lean` |
| `spinHalfDot_mulVec_triplet_anti` | triplet `m = 0` eigenvalue `Ŝ_x · Ŝ_y (|σ⟩ + |swap σ⟩) = (1/4) (|σ⟩ + |swap σ⟩)` (Tasaki (2.2.19) triplet `m = 0`) | `Quantum/SpinDot/Core.lean` |
| `heisenbergHamiltonian` | `H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` (general Heisenberg-type Hamiltonian) | `Quantum/SpinDot/HamiltonianCore.lean` |
| `heisenbergHamiltonian_commutator_totalSpinHalfOp{1,2,3}` | `[H, Ŝ_tot^(α)] = 0` for all axes (Tasaki (2.2.13) SU(2) invariance) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_commutator_totalSpinHalfOp{Plus,Minus}` | `[H, Ŝ^±_tot] = 0` (ladder form of SU(2) invariance) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_commute_totalSpinHalfSquared` | `Commute H Ŝtot²` — the Casimir operator-level form of SU(2) invariance (consequence of `[H, Ŝtot^α] = 0` for each α, via `Commute.mul_right` and `.add_right`) | `Quantum/SpinDot/HamiltonianCore.lean` |
| `heisenbergHamiltonian_mulVec_preserves_totalSpinHalfSquared_eigenvalue` | if `Ŝtot² · v = S · v` then `Ŝtot² · (H · v) = S · (H · v)` — operator-level simultaneous diagonalisation of `H` and the SU(2) Casimir | `Quantum/SpinDot/HamiltonianCore.lean` |
| `spinHalfOpPlus_mul_pauliZ` / `pauliZ_mul_spinHalfOpPlus` | `σ^+ · σ^z = -σ^+` and `σ^z · σ^+ = σ^+` — the (anti)commutation at the single-site Pauli algebra level, used for the Jordan-Wigner cross-site CAR | `Quantum/SpinHalfBasis.lean` |
| `totalSpinHalfSquared_mulVec_basisVec_const` | `Ŝ_tot² |s s … s⟩ = (N(N+2)/4) |s s … s⟩` for any constant `s : Fin 2` (Casimir eigenvalue at maximum total spin `S = N/2`) | `Quantum/SpinDot/HamiltonianCore.lean` |
| `totalSpinHalfSquared_mulVec_basisVec_all_{up,down}` | specializations of the above to `s = 0` (all-up) and `s = 1` (all-down) | `Quantum/SpinDot.lean` |
| `totalSpinHalfSquared_mulVec_totalSpinHalfOp{Minus,Plus}_pow_basisVec_const` | for any `s : Fin 2` and `k : ℕ`, `Ŝtot² · (Ŝtot^∓)^k · |s…s⟩ = (|Λ|·(|Λ|+2)/4) · (Ŝtot^∓)^k · |s…s⟩` — the iterated ladder iterates remain in the maximum-total-spin SU(2) representation `S = Smax = |Λ|/2` (Casimir invariance, Tasaki §2.4) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_basisVec_const` | `H |s…s⟩ = (Σ_{x,y} J(x,y)·(if x=y then 3/4 else 1/4)) · |s…s⟩` — every Heisenberg-type Hamiltonian acts on a uniformly-aligned basis state as a scalar; bilinear-sum lift of Tasaki §2.4 eq. (2.4.5), p. 32 (`-Ŝ_x·Ŝ_y |Φ↑⟩ = -S² |Φ↑⟩` for `S = 1/2`, `x ≠ y`), with the diagonal `S(S+1) = 3/4` contribution recorded explicitly | `Quantum/SpinDot/Hamiltonian.lean` |
| `heisenbergHamiltonian_mulVec_basisVec_all_{up,down}` | specialisations of the above to `s = 0` (all-up) / `s = 1` (all-down) — the eigenvector property of the fully-polarised states; ground-state status (Tasaki's `E_GS = -|B|·S²`) requires extra ferromagnetic structure on `J` and is not asserted here | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_basisVec_const` | `H · (Ŝ_tot^+ · |s…s⟩) = c_J · (Ŝ_tot^+ · |s…s⟩)` — `Ŝ_tot^+` preserves the H-eigenvalue on a constant-spin basis state (corollary of SU(2) invariance, Tasaki §2.4 (2.4.7), p. 33) | `Quantum/SpinDot/Hamiltonian.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_basisVec_const` | same with `Ŝ_tot^-` — the canonical lowering ladder Tasaki uses to enumerate the ferromagnetic ground states `|Φ_M⟩` (eq. (2.4.9), p. 33) | `Quantum/SpinDot/Hamiltonian.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_const` | iterated form: for any constant `s : Fin 2` and any `k : ℕ`, `H · ((Ŝ_tot^-)^k · |s…s⟩) = c_J · ((Ŝ_tot^-)^k · |s…s⟩)`; specialised at `s = 0` this gives the unnormalised Tasaki §2.4 (2.4.9), p. 33 — every iterate `(Ŝ_tot^-)^k · |Φ↑⟩` lies in the same H-eigenspace as `|Φ↑⟩` | `Quantum/SpinDot/Hamiltonian.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_const` | companion iterated form for `Ŝ_tot^+`: for any constant `s : Fin 2` and any `k : ℕ`, `H · ((Ŝ_tot^+)^k · |s…s⟩) = c_J · ((Ŝ_tot^+)^k · |s…s⟩)` (corollary of SU(2) invariance, Tasaki §2.4 (2.4.7), iterated) | `Quantum/SpinDot/Hamiltonian.lean` |
| `heisenbergHamiltonian_commute_totalSpinHalfRot{1,2,3}` | for any `J` and `θ : ℝ`, `H` commutes with the global rotation `Û^(α)_θ = exp(-iθ Ŝ_tot^α)` (composes `heisenbergHamiltonian_commutator_totalSpinHalfOp{α}` with `totalSpinHalfRot{α}_commute_of_commute`; the operator-level form of Tasaki §2.4 (2.4.7), p. 33) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfRot{1,2,3}_basisVec_const` | for any `J`, `θ`, and constant `s : Fin 2`, `H · (Û^(α)_θ · |s…s⟩) = c_J · (Û^(α)_θ · |s…s⟩)` — the rotated (single-axis) constant-spin state shares the H-eigenvalue (Tasaki §2.4 (2.4.7), p. 33) | `Quantum/SpinDot.lean` |
| `heisenbergHamiltonian_mulVec_totalSpinHalfRot32_basisVec_const` | for any `J`, `θ`, `ϕ`, and constant `s : Fin 2`, `H · (Û^(3)_ϕ · Û^(2)_θ · |s…s⟩) = c_J · (Û^(3)_ϕ · Û^(2)_θ · |s…s⟩)` — the two-step spin-coherent state of Tasaki eq. (2.4.6) (`|Ξ_θ,ϕ⟩` for `s = 0`) is an H-eigenvector with the same eigenvalue as the constant configuration (Tasaki eq. (2.4.7), p. 33) | `Quantum/SpinDot/Hamiltonian.lean` |
| `totalSpinHalfSquared_mulVec_two_site_singlet` | `Ŝ_tot² (|↑↓⟩ - |↓↑⟩) = 0` for `Λ = Fin 2` (singlet, `S = 0`) | `Quantum/SpinDot/Hamiltonian.lean` |
| `totalSpinHalfSquared_mulVec_two_site_triplet_zero` | `Ŝ_tot² (|↑↓⟩ + |↓↑⟩) = 2(|↑↓⟩ + |↓↑⟩)` for `Λ = Fin 2` (triplet `m = 0`, `S = 1`) | `Quantum/SpinDot/Hamiltonian.lean` |
| `totalSpinHalfOp3_mulVec_two_site_singlet` | the two-site singlet has zero `Ŝ_tot^(3)` magnetization | `Quantum/SpinDot/Hamiltonian.lean` |
| `onSite_commutator_totalOnSite` | `[onSite x Sα, Σ_z onSite z Sβ] = onSite x [Sα, Sβ]` | `Quantum/TotalSpin.lean` |

<!-- legacy-source:end:1256:1300 -->

---

[← Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8))](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-05/) · [Catalogue](/lattice-system/formalization/legacy/) · [One-dimensional open-chain quantum Ising →](/lattice-system/formalization/legacy/22-one-dimensional-open-chain-quantum-ising/)
