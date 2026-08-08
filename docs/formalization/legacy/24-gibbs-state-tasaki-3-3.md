---
layout: page
title: "Legacy catalogue: Gibbs state (Tasaki §3.3)"
permalink: /formalization/legacy/24-gibbs-state-tasaki-3-3/
---

# Legacy catalogue: Gibbs state (Tasaki §3.3)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

<!-- legacy-source:start:1349:1443 -->
### Gibbs state (Tasaki §3.3)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.3.

All theorems in this module are fully proved with **zero `sorry`**.

| Lean name | Statement | File |
|---|---|---|
| `gibbsExp β H` | `exp(-βH) := Matrix.exp (-β • H)` | `Quantum/GibbsState.lean` |
| `gibbsExp_isHermitian` | `exp(-βH)` is Hermitian (when `H` is Hermitian) | `Quantum/GibbsState.lean` |
| `gibbsExp_zero` | `exp(-0·H) = 1` (Tasaki §3.3, pp. 75–78) | `Quantum/GibbsState.lean` |
| `gibbsExp_add` | `exp(-(β₁+β₂)H) = exp(-β₁H) · exp(-β₂H)` (one-parameter group) | `Quantum/GibbsState.lean` |
| `gibbsExp_add_of_commute_hamiltonians` | `exp(-β(H₁+H₂)) = exp(-βH₁) · exp(-βH₂)` for commuting `H₁, H₂` | `Quantum/GibbsState.lean` |
| `gibbsExp_neg_mul_self` | `exp(βH) · exp(-βH) = 1` | `Quantum/GibbsState.lean` |
| `gibbsExp_self_mul_neg` | `exp(-βH) · exp(βH) = 1` | `Quantum/GibbsState.lean` |
| `gibbsExp_isUnit` | `exp(-βH)` is invertible | `Quantum/GibbsState.lean` |
| `gibbsExp_ne_zero` | `exp(-βH) ≠ 0` (corollary of `gibbsExp_isUnit`) | `Quantum/GibbsState.lean` |
| `gibbsState_ne_zero` | `ρ_β ≠ 0` when `Z(β) ≠ 0` | `Quantum/GibbsState.lean` |
| `gibbsState_inv` | `(ρ_β)⁻¹ = Z(β) · e^{βH}` when `Z(β) ≠ 0` (general matrix inverse, generalises `gibbsState_zero_inv`) | `Quantum/GibbsState.lean` |
| `partitionFn_smul_gibbsState_eq_gibbsExp` | `Z(β) · ρ_β = e^{-βH}` when `Z(β) ≠ 0` (canonical rescaled identity) | `Quantum/GibbsState.lean` |
| `partitionFn_mul_gibbsExpectation_eq` | `Z(β) · ⟨A⟩_β = Tr(e^{-βH} · A)` when `Z(β) ≠ 0` (canonical unnormalised expectation) | `Quantum/GibbsState.lean` |
| `gibbsExp_natCast_mul` | `exp(-(n·β)H) = (exp(-βH))^n` for `n : ℕ` (exact discrete semigroup identity) | `Quantum/GibbsState.lean` |
| `gibbsExp_two_mul` | `exp(-(2β)H) = exp(-βH) · exp(-βH)` | `Quantum/GibbsState.lean` |
| `gibbsExp_inv` | `(exp(-βH))⁻¹ = exp(βH)` (matrix inverse made explicit) | `Quantum/GibbsState.lean` |
| `gibbsExp_intCast_mul` | `exp(-(n·β)H) = (exp(-βH))^n` for `n : ℤ` (integer-power extension) | `Quantum/GibbsState.lean` |
| `partitionFn β H` | `Z := Matrix.trace (exp(-βH))` | `Quantum/GibbsState.lean` |
| `partitionFn_zero` | `Z(0) = Fintype.card (Λ → Fin 2)` (dimension of the Hilbert space) | `Quantum/GibbsState.lean` |
| `partitionFn_zero_ne_zero` | `Z(0) ≠ 0` (concrete sorry-free proof that the partition function is nonzero at β = 0) | `Quantum/GibbsState.lean` |
| `Matrix.IsHermitian.trace_im` | for any Hermitian `A : Matrix n n ℂ`, `A.trace.im = 0` (generic helper; relocated to the matrix-analysis layer in PR #4344) | `Math/MatrixAnalysis/HermitianTrace.lean` |
| `partitionFn_im_of_isHermitian` | for Hermitian `H`, `(partitionFn β H).im = 0` (Z is real) | `Quantum/GibbsState.lean` |
| `gibbsState_mul_self_trace` | `Tr(ρ_β²) = Z(2β) / Z(β)²` (purity / Rényi-2 entropy precursor) | `Quantum/GibbsState.lean` |
| `gibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for any `n : ℕ` (Rényi-n entropy precursor) | `Quantum/GibbsState.lean` |
| `gibbsState_zero` | `ρ_0 = (1/dim) · I` (maximally mixed state at infinite temperature) | `Quantum/GibbsState.lean` |
| `gibbsState_zero_inv` | `ρ_0⁻¹ = dim · I` (matrix inverse at β = 0) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_zero` | `⟨A⟩_0 = (1/dim) · Tr A` (high-temperature limit) | `Quantum/GibbsState.lean` |
| `gibbsState β H` | `ρ := (1/Z) • exp(-βH)` | `Quantum/GibbsState.lean` |
| `gibbsState_trace` | `Tr(ρ) = 1` | `Quantum/GibbsState.lean` |
| `gibbsState_isHermitian` | `ρ` is Hermitian | `Quantum/GibbsState.lean` |
| `gibbsExpectation β H O` | `⟨O⟩ := Matrix.trace (ρ * O)` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_one` | `⟨1⟩ = 1` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_add` | `⟨O₁ + O₂⟩ = ⟨O₁⟩ + ⟨O₂⟩` (linearity in observable) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_smul` | `⟨c · O⟩ = c · ⟨O⟩` (scalar linearity, `c : ℂ`) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_neg` | `⟨-O⟩ = -⟨O⟩` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_sub` | `⟨A - B⟩ = ⟨A⟩ - ⟨B⟩` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_sum` | `⟨∑ i ∈ s, f i⟩ = ∑ i ∈ s, ⟨f i⟩` (finite-sum linearity) | `Quantum/GibbsState.lean` |
| `gibbsExp_commute_hamiltonian` | `[exp(-βH), H] = 0` (Tasaki §3.3, p. 80) | `Quantum/GibbsState.lean` |
| `gibbsState_commute_hamiltonian` | `[ρ_β, H] = 0`, i.e. `ρ_β` is stationary under the dynamics generated by `H` (Tasaki §3.3, p. 80) | `Quantum/GibbsState.lean` |
| `Matrix.trace_mul_star_of_isHermitian` | `star (Tr(A · B)) = Tr(A · B)` for Hermitian `A, B : Matrix n n ℂ` (algebraic core, Gibbs-independent; relocated to the matrix-analysis layer in PR #4344) | `Math/MatrixAnalysis/HermitianTrace.lean` |
| `gibbsExpectation_star_of_isHermitian` | `star ⟨O⟩_β = ⟨O⟩_β` for Hermitian `H`, `O` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_im_of_isHermitian` | `(⟨O⟩_β).im = 0` for Hermitian `H`, `O` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_ofReal_re_eq_of_isHermitian` | `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` for Hermitian `H`, `O` (real-cast equality) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_mul_hamiltonian_comm` | `⟨H · A⟩_β = ⟨A · H⟩_β` for any `A` (Tasaki §3.3, p. 80) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_mul_comm_of_commute_hamiltonian` | for any conserved `A` (`[A, H] = 0`), `⟨A · O⟩_β = ⟨O · A⟩_β` | `Quantum/GibbsState.lean` |
| `gibbsExpectation_commutator_eq_zero_of_commute_hamiltonian` | for any conserved `A`, `⟨A · O − O · A⟩_β = 0` (selection rule) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_commutator_hamiltonian` | `⟨[H, A]⟩_β = 0` (conservation law) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_hamiltonian_im` | `(⟨H⟩_β).im = 0` for Hermitian `H` (real energy expectation) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_sq_im_of_isHermitian` | `(⟨O · O⟩_β).im = 0` for Hermitian `H, O` (second-moment realness, variance precursor) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_pow_im_of_isHermitian` | `(⟨O^n⟩_β).im = 0` for Hermitian `H, O`, any `n : ℕ` (all natural-power moments real) | `Quantum/GibbsState.lean` |
| `gibbsVariance β H O` | `Var_β(O) := ⟨O · O⟩_β − ⟨O⟩_β²` (canonical-ensemble variance) | `Quantum/GibbsState.lean` |
| `gibbsVariance_eq` | unfolding lemma for `gibbsVariance` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_im_of_isHermitian` | `(Var_β(O)).im = 0` for Hermitian `H, O` (variance is real) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_zero` | at β = 0, `Var_0(O) = (1/dim) · Tr(O²) − ((1/dim) · Tr O)²` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_eq_centered_sq` | `Var_β(O) = ⟨(O − ⟨O⟩_β · 1) · (O − ⟨O⟩_β · 1)⟩_β` (centered-square form, `Z ≠ 0`) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance β H A B` | `Cov_β(A, B) := ⟨A · B⟩_β − ⟨A⟩_β · ⟨B⟩_β` (canonical-ensemble complex covariance) | `Quantum/GibbsState.lean` |
| `gibbsCovariance_eq` | unfolding lemma for `gibbsCovariance` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_self_eq_variance` | `Cov_β(O, O) = Var_β(O)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_sub_swap_eq_commutator` | `Cov_β(A, B) − Cov_β(B, A) = ⟨A · B − B · A⟩_β` (antisymmetric part = commutator expectation) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_add_left` | `Cov_β(A₁ + A₂, B) = Cov_β(A₁, B) + Cov_β(A₂, B)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_add_right` | `Cov_β(A, B₁ + B₂) = Cov_β(A, B₁) + Cov_β(A, B₂)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_smul_left` | `Cov_β(c • A, B) = c · Cov_β(A, B)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_smul_right` | `Cov_β(A, c • B) = c · Cov_β(A, B)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_const_smul_one_{left,right}_eq_zero` | `Cov_β(c • 1, B) = 0` and `Cov_β(A, c • 1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_const_smul_one_{left,right}_eq_zero` | `Cov^s_β(c • 1, B) = 0` and `Cov^s_β(A, c • 1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm β H A B` | `Cov^s_β(A, B) := (1/2) · ⟨A · B + B · A⟩_β − ⟨A⟩_β · ⟨B⟩_β` (symmetric / real-valued covariance) | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_self_eq_variance` | `Cov^s_β(O, O) = Var_β(O)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovarianceSymm_im_of_isHermitian` | `(Cov^s_β(A, B)).im = 0` for Hermitian `H, A, B` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovarianceSymm_comm` | `Cov^s_β(A, B) = Cov^s_β(B, A)` (symmetric in observables) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovarianceSymm_add_{left,right}` | additivity of `Cov^s_β` in each argument | `Quantum/GibbsState.lean` |
| `gibbsCovarianceSymm_smul_{left,right}` | scalar pull-out from each argument of `Cov^s_β` | `Quantum/GibbsState.lean` |
| `gibbsVariance_add` | `Var_β(A + B) = Var_β(A) + Var_β(B) + 2 · Cov^s_β(A, B)` (sum-of-observables variance identity) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_one` | `Var_β(1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_smul` | `Var_β(c • A) = c² · Var_β(A)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_smul_one` | `Var_β(c • 1) = 0` (when `Z ≠ 0`) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_neg` | `Var_β(−A) = Var_β(A)` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsVariance_add_const_smul_one` | `Var_β(A + c • 1) = Var_β(A)` (when `Z ≠ 0`) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_eq_symm_add_half_commutator` | `Cov_β(A, B) = Cov^s_β(A, B) + (1/2) · ⟨A · B − B · A⟩_β` (symmetric / antisymmetric decomposition) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovarianceSymm_eq_half_add_swap` | `Cov^s_β(A, B) = (1/2) · (Cov_β(A, B) + Cov_β(B, A))` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsCovariance_eq_symm_of_commute` | for commuting `A, B`, `Cov_β(A, B) = Cov^s_β(A, B)` | `Quantum/GibbsState/Covariance.lean` |
| `Matrix.trace_mul_conjTranspose_swap_of_isHermitian` | `star Tr(ρ · X) = Tr(ρ · Xᴴ)` for Hermitian `ρ` (generic helper) | `Quantum/GibbsState.lean` |
| `gibbsExpectation_star_swap_of_isHermitian` | `star ⟨A · B⟩_β = ⟨B · A⟩_β` for Hermitian `H, A, B` | `Quantum/GibbsState/Covariance.lean` |
| `gibbsExpectation_anticommutator_im` | `(⟨A·B + B·A⟩_β).im = 0` (anticommutator is real) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsExpectation_commutator_re` | `(⟨A·B − B·A⟩_β).re = 0` (commutator is purely imaginary) | `Quantum/GibbsState/Covariance.lean` |
| `gibbsExpectation_mul_hamiltonian_im` | `(⟨H · O⟩_β).im = 0` for Hermitian `H, O` | `Quantum/GibbsState/Covariance.lean` |

<!-- legacy-source:end:1349:1443 -->

---

[← Testing infrastructure](/lattice-system/formalization/legacy/23-testing-infrastructure/) · [Catalogue](/lattice-system/formalization/legacy/) · [Heisenberg chain (Tasaki §3.5) →](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01/)
