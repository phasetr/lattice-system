import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandEigenbasis

/-!
# Ground-state Fock spanning, eq. (11.3.46) (Tasaki §11.3.4, toward Theorem 11.17)

A flat-band Hubbard ground state at filling `N = D₀` lies in the Fock span of the flat-band
(zero-eigenvalue) modes.  Using the spectral eigenbasis of the hopping matrix `T` and the
eigenbasis-annihilation peel (`GeneralFlatBandEigenbasis.lean`): a ground state is annihilated by
`Ĉ_σ(ē_j)` for every nonzero-eigenvalue mode `j` (PR1), and the peel shows that such an annihilator
detects occupation of mode `(j, σ)`; so the ground state's occupation lives entirely on the flat
band.

This module records the algebraic inputs: the eigenvalue equation for the transported eigenbasis,
the resulting ground-state annihilation, and the vanishing of the peel on a monomial not containing
the probed mode.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.46).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- The transported eigenbasis satisfies the eigenvalue equation of `T`:
`T·e_j = λ_j • e_j`. -/
theorem eigenbasisAsBasis_mulVec {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (j : Fin (M + 1)) :
    T.mulVec (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)
      = (hT.eigenvalues j : ℂ) • (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) := by
  rw [eigenbasisAsBasis_apply, hT.mulVec_eigenvectorBasis]
  funext i
  simp [Complex.real_smul]

/-- **A flat-band ground state is annihilated by every nonzero-eigenvalue eigenmode**
`Ĉ_σ(ē_j)` (the operative content of eq. (11.3.46)): combining the precise range-`T` annihilation
(PR1) with the eigenvalue equation of the transported eigenbasis. -/
theorem groundState_eigenModeAnnihilation_eq_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) Φ = 0) (σ : Fin 2) (j : Fin (M + 1))
    (hj : hT.1.eigenvalues j ≠ 0) :
    (spinfulAnnihilationFromVector M
        (star (eigenbasisAsBasis hT.1 j : Fin (M + 1) → ℂ)) σ).mulVec Φ = 0 :=
  spinfulAnnihilation_starEigenvector_mulVec_eq_zero_of_groundState M T U hT hU hΦ σ
    (lam := (hT.1.eigenvalues j : ℂ)) (Complex.ofReal_ne_zero.mpr hj)
    (eigenbasisAsBasis_mulVec hT.1 j)

/-- **The eigenmode annihilator kills a monomial not containing its mode**: if `(j, σ) ∉ qs`,
then `Ĉ_σ(ē_j)|qs⟩ = 0` (every peel amplitude is the Kronecker delta `δ_{(j,σ),(qs[i])}`, which
vanishes since `(j,σ)` is absent). -/
theorem eigenModeAnnihilation_mulVec_generalModeMonomial_eq_zero_of_not_mem
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j : Fin (M + 1)) (σ : Fin 2)
    (qs : List (Fin (M + 1) × Fin 2)) (h : (j, σ) ∉ qs) :
    (spinfulAnnihilationFromVector M (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ).mulVec
        (generalModeMonomial (eigenbasisAsBasis hT) qs) = 0 := by
  rw [eigenModeAnnihilation_peel]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hne : ¬ (j = (qs.get i).1 ∧ σ = (qs.get i).2) := by
    rintro ⟨h1, h2⟩
    exact h (show (j, σ) ∈ qs from by
      rw [show (j, σ) = qs.get i from Prod.ext h1 h2]; exact List.get_mem qs i)
  rw [eigenModePeelTerm, if_neg hne, zero_smul, smul_zero]

/-- **The eigenmode number operator** `n̂_{j,σ} = Ĉ†_σ(e_j)·Ĉ_σ(ē_j)` counts the occupation of the
eigenmode `(j, σ)`. -/
noncomputable def eigenNumberOp {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (j : Fin (M + 1)) (σ : Fin 2) : ManyBodyOp (Fin (2 * M + 2)) :=
  spinfulCreationFromVector M (eigenbasisAsBasis hT j) σ
    * spinfulAnnihilationFromVector M (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ

/-- **The number-operator/creation commutation** `n̂_{j,σ}·Ĉ†_τ(e_k) = δ_{jk}δ_{στ}·Ĉ†_τ(e_k) +
Ĉ†_τ(e_k)·n̂_{j,σ}`: creating mode `(k,τ)` raises the `(j,σ)`-count by `δ`.  From the dual CAR and
the creation–creation anticommutation. -/
theorem eigenNumberOp_mul_creation {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (j k : Fin (M + 1)) (σ τ : Fin 2) :
    eigenNumberOp hT j σ * spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ
      = (if j = k ∧ σ = τ then (1 : ℂ) else 0)
          • spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ
        + spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ * eigenNumberOp hT j σ := by
  have hdual : spinfulAnnihilationFromVector M
        (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ
      * spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ
      = (if j = k ∧ σ = τ then (1 : ℂ) else 0) • 1
        - spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ
          * spinfulAnnihilationFromVector M
              (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ := by
    rw [eq_sub_iff_add_eq]
    exact eigenbasis_dual_annihilation_creation_anticomm hT j k σ τ
  have hcc : spinfulCreationFromVector M (eigenbasisAsBasis hT j) σ
        * spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ
      = - (spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ
          * spinfulCreationFromVector M (eigenbasisAsBasis hT j) σ) :=
    eq_neg_of_add_eq_zero_left
      (spinfulFromVector_creation_creation_anticomm M (eigenbasisAsBasis hT j)
        (eigenbasisAsBasis hT k) σ τ)
  have hδ : (if j = k ∧ σ = τ then (1 : ℂ) else 0)
        • spinfulCreationFromVector M (eigenbasisAsBasis hT j) σ
      = (if j = k ∧ σ = τ then (1 : ℂ) else 0)
        • spinfulCreationFromVector M (eigenbasisAsBasis hT k) τ := by
    by_cases h : j = k ∧ σ = τ
    · rw [h.1, h.2]
    · rw [if_neg h, zero_smul, zero_smul]
  rw [eigenNumberOp, Matrix.mul_assoc, hdual, mul_sub, mul_smul_comm, Matrix.mul_one,
    ← Matrix.mul_assoc, hcc, Matrix.neg_mul, sub_neg_eq_add, hδ, Matrix.mul_assoc]

end LatticeSystem.Fermion
