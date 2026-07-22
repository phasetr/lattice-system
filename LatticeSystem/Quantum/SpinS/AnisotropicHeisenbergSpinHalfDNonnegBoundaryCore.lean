import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfTargetUniquenessFromBalancedPF

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Spin-1/2 `D >= 0` boundary for Theorem 2.4 — parity-block core

Foundational layer of the spin-1/2 `D >= 0` parity-block Perron--Frobenius route (Tasaki §2.5
Theorem 2.4, Issue #412): single-ion `±2` impossibility at spin 1/2, shifted-dressed parity-block
positivity / irreducibility, the PF positive eigenvector, the Hermitian-min-eigenvalue = PF identity,
the parity-block `finrank <= 1` and the global `finrank <= 2` (truly unconditional / at-global-min /
path) theorems.

Split out of `AnisotropicHeisenbergSpinHalfDNonnegBoundary.lean` (periodic build-speed refactor) so
the heavier obligation-(2) / strict-gap / target-finrank capstone compiles against a smaller
dependency set.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/
namespace LatticeSystem.Quantum

open Matrix Module Set LatticeSystem.Math.PerronFrobenius

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
/-! ## Spin-half parity-step positivity with `D >= 0` -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- A spin-`1/2` configuration cannot make a single-ion `±2` step. -/
theorem singleIonStepS_spinHalf_false {σ τ : Λ → Fin (1 + 1)}
    (h : SingleIonStepS σ τ) : False := by
  rcases h with ⟨x, hx | hx, _hagree⟩
  · have hlt := (τ x).isLt
    omega
  · have hlt := (σ x).isLt
    omega

/-- Spin-`1/2` parity-step strict positivity with nonnegative `D`: the
single-ion case is impossible, while transverse and bond-parity steps already
only need `D.re >= 0`. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityStepS_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (1 + 1)} (hstep : ParityStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D 1 c τ σ := by
  rcases hstep with hRL | hPB | hSI
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite
      A hJim hJnn hJpos hJself hJbip hlam hlb (le_of_lt hub) hDim hDnn c hRL
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_bipartite
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn c hPB
  · exact False.elim (singleIonStepS_spinHalf_false hSI)

/-- Spin-`1/2` block matrix power positivity from parity reachability with
nonnegative `D`. -/
theorem shiftedDressedReMatParity_pow_apply_pos_of_parityReach_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ 1 p}
    (hreach : ParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p ^ k) σ' σ := by
  have hB_nn : ∀ ρ τ, 0 ≤ shiftedDressedAxisSwappedReMatrix A J lam D 1 c ρ τ :=
    fun ρ τ => shiftedDressedAxisSwappedReMatrix_nonneg A hJim hJnn hJself hJbip hlam
      (le_of_lt hlb) (le_of_lt hub) hDim hDnn hc ρ τ
  have hB_step : ∀ {ρ τ : Λ → Fin (1 + 1)},
      ParityStepS (bipartiteCompleteGraphOf A) ρ τ →
        0 < shiftedDressedAxisSwappedReMatrix A J lam D 1 c τ ρ :=
    fun {ρ τ} hstep =>
      shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityStepS_spinHalf_D_nonneg
        A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn c hstep
  obtain ⟨k, hpow_pos⟩ := exists_matrixPow_apply_pos_of_parityReachableS
    (G := bipartiteCompleteGraphOf A) (N := 1)
    (B := shiftedDressedAxisSwappedReMatrix A J lam D 1 c) hB_nn hB_step hreach
  refine ⟨k, ?_⟩
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply A hJself]
  exact hpow_pos

/-- Spin-`1/2` parity-block shifted PF matrix irreducibility under reachability
totality, with `D.re >= 0`. -/
theorem shiftedDressedReMatParity_irred_of_parityReach_total_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ 1 p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ 1 p, σ' ≠ σ →
      ParityReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p).IsIrreducible := by
  have hc_le : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ ≤ c := fun σ =>
    le_of_lt (hc_strict σ)
  have h_nn : ∀ σ' σ : parityConfigS Λ 1 p,
      0 ≤ shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p σ' σ :=
    fun σ' σ => shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg A hJim hJnn hJself hJbip hlam
      (le_of_lt hlb) (le_of_lt hub) hDim hDnn hc_le p σ' σ
  rw [Matrix.isIrreducible_iff_exists_pow_pos h_nn]
  intro σ' σ
  by_cases hsig : σ' = σ
  · subst hsig
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_diag_pos A J lam D 1 p (hc_strict σ'.1)
  · have hreach := hreach_total σ' σ hsig
    obtain ⟨k, hk⟩ :=
      shiftedDressedReMatParity_pow_apply_pos_of_parityReach_spinHalf_D_nonneg
        A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_le p hreach
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkp
      · subst hk0
        rw [pow_zero, Matrix.one_apply_ne hsig] at hk
        exact absurd hk (lt_irrefl 0)
      · exact hkp
    exact ⟨k, hk_pos, hk⟩

/-- Spin-`1/2` structural shifted parity-block irreducibility with
nonnegative `D`. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (p : ℕ)
    [Nonempty (parityConfigS Λ 1 p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p).IsIrreducible := by
  refine shiftedDressedReMatParity_irred_of_parityReach_total_spinHalf_D_nonneg
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict p ?_
  intro σ' σ _hne
  refine parityReachableS_total A hA_ne hB_ne (by norm_num : 1 ≤ 1) ?_
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

/-! ## Spin-half PF/minimum identification with `D >= 0` -/

/-- Spin-`1/2` PF positive eigenvector for the unshifted dressed parity-block
submatrix with nonnegative `D`. -/
theorem dressedAxisSwapReMatParity_pos_eigenvector_exists_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (p : ℕ)
    [Nonempty (parityConfigS Λ 1 p)] :
    ∃ (ν : ℝ) (v : parityConfigS Λ 1 p → ℝ),
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1)) v = ν • v := by
  have hSymm := shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (N := 1) A hJim hlam hDim c p
  have hHerm :
      (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSymm
  have hIrred := shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_spinHalf_D_nonneg
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict
    hA_ne hB_ne p
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ := exists_pos_eigenvec_max hHerm hIrred
  have heq := @shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
    Λ _ _ 1 A J lam D c p
  rw [heq] at hAv
  refine ⟨c - μ, v, hv_pos, ?_⟩
  set M : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1).submatrix
      (fun σ : parityConfigS Λ 1 p => σ.1)
      (fun σ : parityConfigS Λ 1 p => σ.1) with hM_def
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hAv
  have heq2 : Matrix.mulVec M v = c • v - μ • v := by linear_combination -hAv
  rw [heq2, sub_smul]

/-- Spin-`1/2` dressed submatrix Hermitian minimum identification with
nonnegative `D`. -/
theorem dressedAxisSwapAHeisS_submat_hMinEig_eq_pf_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (p : ℕ)
    [Nonempty (parityConfigS Λ 1 p)] :
    ∃ ν : ℝ, ∃ v : parityConfigS Λ 1 p → ℝ,
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1)) v = ν • v ∧
      ν = hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) A hJim hlam hDim p) := by
  obtain ⟨ν, v, hv_pos, hAv⟩ :=
    dressedAxisSwapReMatParity_pos_eigenvector_exists_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn
      hc_strict hA_ne hB_ne p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  set M_real : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1).submatrix
      (fun σ : parityConfigS Λ 1 p => σ.1)
      (fun σ : parityConfigS Λ 1 p => σ.1) with hM_def
  have hM_symm : M_real.IsSymm :=
    Matrix.IsSymm.submatrix
      (dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real (N := 1) A hJim hlam hDim) _
  have hShift_eq : shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p =
      c • (1 : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ) - M_real :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
      (N := 1) A J lam D c p
  have h_eig_shifted :
      (c • (1 : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ) - M_real).mulVec v =
        (c - ν) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_smul]
  have hB_symm :
      (c • (1 : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ) - M_real).IsSymm := by
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
      (N := 1) A hJim hlam hDim c p
  have hB_nn :
      ∀ i j, 0 ≤ (c • (1 : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ) - M_real) i j := by
    intro i j
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg
      A hJim hJnn hJself hJbip hlam (le_of_lt hlb) (le_of_lt hub) hDim
      hDnn (fun σ => le_of_lt (hc_strict σ)) p i j
  have h_min_lift :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
        c - (c - ν) :=
    LatticeSystem.Math.CollatzWielandt.hermitianMinEigenvalue_lift_eq_sub_pf
      hM_symm c hB_nn hB_symm h_eig_shifted hv_pos
  have h_mat_eq :
      M_real.map ((↑) : ℝ → ℂ) =
        (dressedAxisSwappedAnisotropicHeisenbergS A J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1) :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
      A hJim hJself hlam hDim p
  have h_spec_eq :
      spectrum ℝ (M_real.map ((↑) : ℝ → ℂ)) =
        spectrum ℝ ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1)) := by
    rw [h_mat_eq]
  have h_min_bridge :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
      hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) A hJim hlam hDim p) :=
    hermitianMinEigenvalue_eq_of_spectrum_eq _ _ h_spec_eq
  linarith [h_min_lift, h_min_bridge]

/-- Spin-`1/2` bare submatrix Hermitian minimum identification with
nonnegative `D`. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (p : ℕ)
    [Nonempty (parityConfigS Λ 1 p)] :
    ∃ ν : ℝ, ∃ v : parityConfigS Λ 1 p → ℝ,
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1)) v = ν • v ∧
      ν = hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) hJim hlam hDim p) := by
  obtain ⟨ν, v, hv_pos, hAv, hν_eq⟩ :=
    dressedAxisSwapAHeisS_submat_hMinEig_eq_pf_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne
      p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hlam hDim p]
  exact hν_eq

/-- Spin-`1/2` bare parity-block submatrix `finrank <= 1` at its Hermitian
minimum with nonnegative `D`. -/
theorem axisSwapAHeisS_submat_finrank_le_one_at_hMinEig_spinHalf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (p : ℕ)
    [Nonempty (parityConfigS Λ 1 p)] :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1).submatrix
        (fun σ : parityConfigS Λ 1 p => σ.1)
        (fun σ : parityConfigS Λ 1 p => σ.1)))
      ((hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) hJim hlam hDim p) : ℂ))) ≤ 1 := by
  obtain ⟨ν, v, hv_pos, hAv, hν_eq⟩ :=
    axisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne
      p
  have h_eig_shifted :
      Matrix.mulVec (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p) v =
        (c - ν) • v := by
    rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
          (N := 1) A J lam D c p]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_smul]
  have hIrred :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict
      hA_ne hB_ne p
  have h_finrank_shifted_R :
      finrank ℝ ↥(End.eigenspace (Matrix.toLin'
        (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p)) (c - ν)) ≤ 1 :=
    LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
      hIrred h_eig_shifted hv_pos
  set M_real : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1).submatrix
      (fun σ : parityConfigS Λ 1 p => σ.1)
      (fun σ : parityConfigS Λ 1 p => σ.1) with hM_def
  have hShift_eq :
      shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D 1 c p =
        c • (1 : Matrix (parityConfigS Λ 1 p) (parityConfigS Λ 1 p) ℝ) - M_real :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
      (N := 1) A J lam D c p
  rw [hShift_eq] at h_finrank_shifted_R
  rw [eigenspace_smul_one_sub_finrank_eq] at h_finrank_shifted_R
  have h_finrank_M_R : finrank ℝ ↥(End.eigenspace (Matrix.toLin' M_real) ν) ≤ 1 := by
    have : c - (c - ν) = ν := by ring
    rw [← this]
    exact h_finrank_shifted_R
  have h_finrank_M_C :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (M_real.map ((↑) : ℝ → ℂ))) (ν : ℂ)) ≤ 1 :=
    matrix_complex_eigenspace_finrank_le_one_of_real M_real ν h_finrank_M_R
  have hMap :
      M_real.map ((↑) : ℝ → ℂ) =
        (dressedAxisSwappedAnisotropicHeisenbergS A J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1) :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
      A hJim hJself hlam hDim p
  rw [hMap] at h_finrank_M_C
  have h_finrank_bare :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 p => σ.1)
          (fun σ : parityConfigS Λ 1 p => σ.1))) (ν : ℂ)) ≤ 1 := by
    have h_similarity_finrank :=
      matrix_similar_eigenspace_finrank_eq
        (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := 1) A p)
        (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := 1) A p)
        (dressedAxisSwapped_submatrix_eq_marshall_conj_bare A J lam D p) (ν : ℂ)
    rw [h_similarity_finrank] at h_finrank_M_C
    exact h_finrank_M_C
  exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_min_conditional
    hJim hlam hDim p ν h_finrank_bare hν_eq

/-- Spin-`1/2` anisotropic `H` eigenspace `finrank <= 2` at
`min(per-block mins)` with nonnegative `D`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)] :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D 1))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJim hlam hDim 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJim hlam hDim 1)) : ℝ) : ℂ)) ≤ 2 := by
  have h0 :=
    axisSwapAHeisS_submat_finrank_le_one_at_hMinEig_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne 0
  have h1 :=
    axisSwapAHeisS_submat_finrank_le_one_at_hMinEig_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne 1
  exact spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    hJim hlam hDim hJself h0 h1

set_option linter.style.longLine false in
/-- Spin-`1/2` anisotropic `H` eigenspace `finrank <= 2` at its global
Hermitian minimum with nonnegative `D`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hlam_star : star lam = lam) (hD_star : star D = D) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
          hJ_star hlam_star hD_star) : ℝ) : ℂ)) ≤ 2 := by
  have hbound := spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional_D_nonneg
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne
  have hblock_eq := hermitianMinEigenvalue_axisSwapped_eq_min_block_mins
    (Λ := Λ) (N := 1) hJim hlam hDim hJself
  have hswap_eq := AxisSwapUnitaryS.hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    (Λ := Λ) (N := 1) (G := axisSwapUnitarySpinHalf) hJ_star hlam_star hD_star
  have henergy_eq : (min (hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) hJim hlam hDim 0))
        (hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := 1) hJim hlam hDim 1)) : ℝ) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
          hJ_star hlam_star hD_star) := by
    rw [← hblock_eq, ← hswap_eq]
  rw [henergy_eq] at hbound
  exact hbound

/-! ## Deformation-path and target wrappers with `D >= 0` -/

/-- Spin-`1/2` `finrank <= 2` at the global minimum along the parametric path,
with `D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    {t : ℝ} (ht_pos : 0 < t) (ht_le : t ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J
        ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
        ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
          hJ_star
          (show star ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) =
              ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])
          (show star ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) =
              ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])) : ℝ) : ℂ)) ≤ 2 := by
  have hlb := anisotropicHeisenbergParametricPath_neg_one_lt_fst
    (D' := D') hlam'_lb (le_of_lt ht_pos) ht_le
  have hub := anisotropicHeisenbergParametricPath_fst_lt_one
    (D' := D') hlam'_ub ht_pos ht_le
  have hDnn := anisotropicHeisenbergParametricPath_snd_nonneg
    (lam' := lam') hD' (le_of_lt ht_pos)
  set lam_t : ℂ := ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
  set D_t : ℂ := ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ)
  have hlam_t_im : lam_t.im = 0 := by simp [lam_t]
  have hD_t_im : D_t.im = 0 := by simp [D_t]
  have hlam_t_re : lam_t.re = (anisotropicHeisenbergParametricPath lam' D' t).1 := by
    simp [lam_t]
  have hD_t_re : D_t.re = (anisotropicHeisenbergParametricPath lam' D' t).2 := by
    simp [D_t]
  have hlam_t_star : star lam_t = lam_t := by
    rw [Complex.star_def]; simp [lam_t]
  have hD_t_star : star D_t = D_t := by
    rw [Complex.star_def]; simp [D_t]
  have hlb_t : -1 < lam_t.re := by rw [hlam_t_re]; exact hlb
  have hub_t : lam_t.re < 1 := by rw [hlam_t_re]; exact hub
  have hDnn_t : 0 ≤ D_t.re := by rw [hD_t_re]; exact hDnn
  exact spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg
    A hJim hJnn hJpos hJself hJbip
    hlam_t_im hlb_t hub_t hD_t_im hDnn_t
    (hc_strict lam_t D_t) hA_ne hB_ne hJ_star hlam_t_star hD_t_star

set_option linter.style.longLine false in
/-- The deformation contradiction capstone with target `D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_ne_balanced :
      (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (hne :
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    (h_strict_gap_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M lam' D' 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2))
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ_star 1 M_balanced lam' D') :
    False := by
  classical
  set t := sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)
    with ht_def
  have hmem : t ∈ perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M lam' D' ∩ Icc (0 : ℝ) 1 :=
    sInf_perMCrossingSet_inter_Icc_mem hJ_star 1 M_balanced M lam' D' hne
  have ht_nn : 0 ≤ t := hmem.2.1
  have ht_le : t ≤ 1 := hmem.2.2
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le ht_nn with hpos | h0_eq
    · exact hpos
    · exfalso
      have h_in := hmem.1
      simp only [perMCrossingSet, Set.mem_setOf_eq] at h_in
      rw [← h0_eq] at h_in
      linarith
  have h_eq_at_t := anisotropicHeisenbergS_per_M_crossing_equality_at_sInf
    hJ_star 1 M_balanced M lam' D' hne h_strict_gap_SU2
  have h_bal_eq_full_def := balanced_min_eq_full_at_sInf
    hJ_star 1 M_balanced M lam' D' hne h_GS_at_SU2 h_balanced_GS_below
  have h_bal_eq_full : hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) := h_bal_eq_full_def
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, hΦ_bal_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M
  have h_eq_at_t' : hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := 1) (M := M) hJ_star
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) := h_eq_at_t
  rw [h_eq_at_t'] at hΦ_M_eig
  rw [h_bal_eq_full] at hΦ_bal_eig
  have h_finrank :=
    spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path_D_nonneg
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
      hlam'_lb hlam'_ub hD' ht_pos ht_le
  rw [h_bal_eq_full] at hΦ_M_eig
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig
    hΦ_M_ne hM_ne_balanced hΦ_M_eig


end LatticeSystem.Quantum
