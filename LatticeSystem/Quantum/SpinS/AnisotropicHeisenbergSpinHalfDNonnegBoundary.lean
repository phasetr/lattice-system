import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfTargetUniquenessFromBalancedPF

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Spin-1/2 `D >= 0` boundary for Theorem 2.4 parity-block finrank

Issue #412 — Tasaki §2.5 Theorem 2.4.

This file extends the spin-1/2 parity-block Perron--Frobenius route in the
`D` direction.  The generic spin-`S` proof assumes `0 < D.re` because
single-ion `±2` moves need strict single-ion matrix entries.  At spin `1/2`
those single-ion moves are impossible on `Fin (1 + 1)`, so the parity-block
irreducibility and global `finrank <= 2` theorem only need `0 <= D.re`.

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
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_parityReachable_spinHalf_D_nonneg
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
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total_spinHalf_D_nonneg
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
      shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_parityReachable_spinHalf_D_nonneg
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
  refine shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total_spinHalf_D_nonneg
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict p ?_
  intro σ' σ _hne
  refine parityReachableS_total A hA_ne hB_ne (by norm_num : 1 ≤ 1) ?_
  have hp_σ : magSumS σ.1 % 2 = p := σ.2
  have hp_σ' : magSumS σ'.1 % 2 = p := σ'.2
  omega

/-! ## Spin-half PF/minimum identification with `D >= 0` -/

/-- Spin-`1/2` PF positive eigenvector for the unshifted dressed parity-block
submatrix with nonnegative `D`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_spinHalf_D_nonneg
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

set_option linter.style.longLine false in
/-- Spin-`1/2` dressed submatrix Hermitian minimum identification with
nonnegative `D`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_spinHalf_D_nonneg
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
    dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_spinHalf_D_nonneg
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

set_option linter.style.longLine false in
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
    dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne
      p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hlam hDim p]
  exact hν_eq

set_option linter.style.longLine false in
/-- Spin-`1/2` bare parity-block submatrix `finrank <= 1` at its Hermitian
minimum with nonnegative `D`. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue_spinHalf_D_nonneg
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

set_option linter.style.longLine false in
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
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue_spinHalf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDnn hc_strict hA_ne hB_ne 0
  have h1 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue_spinHalf_D_nonneg
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

/-- Along the Theorem 2.4 deformation path, nonnegative target `D` stays
nonnegative. -/
theorem anisotropicHeisenbergParametricPath_snd_nonneg
    {lam' D' : ℝ} (hD' : 0 ≤ D') {t : ℝ} (ht_nn : 0 ≤ t) :
    0 ≤ (anisotropicHeisenbergParametricPath lam' D' t).2 := by
  unfold anisotropicHeisenbergParametricPath
  change 0 ≤ t * D'
  exact mul_nonneg ht_nn hD'

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

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) under a single SU(2)-point strict-gap axiom,
with target `D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom_D_nonneg
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    (axiom_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ 1 M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M' lam' D' 0) :
    False := by
  have axiom_GS_at_SU2 :=
    strict_GS_at_path_zero_from_strict_gap_at_SU2 (Λ := Λ) hJ_star 1 M_balanced
      lam' D' (fun M' _ hne => by
        haveI := ‹Nonempty (magConfigS Λ 1 M')›
        have := axiom_strict_gap_at_SU2 M' hne
        unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at this
        have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
        simp only [hpath] at this
        exact this)
  classical
  have hne_orig : (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_orig lam' D' ∩
      Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, h_violation_orig, ⟨by norm_num, le_refl _⟩⟩
  obtain ⟨M_chosen, hM_chosen_range, hM_chosen_ne_bal, hM_chosen_NE,
          hM_chosen_cross_total, h_argmin_total⟩ :=
    exists_M_chosen_argmin_per_M_first_crossing
      hJ_star 1 M_balanced M_orig hM_orig_ne lam' D' hne_orig
  haveI := hM_chosen_NE
  have hM_chosen_cross :
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1).Nonempty := by
    rw [← perMCrossingSet_total_eq_perMCrossingSet]
    exact hM_chosen_cross_total
  have hM_chosen_centered_ne : (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) -
      (M_chosen : ℂ)) ≠ 0 :=
    h_centered_nonzero M_chosen hM_chosen_range hM_chosen_ne_bal
  have h_strict_chosen :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_chosen lam' D' 0 :=
    axiom_strict_gap_at_SU2 M_chosen hM_chosen_ne_bal
  have h_argmin : ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M'), M' ≠ M_balanced →
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
      sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1) ≤
      sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩
        Icc (0 : ℝ) 1) := by
    intro M' hNE_M' h_ne_bal_M' h_cross_M'
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    have h_cross_M'_total :
        (perMCrossingSet_total (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩
          Icc (0 : ℝ) 1).Nonempty := by
      rw [perMCrossingSet_total_eq_perMCrossingSet]
      exact h_cross_M'
    have h_le_total := h_argmin_total M' hM'_range h_ne_bal_M' hNE_M' h_cross_M'_total
    rw [perMCrossingSet_total_eq_perMCrossingSet,
        perMCrossingSet_total_eq_perMCrossingSet] at h_le_total
    exact h_le_total
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star 1 M_balanced M_chosen lam' D' hM_chosen_cross h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star 1 M_balanced M_chosen lam' D'
      hM_chosen_cross h_argmin)
  exact spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_chosen h_balanced hM_chosen_centered_ne hlam'_lb hlam'_ub hD'
    hM_chosen_cross h_strict_chosen axiom_GS_at_SU2 h_below

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) from SU(2) global uniqueness with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_D_nonneg
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1)
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0)) :
    False := by
  classical
  have h_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ 1 M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M' lam' D' 0 := by
    intro M' hNE_M' hM'_ne_bal
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    exact strict_gap_at_path_zero_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced M' lam' D'
      h_balanced (h_centered_nonzero M' hM'_range hM'_ne_bal)
      h_SU2_global_unique h_GS_at_SU2
  exact spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_strict_gap_at_SU2

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) from only SU(2) global uniqueness with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_D_nonneg
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1) :
    False := by
  classical
  have h_GS_at_SU2 :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced h_balanced h_SU2_global_unique
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique h_GS_at_SU2

/-- Transport Heisenberg ground-line uniqueness at the SU(2) point to the
anisotropic Hamiltonian written with `(lambda, D) = (1, 0)`. -/
private theorem anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_D_nonneg_aux
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (1 + 1))]
    {μ : ℝ}
    (hμ : hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ_star 1) = μ)
    (huniq :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J 1))
        (μ : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
      ((hermitianMinEigenvalue (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
        ℝ) : ℂ)) ≤ 1 := by
  have hmin :
      hermitianMinEigenvalue (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) =
        μ := by
    simpa [anisotropicHeisenbergS_one_zero] using hμ
  have h_eigsp_eq := anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS
    (Λ := Λ) (N := 1) J
    (((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) : ℝ) : ℂ))
  rw [h_eigsp_eq]
  rw [hmin]
  exact huniq

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) from the MLM/Casimir endpoint with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1) :
    False := by
  classical
  have hJ_bipartite_zero : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    obtain ⟨a, ha⟩ := hA_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, by simp [ha]⟩)
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    obtain ⟨b, hb⟩ := hB_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨b, by simp [hb]⟩)
  have h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := Λ) hJ_star 1) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J 1
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * 1))) (μ : ℂ)) ≤ 1 :=
    fun μ hmin_eq =>
      tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min
        (V := Λ) A 1 c_mlm hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
        hJpos hc_heis_strict h_card_eq (by norm_num) hcardA hcardB hmin_eq
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    LatticeSystem.Quantum.exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder
      (V := Λ) A 1 c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq (by norm_num) hcardA hcardB h_sector_pf
  have h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1 :=
    anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_D_nonneg_aux
      (Λ := Λ) hJ_star hμ_min huniq_heis
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_axis_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) strict-gap form from the MLM/Casimir endpoint and
Theorem 2.3 sector PF, with target `D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_strict_gap_of_MLM_casimir_ladder_t23_pf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_orig lam' D' 1 := by
  classical
  exact lt_of_not_ge (by
    intro h_violation_orig
    exact spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
      hlam'_lb hlam'_ub hD' h_violation_orig)

set_option linter.style.longLine false in
/-- Spin-`1/2` strict gap for every non-balanced sector, with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_strict_gap_all_M_of_MLM_casimir_ladder_t23_pf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (M : ℕ) [Nonempty (magConfigS Λ 1 M)] (hM_ne : M ≠ M_balanced) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M lam' D' 1 := by
  classical
  have hM_range : M ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
    rw [Finset.mem_range]
    obtain ⟨σ⟩ := (inferInstance : Nonempty (magConfigS Λ 1 M))
    have hbound := magSumS_le σ.val
    rw [σ.property] at hbound
    exact Nat.lt_succ_of_le hbound
  exact spinHalf_anisotropicHeisenbergS_obligation_2_strict_gap_of_MLM_casimir_ladder_t23_pf_D_nonneg
    A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
    c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
    M_balanced M h_balanced hM_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD'

set_option linter.style.longLine false in
/-- Spin-`1/2` balanced sector is the full target ground sector, with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_balanced_eq_full_of_MLM_casimir_ladder_t23_pf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') := by
  classical
  have h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M) hJ_star lam' D') := by
    intro M hM_nonempty hM_ne
    haveI := hM_nonempty
    have hpath :=
      spinHalf_anisotropicHeisenbergS_strict_gap_all_M_of_MLM_casimir_ladder_t23_pf_D_nonneg
        A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
        c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
        M_balanced h_balanced h_centered_nonzero
        hlam'_lb hlam'_ub hD' M hM_ne
    unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at hpath
    simpa using hpath
  exact hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
    hJ_star 1 M_balanced lam' D' h_strict_gap

set_option linter.style.longLine false in
/-- Spin-`1/2` target ground eigenspace `finrank <= 1` in the case-(i)
`D' >= 0` boundary strip. -/
theorem spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ)) ≤
      1 := by
  classical
  set μ_sector : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') with hμ_sector_def
  set μ_full : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') with hμ_full_def
  have h_bal_full :=
    spinHalf_anisotropicHeisenbergS_balanced_eq_full_of_MLM_casimir_ladder_t23_pf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'
  have hμ_eq : ((μ_sector : ℝ) : ℂ) = ((μ_full : ℝ) : ℂ) := by
    rw [hμ_sector_def, hμ_full_def]
    exact congrArg (fun x : ℝ => (x : ℂ)) h_bal_full
  have h_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
      ((μ_full : ℝ) : ℂ)) ≤ 2 := by
    have hraw :=
      spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg
        A hJim hJnn hJpos hJself hJbip
        (by simp) hlam'_lb hlam'_ub (by simp) hD'
        (hc_axis_strict (lam' : ℂ) (D' : ℂ)) hA_ne hB_ne hJ_star
        (show star (lam' : ℂ) = (lam' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
        (show star (D' : ℂ) = (D' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
    simpa [hμ_full_def, anisotropicHeisenbergS_full_isHermitian_real] using hraw
  have h_balanced_sector_pf :=
    spinHalf_anisotropicHeisenbergS_balanced_sector_pf_at_target
      A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne M_balanced
      (lam' := lam') (D' := D')
  have h_admis_pf : finrank ℂ ↥((End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
        ((μ_full : ℝ) : ℂ)) ⊓ magSubspaceS Λ 1 0) ≤ 1 := by
    have h_transfer :=
      anisotropicHeisenbergS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
        (Λ := Λ) (N := 1) J (lam' : ℂ) (D' : ℂ) M_balanced
        ((μ_sector : ℝ) : ℂ) (by simpa [hμ_sector_def] using h_balanced_sector_pf)
    rw [h_balanced] at h_transfer
    rw [hμ_eq] at h_transfer
    exact h_transfer
  obtain ⟨Φ_sector, hΦ_sector_ne, hΦ_eig, hΦ_admis⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS
      (Λ := Λ) hJ_star lam' D' 1 M_balanced
  set Φ : (Λ → Fin (1 + 1)) → ℂ := magSectorEmbedding Φ_sector with hΦ_def
  have hΦ_ne : Φ ≠ 0 := by
    intro hzero
    apply hΦ_sector_ne
    have hres := congrArg
      (magSectorRestriction (V := Λ) (N := 1) (M := M_balanced)) hzero
    simpa [hΦ_def, magSectorRestriction_magSectorEmbedding,
      magSectorRestriction_zero] using hres
  have hΦ_admis0 : Φ ∈ magSubspaceS Λ 1 0 := by
    have h_balanced' : ((Fintype.card Λ : ℂ) / 2 - (M_balanced : ℂ)) = 0 := by
      simpa using h_balanced
    simpa [hΦ_def, h_balanced', zero_smul] using hΦ_admis
  have hΦ_eig_full :
      (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) 1).mulVec Φ =
        ((μ_full : ℝ) : ℂ) • Φ := by
    have h := hΦ_eig
    rw [hΦ_def] at h
    rw [hμ_sector_def] at hμ_eq
    rw [hμ_eq] at h
    exact h
  exact anisotropicHeisenbergS_finrank_le_one_from_admis_pf
    J (lam' : ℂ) (D' : ℂ) ((μ_full : ℝ) : ℂ)
    h_two hΦ_admis0 hΦ_ne hΦ_eig_full h_admis_pf

set_option linter.style.longLine false in
/-- Spin-`1/2` target ground states have zero magnetization in the case-(i)
`D' >= 0` boundary strip. -/
theorem spinHalf_anisotropicHeisenbergS_target_groundState_zero_magnetization_of_MLM_casimir_ladder_t23_pf_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ) •
        Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  classical
  have huniq :=
    spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
