import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinS
import LatticeSystem.Quantum.SpinS.BareSubmatrixBoundAtMin
import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityBlockIrreducibleLambdaOne
import LatticeSystem.Quantum.SpinS.DressedBareSubmatrixMinEqPFStructural
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSMLMEndpoint

/-!
# General spin-S `lambda = 1`, `D > 0` boundary for the parity-block capstone

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file lifts the general spin-`S` parity-block Perron--Frobenius capstone to
the case-(i) boundary `lambda = 1`, `D > 0`, `2 <= N`.  The new input is the
ion-only parity-block irreducibility theorem, which avoids the same-direction
parity-bond branch whose coefficient vanishes at `lambda = 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- General spin-`S` PF positive eigenvector for the unshifted dressed
axis-swapped parity-block submatrix at `lambda = 1`, `D.re > 0`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_lambda_one_D_pos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
  (p : ℕ)
  [Nonempty (parityConfigS Λ N p)] :
    ∃ (ν : ℝ) (v : parityConfigS Λ N p → ℝ),
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v := by
  have hOneIm : ((1 : ℂ).im = 0) := by norm_num
  have hSymm := shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (N := N) A hJim hOneIm hDim c p
  have hHerm :
      (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSymm
  have hIrred := shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_lambda_one_D_pos
    A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN p
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ :=
    LatticeSystem.Math.PerronFrobenius.exists_pos_eigenvec_max hHerm hIrred
  have heq := @shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
    Λ _ _ N A J 1 D c p
  rw [heq] at hAv
  refine ⟨c - μ, v, hv_pos, ?_⟩
  set M : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hAv
  have heq2 : Matrix.mulVec M v = c • v - μ • v := by linear_combination -hAv
  rw [heq2, sub_smul]

set_option linter.style.longLine false in
/-- General spin-`S` dressed submatrix Hermitian minimum identification at
`lambda = 1`, `D.re > 0`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_lambda_one_D_pos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ, ∃ v : parityConfigS Λ N p → ℝ,
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v ∧
      ν = hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim (show ((1 : ℂ).im = 0) from by norm_num) hDim p) := by
  have hOneIm : ((1 : ℂ).im = 0) := by norm_num
  have hOneReNeg : -1 ≤ (1 : ℂ).re := by norm_num
  have hOneReLe : (1 : ℂ).re ≤ 1 := by norm_num
  obtain ⟨ν, v, hv_pos, hAv⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_lambda_one_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  set M_real : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  have hM_symm : M_real.IsSymm :=
    Matrix.IsSymm.submatrix
      (dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real
        (N := N) A hJim hOneIm hDim) _
  have hShift_eq : shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p =
      c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
      (N := N) A J 1 D c p
  have h_eig_shifted :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).mulVec v =
        (c - ν) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_smul]
  have hB_symm :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).IsSymm := by
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
      (N := N) A hJim hOneIm hDim c p
  have hB_nn :
      ∀ i j, 0 ≤ (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real) i j := by
    intro i j
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg
      A hJim hJnn hJself hJbip hOneIm hOneReNeg hOneReLe hDim
      (le_of_lt hDpos) (fun σ => le_of_lt (hc_strict σ)) p i j
  have h_min_lift :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
        c - (c - ν) :=
    LatticeSystem.Math.CollatzWielandt.hermitianMinEigenvalue_lift_eq_sub_pf
      hM_symm c hB_nn hB_symm h_eig_shifted hv_pos
  have h_mat_eq :
      M_real.map ((↑) : ℝ → ℂ) =
        (dressedAxisSwappedAnisotropicHeisenbergS A J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1) :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
      A hJim hJself hOneIm hDim p
  have h_spec_eq :
      spectrum ℝ (M_real.map ((↑) : ℝ → ℂ)) =
        spectrum ℝ ((dressedAxisSwappedAnisotropicHeisenbergS A J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) := by
    rw [h_mat_eq]
  have h_min_bridge :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
      hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hOneIm hDim p) :=
    hermitianMinEigenvalue_eq_of_spectrum_eq _ _ h_spec_eq
  linarith [h_min_lift, h_min_bridge]

set_option linter.style.longLine false in
/-- General spin-`S` bare submatrix Hermitian minimum identification at
`lambda = 1`, `D.re > 0`. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_lambda_one_D_pos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ, ∃ v : parityConfigS Λ N p → ℝ,
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v ∧
      ν = hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim (show ((1 : ℂ).im = 0) from by norm_num) hDim p) := by
  have hOneIm : ((1 : ℂ).im = 0) := by norm_num
  obtain ⟨ν, v, hv_pos, hAv, hν_eq⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_lambda_one_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hOneIm hDim p]
  exact hν_eq

set_option linter.style.longLine false in
/-- General spin-`S` bare parity-block submatrix `finrank <= 1` at its
Hermitian minimum at `lambda = 1`, `D.re > 0`. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue_lambda_one_D_pos
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J 1 D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim (show ((1 : ℂ).im = 0) from by norm_num) hDim p) : ℂ))) ≤ 1 := by
  have hOneIm : ((1 : ℂ).im = 0) := by norm_num
  obtain ⟨ν, v, hv_pos, hAv, hν_eq⟩ :=
    axisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_lambda_one_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN p
  have h_eig_shifted :
      Matrix.mulVec (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p) v =
        (c - ν) • v := by
    rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
          (N := N) A J 1 D c p]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_smul]
  have hIrred :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_lambda_one_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN p
  have h_finrank_shifted_R :
      finrank ℝ ↥(End.eigenspace (Matrix.toLin'
        (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p)) (c - ν)) ≤ 1 :=
    LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
      hIrred h_eig_shifted hv_pos
  set M_real : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  have hShift_eq :
      shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p =
        c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
      (N := N) A J 1 D c p
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
        (dressedAxisSwappedAnisotropicHeisenbergS A J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1) :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
      A hJim hJself hOneIm hDim p
  rw [hMap] at h_finrank_M_C
  have h_finrank_bare :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J 1 D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 := by
    have h_similarity_finrank :=
      matrix_similar_eigenspace_finrank_eq
        (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := N) A p)
        (marshallDiagonalOnParity_mul_self (Λ := Λ) (N := N) A p)
        (dressedAxisSwapped_submatrix_eq_marshall_conj_bare A J 1 D p) (ν : ℂ)
    rw [h_similarity_finrank] at h_finrank_M_C
    exact h_finrank_M_C
  exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_min_conditional
    hJim hOneIm hDim p ν h_finrank_bare hν_eq

set_option linter.style.longLine false in
/-- General spin-`S` anisotropic `H` eigenspace `finrank <= 2` at
`min(per-block mins)` at `lambda = 1`, `D.re > 0`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_unconditional_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)] :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 D N))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJim (show ((1 : ℂ).im = 0) from by norm_num) hDim 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJim (show ((1 : ℂ).im = 0) from by norm_num) hDim 1)) : ℝ) : ℂ)) ≤ 2 := by
  have hOneIm : ((1 : ℂ).im = 0) := by norm_num
  have h0 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue_lambda_one_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN 0
  have h1 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue_lambda_one_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN 1
  exact anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins_general
    hJim hOneIm hDim hJself h0 h1

set_option linter.style.longLine false in
/-- General spin-`S` anisotropic `H` eigenspace `finrank <= 2` at its global
Hermitian minimum at `lambda = 1`, `D.re > 0`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hD_star : star D = D) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 D N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star (show star (1 : ℂ) = (1 : ℂ) from by norm_num) hD_star) : ℝ) : ℂ)) ≤ 2 := by
  classical
  have hOneIm : ((1 : ℂ).im = 0) := by norm_num
  have hOneStar : star (1 : ℂ) = (1 : ℂ) := by norm_num
  have hbound := anisotropicHeisenbergS_eigenspace_finrank_le_two_unconditional_lambda_one_D_pos_general
    A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN
  have hblock_eq := hermitianMinEigenvalue_axisSwapped_eq_min_block_mins
    (Λ := Λ) (N := N) hJim hOneIm hDim hJself
  have hswap_eq := axisSwapUnitarySSpinS_hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    (Λ := Λ) (N := N) hJ_star hOneStar hD_star
  have henergy_eq : (min (hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hOneIm hDim 0))
        (hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) hJim hOneIm hDim 1)) : ℝ) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star hOneStar hD_star) := by
    rw [← hblock_eq, ← hswap_eq]
  rw [henergy_eq] at hbound
  exact hbound

/-! ## Deformation-path and target wrappers at `lambda = 1`, `D > 0` -/

/-- Along the Theorem 2.4 deformation path with target `lambda' = 1`, the
first coordinate stays equal to `1`. -/
theorem anisotropicHeisenbergParametricPath_fst_eq_one_lambda_one
    {D' t : ℝ} :
    (anisotropicHeisenbergParametricPath 1 D' t).1 = 1 := by
  unfold anisotropicHeisenbergParametricPath
  ring

/-- Along the Theorem 2.4 deformation path with target `lambda' = 1`, positive
target `D'` is positive for every `0 < t`. -/
theorem anisotropicHeisenbergParametricPath_snd_pos_lambda_one
    {D' t : ℝ} (hD' : 0 < D') (ht_pos : 0 < t) :
    0 < (anisotropicHeisenbergParametricPath 1 D' t).2 := by
  unfold anisotropicHeisenbergParametricPath
  change 0 < t * D'
  exact mul_pos ht_pos hD'

set_option linter.style.longLine false in
/-- General spin-`S` `finrank <= 2` at the global minimum along the
`lambda = 1`, `D > 0` boundary path. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    {D' : ℝ} (hD' : 0 < D')
    {t : ℝ} (ht_pos : 0 < t) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J
        ((anisotropicHeisenbergParametricPath 1 D' t).1 : ℂ)
        ((anisotropicHeisenbergParametricPath 1 D' t).2 : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star
          (show star ((anisotropicHeisenbergParametricPath 1 D' t).1 : ℂ) =
              ((anisotropicHeisenbergParametricPath 1 D' t).1 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])
          (show star ((anisotropicHeisenbergParametricPath 1 D' t).2 : ℂ) =
              ((anisotropicHeisenbergParametricPath 1 D' t).2 : ℂ) from by
            rw [Complex.star_def, Complex.conj_ofReal])) : ℝ) : ℂ)) ≤ 2 := by
  have hfst := anisotropicHeisenbergParametricPath_fst_eq_one_lambda_one (D' := D') (t := t)
  have hDpos := anisotropicHeisenbergParametricPath_snd_pos_lambda_one hD' ht_pos
  set D_t : ℂ := ((anisotropicHeisenbergParametricPath 1 D' t).2 : ℂ)
  have hD_t_im : D_t.im = 0 := by simp [D_t]
  have hD_t_re : D_t.re = (anisotropicHeisenbergParametricPath 1 D' t).2 := by
    simp [D_t]
  have hD_t_star : star D_t = D_t := by
    rw [Complex.star_def]; simp [D_t]
  have hDpos_t : 0 < D_t.re := by rw [hD_t_re]; exact hDpos
  have hraw :=
    anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_lambda_one_D_pos_general
      A hJim hJnn hJpos hJself hJbip hD_t_im hDpos_t
      (hc_strict 1 D_t) hA_ne hB_ne hN hJ_star hD_t_star
  rw [hfst]
  change finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 D_t N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := N)
          hJ_star (show star (1 : ℂ) = (1 : ℂ) from by norm_num) hD_t_star) : ℝ) : ℂ)) ≤ 2
  exact hraw

set_option linter.style.longLine false in
/-- General spin-`S` deformation contradiction capstone on the `lambda = 1`,
`D' > 0` boundary path. -/
theorem anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_ne_balanced : (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D')
    (hne :
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M 1 D' ∩ Icc (0 : ℝ) 1).Nonempty)
    (h_strict_gap_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced 1 D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M 1 D' 0)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced 1 D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath 1 D' 0).1
          (anisotropicHeisenbergParametricPath 1 D' 0).2))
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M 1 D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ_star N M_balanced 1 D') :
    False := by
  classical
  set t := sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M 1 D' ∩ Icc (0 : ℝ) 1)
    with ht_def
  have hmem : t ∈ perMCrossingSet (Λ := Λ) hJ_star N M_balanced M 1 D' ∩ Icc (0 : ℝ) 1 :=
    sInf_perMCrossingSet_inter_Icc_mem hJ_star N M_balanced M 1 D' hne
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
    hJ_star N M_balanced M 1 D' hne h_strict_gap_SU2
  have h_bal_eq_full_def := balanced_min_eq_full_at_sInf
    hJ_star N M_balanced M 1 D' hne h_GS_at_SU2 h_balanced_GS_below
  have h_bal_eq_full : hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star
          (anisotropicHeisenbergParametricPath 1 D' t).1
          (anisotropicHeisenbergParametricPath 1 D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath 1 D' t).1
          (anisotropicHeisenbergParametricPath 1 D' t).2) := h_bal_eq_full_def
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath 1 D' t).1
      (anisotropicHeisenbergParametricPath 1 D' t).2 N M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, _⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath 1 D' t).1
      (anisotropicHeisenbergParametricPath 1 D' t).2 N M
  have h_eq_at_t' : hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ_star
        (anisotropicHeisenbergParametricPath 1 D' t).1
        (anisotropicHeisenbergParametricPath 1 D' t).2) =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ_star
        (anisotropicHeisenbergParametricPath 1 D' t).1
        (anisotropicHeisenbergParametricPath 1 D' t).2) := h_eq_at_t
  rw [h_eq_at_t'] at hΦ_M_eig
  rw [h_bal_eq_full] at hΦ_bal_eig
  have h_finrank :=
    anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path_lambda_one_D_pos_general
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
      hD' ht_pos
  rw [h_bal_eq_full] at hΦ_M_eig
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath 1 D' t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath 1 D' t).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig
    hΦ_M_ne hM_ne_balanced hΦ_M_eig

set_option linter.style.longLine false in
/-- General spin-`S` obligation (2) under a single SU(2)-point strict-gap
axiom on the `lambda = 1`, `D' > 0` boundary path. -/
theorem anisotropicHeisenbergS_obligation_2_single_axiom_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_orig 1 D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced 1 D' 1)
    (axiom_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ N M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced 1 D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M' 1 D' 0) :
    False := by
  classical
  have axiom_GS_at_SU2 :=
    strict_GS_at_path_zero_from_strict_gap_at_SU2 (Λ := Λ) hJ_star N M_balanced
      1 D' (fun M' _ hne => by
        haveI := ‹Nonempty (magConfigS Λ N M')›
        have := axiom_strict_gap_at_SU2 M' hne
        unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at this
        have hpath := anisotropicHeisenbergParametricPath_zero 1 D'
        simp only [hpath] at this
        exact this)
  have hne_orig : (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_orig 1 D' ∩
      Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, h_violation_orig, ⟨by norm_num, le_refl _⟩⟩
  obtain ⟨M_chosen, hM_chosen_range, hM_chosen_ne_bal, hM_chosen_NE,
          hM_chosen_cross_total, h_argmin_total⟩ :=
    exists_M_chosen_argmin_per_M_first_crossing
      hJ_star N M_balanced M_orig hM_orig_ne 1 D' hne_orig
  haveI := hM_chosen_NE
  have hM_chosen_cross :
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen 1 D' ∩
        Icc (0 : ℝ) 1).Nonempty := by
    rw [← perMCrossingSet_total_eq_perMCrossingSet]
    exact hM_chosen_cross_total
  have hM_chosen_centered_ne : (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      (M_chosen : ℂ)) ≠ 0 :=
    h_centered_nonzero M_chosen hM_chosen_range hM_chosen_ne_bal
  have h_strict_chosen :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced 1 D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_chosen 1 D' 0 :=
    axiom_strict_gap_at_SU2 M_chosen hM_chosen_ne_bal
  have h_argmin : ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ N M'), M' ≠ M_balanced →
      (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' 1 D' ∩ Icc (0 : ℝ) 1).Nonempty →
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M_chosen 1 D' ∩
        Icc (0 : ℝ) 1) ≤
      sInf (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M' 1 D' ∩
        Icc (0 : ℝ) 1) := by
    intro M' hNE_M' h_ne_bal_M' h_cross_M'
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * N + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    have h_cross_M'_total :
        (perMCrossingSet_total (Λ := Λ) hJ_star N M_balanced M' 1 D' ∩
          Icc (0 : ℝ) 1).Nonempty := by
      rw [perMCrossingSet_total_eq_perMCrossingSet]
      exact h_cross_M'
    have h_le_total := h_argmin_total M' hM'_range h_ne_bal_M' hNE_M' h_cross_M'_total
    rw [perMCrossingSet_total_eq_perMCrossingSet,
        perMCrossingSet_total_eq_perMCrossingSet] at h_le_total
    exact h_le_total
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star N M_balanced M_chosen 1 D' hM_chosen_cross h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star N M_balanced M_chosen 1 D'
      hM_chosen_cross h_argmin)
  exact anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_lambda_one_D_pos_general
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
    M_balanced M_chosen h_balanced hM_chosen_centered_ne hD'
    hM_chosen_cross h_strict_chosen axiom_GS_at_SU2 h_below

set_option linter.style.longLine false in
/-- General spin-`S` obligation (2) from only SU(2) global uniqueness on the
`lambda = 1`, `D' > 0` boundary path. -/
theorem anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_orig 1 D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced 1 D' 1)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1) :
    False := by
  classical
  have h_GS_at_SU2 :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star N M_balanced h_balanced h_SU2_global_unique
  have h_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ N M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced 1 D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M' 1 D' 0 := by
    intro M' hNE_M' hM'_ne_bal
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * N + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    exact strict_gap_at_path_zero_of_global_unique
      (Λ := Λ) hJ_star N M_balanced M' 1 D'
      h_balanced (h_centered_nonzero M' hM'_range hM'_ne_bal)
      h_SU2_global_unique h_GS_at_SU2
  exact anisotropicHeisenbergS_obligation_2_single_axiom_lambda_one_D_pos_general
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hD' h_violation_orig h_strict_gap_at_SU2

set_option linter.style.longLine false in
/-- General spin-`S` target strict gap from SU(2) global uniqueness on the
`lambda = 1`, `D' > 0` boundary. -/
theorem anisotropicHeisenbergS_strict_gap_all_M_of_SU2_global_unique_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1)
    {D' : ℝ} (hD' : 0 < D')
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced) :
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ_star 1 D') <
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ_star 1 D') := by
  classical
  have hpath : anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star N M_balanced 1 D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star N M 1 D' 1 := by
    exact lt_of_not_ge (by
      intro h_violation
      exact anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_lambda_one_D_pos_general
        A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
        M_balanced M h_balanced hM_ne h_centered_nonzero
        hD' h_violation h_SU2_global_unique)
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at hpath
  simp only [anisotropicHeisenbergParametricPath_one] at hpath
  exact hpath

set_option linter.style.longLine false in
/-- General spin-`S` target uniqueness from SU(2) global uniqueness on the
`lambda = 1`, `D' > 0` boundary. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1)
    {D' : ℝ} (hD' : 0 < D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hN1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) hN
  have h_global_two :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 (D' : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
            ℝ) : ℂ)) ≤ 2 := by
    have hD_im : ((D' : ℂ)).im = 0 := by simp
    have hD_re : ((D' : ℂ)).re = D' := by simp
    have hD_star : star (D' : ℂ) = (D' : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hraw :=
      anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_lambda_one_D_pos_general
        A hJim hJnn hJpos hJself hJbip hD_im
        (by simpa [hD_re] using hD') (hc_strict 1 (D' : ℂ))
        hA_ne hB_ne hN hJ_star hD_star
    simpa [anisotropicHeisenbergS_full_isHermitian_real] using hraw
  have h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star 1 D') <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star 1 D') := by
    intro M hM hM_ne
    haveI := hM
    exact anisotropicHeisenbergS_strict_gap_all_M_of_SU2_global_unique_lambda_one_D_pos_general
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
      M_balanced h_balanced h_centered_nonzero h_SU2_global_unique hD' M hM_ne
  exact anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap
    A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN1
    M_balanced h_balanced h_strict_gap h_global_two

set_option linter.style.longLine false in
/-- General spin-`S` target ground states have zero magnetization from SU(2)
global uniqueness on the `lambda = 1`, `D' > 0` boundary. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_SU2_global_unique_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1)
    {D' : ℝ} (hD' : 0 < D')
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J 1 (D' : ℂ) N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_lambda_one_D_pos_general
      A hJim hJnn hJpos hJself hJbip hJ_sym hc_strict hA_ne hB_ne hN hJ_star
      M_balanced h_balanced h_centered_nonzero h_SU2_global_unique hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J 1 (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

set_option linter.style.longLine false in
/-- General spin-`S` target uniqueness from the MLM/Casimir SU(2) endpoint on
the `lambda = 1`, `D' > 0` boundary. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hN1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) hN
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
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder_t23_pf
      (V := Λ) A N c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq hN1 hcardA hcardB
  have h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1 :=
    anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
      (Λ := Λ) (N := N) hJ_star hμ_min huniq_heis
  exact anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_lambda_one_D_pos_general
    A hJim hJnn hJpos hJself hJbip hJ_sym hc_axis_strict hA_ne hB_ne hN hJ_star
    M_balanced h_balanced h_centered_nonzero h_SU2_global_unique hD'

set_option linter.style.longLine false in
/-- General spin-`S` target zero-magnetization from the MLM/Casimir SU(2)
endpoint on the `lambda = 1`, `D' > 0` boundary. -/
theorem anisotropicHeisenbergS_target_zero_magnetization_of_MLM_casimir_ladder_t23_pf_lambda_one_D_pos_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D')
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J 1 (D' : ℂ) N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_lambda_one_D_pos_general
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J 1 (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

end LatticeSystem.Quantum
