import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinS
import LatticeSystem.Quantum.SpinS.BareSubmatrixBoundAtMin
import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityBlockIrreducibleLambdaOne
import LatticeSystem.Quantum.SpinS.DressedBareSubmatrixMinEqPFStructural
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSMLMEndpoint
/-!
# General spin-S `lambda = 1`, `D > 0` boundary for the parity-block capstone — core lemmas

Core (foundational) lemmas of the general spin-`S` case-(i) boundary `lambda = 1`,
`D.re > 0`, `2 <= N` parity-block Perron--Frobenius capstone (Issue #412, Tasaki
Section 2.5 Theorem 2.4): the unshifted dressed axis-swapped parity-block PF
positive eigenvector, the Hermitian-minimum = PF eigenvalue identifications, the
parity-block `finrank <= 1` at the Hermitian minimum, and the unconditional /
global-minimum full-eigenspace `finrank <= 2` bounds.  The deformation-path and
target wrappers are assembled in `AnisotropicHeisenbergSpinSLambdaOneBoundary`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}


/-- General spin-`S` PF positive eigenvector for the unshifted dressed
axis-swapped parity-block submatrix at `lambda = 1`, `D.re > 0`. -/
theorem dressedAxisSwapReMatParity_pos_eigenvector_exists_lam1_D_pos
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

/-- General spin-`S` dressed submatrix Hermitian minimum identification at
`lambda = 1`, `D.re > 0`. -/
theorem dressedAxisSwapAHeisS_submat_hMinEig_eq_pf_lam1_D_pos
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
    dressedAxisSwapReMatParity_pos_eigenvector_exists_lam1_D_pos
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
    dressedAxisSwapAHeisS_submat_hMinEig_eq_pf_lam1_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hOneIm hDim p]
  exact hν_eq

/-- General spin-`S` bare parity-block submatrix `finrank <= 1` at its
Hermitian minimum at `lambda = 1`, `D.re > 0`. -/
theorem axisSwapAHeisS_submat_finrank_le_one_at_hMinEig_lam1_D_pos
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
    axisSwapAHeisS_submat_finrank_le_one_at_hMinEig_lam1_D_pos
      A hJim hJnn hJpos hJself hJbip hDim hDpos hc_strict hA_ne hB_ne hN 0
  have h1 :=
    axisSwapAHeisS_submat_finrank_le_one_at_hMinEig_lam1_D_pos
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


end LatticeSystem.Quantum
