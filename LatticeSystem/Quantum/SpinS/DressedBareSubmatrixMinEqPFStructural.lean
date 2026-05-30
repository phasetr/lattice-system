import LatticeSystem.Quantum.SpinS.DressedBareSubmatrixMinEqPF
import LatticeSystem.Quantum.SpinS.DressedSubmatrixPFEigenvectorStructural

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Structural (j.13.h.2) dressed/bare hermitianMinEigenvalue identification (no `h_intermediate`)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

(#3887.6): Structural variants of (j.13.h.2) dressed and bare hermitianMinEigenvalue
identification theorems using (#3887.5) (j.1) structural PF eigenvector. Drops
`h_intermediate`; requires `hA_ne + hB_ne + 1 ≤ N`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **(#3887.6-dressed) Dressed submatrix hermitianMinEigenvalue identification (no `h_intermediate`)**. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_structural
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ, ∃ v : parityConfigS Λ N p → ℝ,
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v ∧
      ν = hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p) := by
  obtain ⟨ν, v, hv_pos, hAv⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists
      (N := N) A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos
      hc_strict hA_ne hB_ne hN p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  set M_real : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  have hM_symm : M_real.IsSymm :=
    Matrix.IsSymm.submatrix
      (dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real (N := N) A hJim hlam hDim) _
  have hShift_eq : shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p =
      c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
      (N := N) A J lam D c p
  have h_eig_shifted :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).mulVec v =
        (c - ν) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_smul]
  have hB_symm :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).IsSymm := by
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
      (N := N) A hJim hlam hDim c p
  have hB_nn :
      ∀ i j, 0 ≤ (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real) i j := by
    intro i j
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg
      A hJim hJnn hJself hJbip hlam (le_of_lt hlb) (le_of_lt hub) hDim
      (le_of_lt hDpos) (fun σ => le_of_lt (hc_strict σ)) p i j
  have h_min_lift :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
        c - (c - ν) :=
    LatticeSystem.Math.CollatzWielandt.hermitianMinEigenvalue_lift_eq_sub_pf
      hM_symm c hB_nn hB_symm h_eig_shifted hv_pos
  have h_mat_eq :
      M_real.map ((↑) : ℝ → ℂ) =
        (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1) :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
      A hJim hJself hlam hDim p
  have h_spec_eq :
      spectrum ℝ (M_real.map ((↑) : ℝ → ℂ)) =
        spectrum ℝ ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) := by
    rw [h_mat_eq]
  have h_min_bridge :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
      hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p) :=
    hermitianMinEigenvalue_eq_of_spectrum_eq _ _ h_spec_eq
  linarith [h_min_lift, h_min_bridge]

/-- **(#3887.6-bare) Bare submatrix hermitianMinEigenvalue identification (no `h_intermediate`)**. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ, ∃ v : parityConfigS Λ N p → ℝ,
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v ∧
      ν = hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hlam hDim p) := by
  obtain ⟨ν, v, hv_pos, hAv, hν_eq⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_structural
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
      hN p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hlam hDim p]
  exact hν_eq

end LatticeSystem.Quantum
