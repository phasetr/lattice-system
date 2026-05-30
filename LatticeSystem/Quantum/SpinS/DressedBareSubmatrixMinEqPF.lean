import LatticeSystem.Math.HermitianMinEqOfShiftPF
import LatticeSystem.Quantum.SpinS.DressedSubmatrixPFEigenvector
import LatticeSystem.Quantum.SpinS.MarshallSubmatrixMinEq
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.ParityBlockDressedFinrank
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance

/-!
# Dressed/bare submatrix `hermitianMinEigenvalue = ν_PF` identification

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.h.2): Specialise (j.13.h.1) to the dressed parity-block submatrix using
(j.1) PF positive eigenvector, then transfer to the bare submatrix via Marshall
similarity (j.8) #3865.

This produces the identification `ν_PF = hermitianMinEigenvalue` unconditionally
for both the dressed and bare submatrices, discharging the deferred hypothesis
in (j.5) #3861 / (j.11) #3869 conditional bounds.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **(j.13.h.2-dressed) Dressed submatrix hermitianMinEigenvalue identification**.

Combining (j.1) positive PF eigenvector existence + (j.13.h.1) generic shift
identification + matrix-identity bridge between real-lifted and complex submatrix,
the dressed submatrix's `hermitianMinEigenvalue` equals the un-shifted PF value
`ν = c - μ_PF`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf
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
    (h_intermediate : ∀ τ : Λ → Fin (N + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
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
  -- (j.1): extract positive PF eigenvector v at ν of dressed.submatrix.
  obtain ⟨ν, v, hv_pos, hAv⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_legacy
      (N := N) A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos
      hc_strict hA_ne hB_ne h_intermediate p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  -- Set up M_real and B_real = c•1 - M_real (= shifted).
  set M_real : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  have hM_symm : M_real.IsSymm :=
    Matrix.IsSymm.submatrix
      (dressedAxisSwappedAnisotropicHeisenbergSReMatrix_isSymm_of_real (N := N) A hJim hlam hDim) _
  -- The shifted equals c•1 - M_real (real matrices).
  have hShift_eq : shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p =
      c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
      (N := N) A J lam D c p
  -- Shifted v = (c - ν) • v from M_real v = ν v.
  have h_eig_shifted :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).mulVec v =
        (c - ν) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_smul]
  -- B_real symmetric (via shift identity).
  have hB_symm :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).IsSymm := by
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
      (N := N) A hJim hlam hDim c p
  -- B_real nonneg (via shift identity).
  have hB_nn :
      ∀ i j, 0 ≤ (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real) i j := by
    intro i j
    rw [← hShift_eq]
    exact shiftedDressedAxisSwappedReMatrixOnParityBlock_nonneg
      A hJim hJnn hJself hJbip hlam (le_of_lt hlb) (le_of_lt hub) hDim
      (le_of_lt hDpos) (fun σ => le_of_lt (hc_strict σ)) p i j
  -- Apply (j.13.h.1).
  have h_min_lift :
      LatticeSystem.Quantum.hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
        c - (c - ν) :=
    LatticeSystem.Math.CollatzWielandt.hermitianMinEigenvalue_lift_eq_sub_pf
      hM_symm c hB_nn hB_symm h_eig_shifted hv_pos
  -- Bridge: the matrix M_real.map ofReal equals dressed_complex.submatrix.
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

/-- **(j.13.h.2-bare) Bare submatrix hermitianMinEigenvalue identification**.

Transfer (j.13.h.2-dressed) via Marshall similarity (j.8) #3865. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf_legacy
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
    (h_intermediate : ∀ τ : Λ → Fin (N + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
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
    dressedAxisSwappedAnisotropicHeisenbergS_submatrix_hermitianMinEigenvalue_eq_pf
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
      h_intermediate p
  refine ⟨ν, v, hv_pos, hAv, ?_⟩
  -- Use (j.8) Marshall similarity to transfer min eigenvalue: bare = dressed.
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hlam hDim p]
  exact hν_eq

end LatticeSystem.Quantum
