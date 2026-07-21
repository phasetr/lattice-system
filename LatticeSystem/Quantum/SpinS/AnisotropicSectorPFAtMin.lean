import LatticeSystem.Quantum.SpinS.DressedAnisotropicMatrixOnMagSector
import LatticeSystem.Math.HermitianMinEqOfShiftPF
import LatticeSystem.Quantum.SpinS.MatrixSimilaritySpectrum
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance

/-!
# Anisotropic sector Perron--Frobenius bound at the Hermitian minimum

This file converts the shifted dressed anisotropic sector matrix from
`DressedAnisotropicMatrixOnMagSector` into the bare complex sector-matrix
simplicity statement at its Hermitian minimum.  The proof follows the existing
axis-swapped parity-block PF/minimum pattern: Perron--Frobenius gives a
one-dimensional real eigenspace for the shifted matrix, the shift identifies the
unshifted dressed eigenvalue as `c - r`, Collatz--Wielandt identifies that value
with the Hermitian minimum, and the Marshall diagonal similarity transfers the
result to the bare complex sector matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The bare anisotropic sector matrix has `finrank ≤ 1` at its Hermitian
minimum, provided the shifted dressed real sector matrix has a strict diagonal
shift. -/
theorem anisotropicHeisenbergS_magSector_submatrix_finrank_le_one_at_hermitianMinEigenvalue
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ} {M : ℕ}
    [Nonempty (magConfigS Λ N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos : ∀ x y : Λ, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hlam : lam.im = 0) (hD : D.im = 0)
    {c : ℝ}
    (hc_strict : ∀ σ : magConfigS Λ N M,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) (M := M)
          (fun x y => by
            rw [Complex.star_def, Complex.conj_eq_iff_im]
            exact hJ_real x y)
          (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
          (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hD)) : ℝ) : ℂ)) ≤ 1 := by
  classical
  let M_real : Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ :=
    dressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M
  let B_real : Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ :=
    shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector A J lam D N M c
  have hJ_star : ∀ x y, star (J x y) = J x y := fun x y => by
    rw [Complex.star_def, Complex.conj_eq_iff_im]
    exact hJ_real x y
  have hM_symm : M_real.IsSymm := by
    dsimp [M_real]
    exact dressedAnisotropicHeisenbergSReMatrixOnMagSector_isSymm
      A hJ_star hlam hD N M
  have hB_eq : B_real =
      c • (1 : Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ) - M_real := by
    rfl
  have hIrred : B_real.IsIrreducible := by
    dsimp [B_real]
    exact isIrreducible_shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector
      (N := N) (M := M) A lam D c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict hA_ne hB_ne hN
  obtain ⟨r, v, _hr_pos, hv_pos, hBv⟩ :=
    LatticeSystem.Math.PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible
      hIrred
  have hBv_shift :
      (c • (1 : Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ) - M_real).mulVec v =
        r • v := by
    simpa [hB_eq] using hBv
  have h_finrank_shifted_R :
      finrank ℝ ↥(End.eigenspace (Matrix.toLin' B_real) r) ≤ 1 :=
    LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
      hIrred hBv hv_pos
  have h_finrank_dressed_R :
      finrank ℝ ↥(End.eigenspace (Matrix.toLin' M_real) (c - r)) ≤ 1 := by
    rw [hB_eq] at h_finrank_shifted_R
    rw [eigenspace_smul_one_sub_finrank_eq] at h_finrank_shifted_R
    exact h_finrank_shifted_R
  have h_finrank_dressed_C :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (M_real.map ((↑) : ℝ → ℂ)))
        ((c - r : ℝ) : ℂ)) ≤ 1 :=
    matrix_complex_eigenspace_finrank_le_one_of_real M_real (c - r)
      h_finrank_dressed_R
  have h_similarity_finrank :=
    matrix_similar_eigenspace_finrank_eq
      (marshallDiagonalOnMagSector_mul_self (V := Λ) (N := N) A M)
      (marshallDiagonalOnMagSector_mul_self (V := Λ) (N := N) A M)
      (by
        simpa [M_real] using
          dressedAnisotropicHeisenbergSReMatrixOnMagSector_map_eq_marshall_conj
            (Λ := Λ) A hJ_real hlam hD N M)
      (((c - r : ℝ) : ℂ))
  rw [h_similarity_finrank] at h_finrank_dressed_C
  have hB_nn :
      ∀ i j,
        0 ≤ (c • (1 : Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ) - M_real) i j := by
    intro i j
    rw [← hB_eq]
    exact shiftedDressedAnisotropicHeisenbergSReMatrixOnMagSector_nonneg
      A lam D N M c hJ_real hJ_nn hJ_sym hJ_bipartite hc_strict i j
  have hB_symm :
      (c • (1 : Matrix (magConfigS Λ N M) (magConfigS Λ N M) ℝ) - M_real).IsSymm :=
    (Matrix.isSymm_one.smul c).sub hM_symm
  have h_min_lift :
      hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
        c - r :=
    LatticeSystem.Math.CollatzWielandt.hermitianMinEigenvalue_lift_eq_sub_pf
      hM_symm c hB_nn hB_symm hBv_shift hv_pos
  have h_spectrum :
      spectrum ℝ (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J lam D N M) =
        spectrum ℝ (M_real.map ((↑) : ℝ → ℂ)) := by
    have hsim := dressedAnisotropicHeisenbergSReMatrixOnMagSector_map_eq_marshall_conj
      (Λ := Λ) A hJ_real hlam hD N M
    have hs := matrix_similar_spectrum_real_eq
      (marshallDiagonalOnMagSector_mul_self (V := Λ) (N := N) A M)
      (marshallDiagonalOnMagSector_mul_self (V := Λ) (N := N) A M)
      hsim
    simpa [M_real] using hs
  have h_min_bare :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) (M := M) hJ_star
          (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
          (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hD)) =
        c - r := by
    have hmin_eq := hermitianMinEigenvalue_eq_of_spectrum_eq
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) (M := M) hJ_star
        (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hlam)
        (by rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hD))
      (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm)
      h_spectrum
    linarith [hmin_eq, h_min_lift]
  rw [h_min_bare]
  exact h_finrank_dressed_C

end LatticeSystem.Quantum
