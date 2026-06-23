import LatticeSystem.Quantum.SpinS.RayleighOnDiagonal
import LatticeSystem.Quantum.SpinS.RayleighUnitarySimilarity
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Math.HermitianMaxEigenvalue
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Hermitian variational upper bound (max-Rayleigh)

The dual of `HermitianVariationalLowerBound`: for a Hermitian matrix `M` and any vector `v`,
the Rayleigh quotient is bounded above by the maximal eigenvalue times the squared norm,
`rayleighOnVec M v ≤ hermitianMaxEigenvalue hM · (star v ⬝ᵥ v).re`.

The proof mirrors the lower bound: diagonalise `M = U D Uᴴ` (spectral theorem), reduce the Rayleigh
quotient to a diagonal sum `∑ ‖(Uᴴ v)_i‖² λ_i`, and bound each weight by the maximal eigenvalue.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] in
/-- Finite-sum upper bound: `∑_i (‖v_i‖² · lam_i) ≤ (max_i lam_i) · ∑_i ‖v_i‖²`. -/
theorem sum_normSq_mul_real_le_max_mul_sum (lam : n → ℝ) (v : n → ℂ) :
    (∑ i, ‖v i‖ ^ 2 * lam i) ≤
      (Finset.univ.image lam).max' (Finset.image_nonempty.mpr Finset.univ_nonempty) *
        (∑ i, ‖v i‖ ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle_max : lam i ≤ (Finset.univ.image lam).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty) :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hnonneg : 0 ≤ ‖v i‖ ^ 2 := sq_nonneg _
  calc ‖v i‖ ^ 2 * lam i
      ≤ ‖v i‖ ^ 2 * (Finset.univ.image lam).max'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) :=
        mul_le_mul_of_nonneg_left hle_max hnonneg
    _ = (Finset.univ.image lam).max'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) * ‖v i‖ ^ 2 := by ring

/-- **Hermitian variational upper bound**: for Hermitian `M` and any `v`,
`rayleighOnVec M v ≤ hermitianMaxEigenvalue hM · (star v ⬝ᵥ v).re`. -/
theorem rayleighOnVec_le_hermitianMaxEigenvalue_mul_dotProduct_re
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (v : n → ℂ) :
    rayleighOnVec M v ≤
      LatticeSystem.Math.hermitianMaxEigenvalue hM * (dotProduct (star v) v).re := by
  set U : Matrix n n ℂ := (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) with hU_def
  have hspec : M = U * Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) *
      U.conjTranspose := by
    have := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  conv_lhs => rw [hspec, rayleighOnVec_unitary_conj, rayleighOnVec_diagonal_real]
  have hmax_eq : (Finset.univ.image hM.eigenvalues).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty) =
      LatticeSystem.Math.hermitianMaxEigenvalue hM := rfl
  have hbridge : (∑ i, ‖U.conjTranspose.mulVec v i‖ ^ 2 : ℝ) = (dotProduct (star v) v).re :=
    sum_normSq_conjTranspose_eigenvectorUnitary_mulVec_eq hM v
  have hbound := sum_normSq_mul_real_le_max_mul_sum hM.eigenvalues (U.conjTranspose.mulVec v)
  rw [hmax_eq, hbridge] at hbound
  exact hbound

end LatticeSystem.Quantum
