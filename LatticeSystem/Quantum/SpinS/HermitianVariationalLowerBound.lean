import LatticeSystem.Quantum.SpinS.RayleighOnDiagonal
import LatticeSystem.Quantum.SpinS.RayleighUnitarySimilarity
import LatticeSystem.Quantum.SpinS.RayleighOnVecHermitianLowerBound
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Hermitian variational lower bound: `min eigenvalue ≤ rayleighOnVec` on unit vectors

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

The **variational lower bound**: for Hermitian `M` and any vector `v : n → ℂ`,
`hermitianMinEigenvalue hM · (dotProduct (star v) v).re ≤ rayleighOnVec M v`.

Proof via spectral_theorem + unitary similarity + diagonal lower bound + unit-norm preservation.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Sum of squared component norms of `Uᴴ v` equals `(dotProduct (star v) v).re`
when `U` is the Hermitian eigenvectorUnitary. -/
theorem sum_normSq_conjTranspose_eigenvectorUnitary_mulVec_eq
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (v : n → ℂ) :
    let U : Matrix n n ℂ := Matrix.IsHermitian.eigenvectorUnitary hM
    (∑ i, ‖U.conjTranspose.mulVec v i‖ ^ 2 : ℝ) = (dotProduct (star v) v).re := by
  intro U
  have hU : U * U.conjTranspose = 1 := eigenvectorUnitary_mul_conjTranspose_eq_one hM
  have hpres : dotProduct (star (U.conjTranspose.mulVec v)) (U.conjTranspose.mulVec v) =
      dotProduct (star v) v :=
    dotProduct_star_conjTranspose_mulVec_self hU v
  -- Σ ‖(U† v)_i‖² = (dotProduct (star (U† v)) (U† v)).re = (dotProduct (star v) v).re
  have hsq : (∑ i, ‖U.conjTranspose.mulVec v i‖ ^ 2 : ℝ) =
      (dotProduct (star (U.conjTranspose.mulVec v)) (U.conjTranspose.mulVec v)).re := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hsq, hpres]

/-- **Hermitian variational lower bound**: for Hermitian `M` and any `v`,
`hermitianMinEigenvalue hM · (dotProduct (star v) v).re ≤ rayleighOnVec M v`. -/
theorem hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (v : n → ℂ) :
    hermitianMinEigenvalue hM * (dotProduct (star v) v).re ≤ rayleighOnVec M v := by
  set U : Matrix n n ℂ := (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) with hU_def
  -- spectral: M = U * D * Uᴴ
  have hspec : M = U * Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) *
      U.conjTranspose := by
    have := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  conv_rhs => rw [hspec, rayleighOnVec_unitary_conj, rayleighOnVec_diagonal_real]
  -- Goal: hermitianMinEigenvalue hM * (dotProduct (star v) v).re ≤
  --       ∑ i, ‖(U† v)_i‖² · eigenvalues i
  -- min eigenvalues = hermitianMinEigenvalue hM by def
  have hmin_eq : (Finset.univ.image hM.eigenvalues).min'
      (Finset.image_nonempty.mpr Finset.univ_nonempty) = hermitianMinEigenvalue hM := rfl
  -- Σ ‖(U† v)_i‖² = (dotProduct (star v) v).re (from bridge)
  have hbridge : (∑ i, ‖U.conjTranspose.mulVec v i‖ ^ 2 : ℝ) = (dotProduct (star v) v).re :=
    sum_normSq_conjTranspose_eigenvectorUnitary_mulVec_eq hM v
  -- Diagonal lower bound: Σ ‖(U†v)_i‖² · λ_i ≥ (min λ) · Σ ‖(U†v)_i‖²
  have hbound := sum_normSq_mul_real_ge_min_mul_sum hM.eigenvalues (U.conjTranspose.mulVec v)
  rw [hmin_eq, hbridge] at hbound
  exact hbound

end LatticeSystem.Quantum
