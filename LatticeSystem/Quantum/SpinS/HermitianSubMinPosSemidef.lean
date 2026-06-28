/-
The Hamiltonian shifted to its ground energy is positive-semidefinite
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Shifting a Hermitian `H` by its minimal eigenvalue gives a positive-semidefinite operator
`H − E₀ ≥ 0` (`E₀ = hermitianMinEigenvalue`): the quadratic form is real (Hermiticity) and its real
part is nonnegative because the ground energy is the minimum of the Rayleigh quotient.  This
`K = H − E₀` is the positive-semidefinite operator fed into the ground-state Falk–Bruch inequality.
-/
import LatticeSystem.Quantum.SpinS.FalkBruch
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- The quadratic form of a Hermitian matrix is real (zero imaginary part). -/
theorem isHermitian_dotProduct_mulVec_im_zero {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (x : n → ℂ) : (star x ⬝ᵥ M.mulVec x).im = 0 := by
  rw [← Complex.conj_eq_iff_im, starRingEnd_apply]
  have h : star (star x ⬝ᵥ M.mulVec x) = star (M.mulVec x) ⬝ᵥ x := by
    rw [Matrix.star_dotProduct, star_star]
  rw [h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM.eq]

/-- **`H − E₀` is positive-semidefinite** for `E₀ = hermitianMinEigenvalue`. -/
theorem hermitianSubMin_posSemidef {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (H - (hermitianMinEigenvalue hH : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hHerm : (H - (hermitianMinEigenvalue hH : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul (by rw [isSelfAdjoint_iff]; simp))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun x => ?_)
  rw [Complex.le_def]
  refine ⟨?_, ?_⟩
  · -- real part nonnegative (variational bound)
    have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hH x
    rw [rayleighOnVec] at hvar
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.zero_re, Complex.sub_re, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    linarith [hvar]
  · -- imaginary part zero (Hermiticity)
    rw [Complex.zero_im, eq_comm]
    exact isHermitian_dotProduct_mulVec_im_zero hHerm x

end LatticeSystem.Quantum
