/-
The ground-state double commutator is nonnegative
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

For a Hermitian observable `A` and a ground-state eigenvector `Φ` (eigenvalue the minimum),
the f-sum-rule oscillator strength `Re⟨Φ, [A, [H, A]] Φ⟩` is nonnegative: it equals twice the
variational energy of `A Φ` above the ground energy, which is `≥ 0` because the ground energy is the
minimum of the Rayleigh quotient.  This is the sign of the numerator of the ground-state Falk–Bruch
inequality, ensuring the square root in the bound is well defined.
-/
import LatticeSystem.Quantum.SpinS.DoubleCommutatorVariational
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound

namespace LatticeSystem.Quantum

open Matrix Complex

/-- **Nonnegativity of the ground-state double commutator.**  For a Hermitian `A` and a ground-state
eigenvector `Φ` of a Hermitian `H` (eigenvalue `hermitianMinEigenvalue hH`),
`0 ≤ Re⟨Φ, [A, [H, A]] Φ⟩`. -/
theorem double_commutator_ground_state_nonneg {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H A : Matrix n n ℂ}
    {Φ : n → ℂ} (hH : H.IsHermitian) (hA : A.IsHermitian)
    (hΦ : H.mulVec Φ = (hermitianMinEigenvalue hH : ℂ) • Φ) :
    0 ≤ (star Φ ⬝ᵥ (A * (H * A - A * H) - (H * A - A * H) * A).mulVec Φ).re := by
  rw [double_commutator_ground_state_eq hH hA hΦ]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hH (A.mulVec Φ)
  rw [rayleighOnVec] at hvar
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
  nlinarith [hvar]

end LatticeSystem.Quantum
