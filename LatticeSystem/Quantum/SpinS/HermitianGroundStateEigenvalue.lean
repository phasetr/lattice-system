/-
A ground-state eigenvalue equals the minimum eigenvalue
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

If `Φ` is a normalized eigenvector of a Hermitian matrix `H` whose eigenvalue `E₀` has minimal real
part among all eigenpairs, then `E₀` coincides with `hermitianMinEigenvalue H`: its imaginary part
vanishes (Hermiticity) and its real part is squeezed between the variational lower bound and the
minimizing eigenvector.  This bridges the "energy-minimizing eigenpair" hypothesis used in the
ground-state axioms to the `hermitianMinEigenvalue` interface of the Falk–Bruch inequality.
-/
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.HermitianSubMinPosSemidef

namespace LatticeSystem.Quantum

open Matrix

/-- **A ground-state eigenvalue equals the minimum eigenvalue.**  For a Hermitian `H`, a normalized
eigenvector `Φ` (`star Φ ⬝ᵥ Φ = 1`, `H Φ = E₀ • Φ`) whose eigenvalue `E₀` has minimal real part over
all eigenpairs, `H Φ = (hermitianMinEigenvalue H) • Φ`. -/
theorem groundState_mulVec_eq_hermitianMinEigenvalue {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {Φ : n → ℂ} (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    {E₀ : ℂ} (heig : H.mulVec Φ = E₀ • Φ)
    (hmin : ∀ E : ℂ, ∀ Ψ : n → ℂ, Ψ ≠ 0 → H.mulVec Ψ = E • Ψ → E₀.re ≤ E.re) :
    H.mulVec Φ = (hermitianMinEigenvalue hH : ℂ) • Φ := by
  -- `E₀ = ⟨Φ, H Φ⟩`
  have hquad : star Φ ⬝ᵥ H.mulVec Φ = E₀ := by
    rw [heig, dotProduct_smul, smul_eq_mul, hΦnorm, mul_one]
  -- imaginary part vanishes by Hermiticity
  have him : E₀.im = 0 := by rw [← hquad]; exact isHermitian_dotProduct_mulVec_im_zero hH Φ
  -- `E₀.re ≤ minEig` via the minimizing eigenvector
  obtain ⟨v, hv_ne, hv_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hH
  have hle : E₀.re ≤ hermitianMinEigenvalue hH := by
    have h := hmin ((hermitianMinEigenvalue hH : ℝ) : ℂ) v hv_ne hv_eig
    simpa using h
  -- `minEig ≤ E₀.re` via the variational lower bound
  have hge : hermitianMinEigenvalue hH ≤ E₀.re := by
    have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hH Φ
    rw [hΦnorm, Complex.one_re, mul_one] at hvar
    unfold rayleighOnVec at hvar
    rw [hquad] at hvar
    exact hvar
  -- combine: `E₀ = minEig`
  have hE₀ : E₀ = (hermitianMinEigenvalue hH : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; linarith
    · rw [Complex.ofReal_im]; exact him
  rw [heig, hE₀]

end LatticeSystem.Quantum
