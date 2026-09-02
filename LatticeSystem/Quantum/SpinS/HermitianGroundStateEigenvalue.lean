/-
The minimum eigenvalue and the energy-minimizing eigenpairs of a Hermitian matrix
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Two directions of the same variational fact are developed here.

`hermitianMinEigenvalue_le_re_of_eigenpair` bounds `hermitianMinEigenvalue H` below every eigenvalue
of `H`, for an arbitrary nonzero eigenvector.  It is what certifies a minimizing eigenvector as a
*ground state* in the `∀ E Ψ, Ψ ≠ 0 → H Ψ = E • Ψ → E₀.re ≤ E.re` sense.

`groundState_mulVec_eq_hermitianMinEigenvalue` runs the other way: if `Φ` is a normalized
eigenvector of a Hermitian matrix `H` whose eigenvalue `E₀` has minimal real part among all
eigenpairs, then `E₀` coincides with `hermitianMinEigenvalue H`: its imaginary part vanishes
(Hermiticity) and its real part is squeezed between the variational lower bound and the minimizing
eigenvector.  This bridges the "energy-minimizing eigenpair" hypothesis used in the ground-state
axioms to the `hermitianMinEigenvalue` interface of the Falk–Bruch inequality.
-/
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.HermitianSubMinPosSemidef
import LatticeSystem.Math.ComplexVectorKernel

namespace LatticeSystem.Quantum

open Matrix

/-- **The minimum eigenvalue lies below the real part of every eigenvalue.**  For a Hermitian `H`
and any eigenpair `(E, Ψ)` with `Ψ ≠ 0` (`H Ψ = E • Ψ`), `hermitianMinEigenvalue hH ≤ E.re`.  No
normalisation of `Ψ` is assumed.

This is the direction converse to `groundState_mulVec_eq_hermitianMinEigenvalue` below, which takes
an eigenpair already known to minimise `E.re` over all eigenpairs and identifies its eigenvalue with
`hermitianMinEigenvalue`.  Here nothing is known about `(E, Ψ)`, and the conclusion is the
minimality clause itself: applied to the eigenvector supplied by
`exists_unit_eigenvector_hermitianMinEigenvalue`, it discharges the
`∀ E Ψ, Ψ ≠ 0 → H Ψ = E • Ψ → E₀.re ≤ E.re` clause of the ground-state hypothesis, i.e. it is what
*produces* ground states rather than consuming them.

Proof: the variational bound `hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec` reads
`minEig · ⟨Ψ, Ψ⟩.re ≤ ⟨Ψ, HΨ⟩.re`.  The eigenvalue equation turns the right-hand side into
`E.re · ⟨Ψ, Ψ⟩.re`, using that `⟨Ψ, Ψ⟩ = ∑ ‖Ψᵢ‖²` is real (`star_dotProduct_self_eq`), and
`⟨Ψ, Ψ⟩.re > 0` for `Ψ ≠ 0` (`dotProduct_star_self_re_pos`) cancels the common factor.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.20), p. 70 (the variational comparison
`⟨Ξ|Ĥ_h|Ξ⟩ ≥ ⟨Φ_{GS,h}|Ĥ_h|Φ_{GS,h}⟩`); §4.1, Theorem 4.2, eq. (4.1.9), p. 76. -/
theorem hermitianMinEigenvalue_le_re_of_eigenpair {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {E : ℂ} {Ψ : n → ℂ} (hΨ : Ψ ≠ 0)
    (heig : H.mulVec Ψ = E • Ψ) :
    hermitianMinEigenvalue hH ≤ E.re := by
  have hpos : 0 < (star Ψ ⬝ᵥ Ψ).re := dotProduct_star_self_re_pos hΨ
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hH Ψ
  unfold rayleighOnVec at hvar
  have hquad : (star Ψ ⬝ᵥ H.mulVec Ψ).re = E.re * (star Ψ ⬝ᵥ Ψ).re := by
    rw [heig, dotProduct_smul, smul_eq_mul, star_dotProduct_self_eq]
    simp [Complex.mul_re]
  rw [hquad] at hvar
  exact le_of_mul_le_mul_right hvar hpos

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
