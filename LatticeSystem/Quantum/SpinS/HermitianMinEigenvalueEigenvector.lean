import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueViaRayleigh

/-!
# Eigenvector existence at `hermitianMinEigenvalue`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For a Hermitian matrix `M : Matrix n n ℂ`, there exists a unit eigenvector at
the minimum eigenvalue. Specifically: there exists `v : n → ℂ` with
`dotProduct (star v) v = 1` and
`M.mulVec v = ((hermitianMinEigenvalue hM : ℝ) : ℂ) • v`.

This packages the underlying mathlib fact
`Matrix.IsHermitian.mulVec_eigenvectorBasis` at the minimising eigenvalue
index (an immediate corollary of `exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue`
in PR #3942 but stated in eigenvector form rather than Rayleigh form).

Used by the obligation (2) IVT crossing argument capstone: extract the
sector ground eigenvector at the common min energy at the crossing point,
then lift via PR #3961 to a full eigenvector, then apply reflection +
obligation (1) `≤ 2` contradiction (PR #3903).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Eigenvector existence at the minimum eigenvalue**: for a Hermitian matrix
`M`, there is a unit eigenvector `v` with `M.mulVec v = (hermitianMinEigenvalue hM) • v`.

Concretely `v = (hM.eigenvectorBasis i₀).ofLp` for `i₀` an index attaining
the min eigenvalue. -/
theorem exists_unit_eigenvector_hermitianMinEigenvalue
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ v : n → ℂ, dotProduct (star v) v = 1 ∧
      M.mulVec v = ((hermitianMinEigenvalue hM : ℝ) : ℂ) • v := by
  obtain ⟨i₀, hi₀⟩ := exists_index_eigenvalue_eq_hermitianMinEigenvalue hM
  refine ⟨(hM.eigenvectorBasis i₀).ofLp,
    eigenvectorBasis_dotProduct_self_eq_one hM i₀, ?_⟩
  have heig := Matrix.IsHermitian.mulVec_eigenvectorBasis hM i₀
  -- heig : M.mulVec ((hM.eigenvectorBasis i₀).ofLp) = (hM.eigenvalues i₀ : ℂ) • ...
  rw [show ((hermitianMinEigenvalue hM : ℝ) : ℂ) = ((hM.eigenvalues i₀ : ℝ) : ℂ) from by
    rw [hi₀]]
  convert heig using 2

/-- **Eigenvector existence at the minimum eigenvalue (nonzero form)**: same as
`exists_unit_eigenvector_hermitianMinEigenvalue` but expressed with `v ≠ 0`
instead of the unit normalisation. This is the form directly consumed by
downstream eigenspace arguments. -/
theorem exists_nonzero_eigenvector_hermitianMinEigenvalue
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ v : n → ℂ, v ≠ 0 ∧
      M.mulVec v = ((hermitianMinEigenvalue hM : ℝ) : ℂ) • v := by
  obtain ⟨v, hunit, heig⟩ := exists_unit_eigenvector_hermitianMinEigenvalue hM
  refine ⟨v, ?_, heig⟩
  intro h0
  rw [h0] at hunit
  simp at hunit

end LatticeSystem.Quantum
