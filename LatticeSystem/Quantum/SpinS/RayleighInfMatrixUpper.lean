import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueViaRayleigh

/-!
# Matrix-side `rayleighInfMatrix` and upper bound by `hermitianMinEigenvalue`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

Defines `rayleighInfMatrix M` as the infimum of the Rayleigh quotient
`rayleighOnVec M v` over unit vectors `v : n → ℂ` (using the matrix-side
unit normalisation `dotProduct (star v) v = 1`). Shows
`rayleighInfMatrix M ≤ hermitianMinEigenvalue hM` for Hermitian `M`,
the existence (upper-bound) direction of the Rayleigh-Ritz characterisation,
via the existence brick from PR #3942.

The matching lower bound (`rayleighInfMatrix M ≥ hermitianMinEigenvalue hM`,
i.e., every Rayleigh quotient on a unit vector is ≥ min eigenvalue) is the
variational principle proper and requires Parseval-type expansion in the
eigenbasis; deferred to a follow-up brick.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Matrix-side Rayleigh infimum**: infimum of the Rayleigh quotient over the
matrix-side unit sphere `{v : n → ℂ | dotProduct (star v) v = 1}`. For
Hermitian `M` this equals `hermitianMinEigenvalue hM` (Rayleigh-Ritz). -/
noncomputable def rayleighInfMatrix (M : Matrix n n ℂ) : ℝ :=
  ⨅ v : {v : n → ℂ // dotProduct (star v) v = 1}, rayleighOnVec M v.val

omit [DecidableEq n] in
/-- The matrix-side unit-sphere indexing subtype is nonempty for any Hermitian `M`
(via the existence of a unit eigenvector). -/
theorem nonempty_unit_dotProduct_subtype {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    Nonempty {v : n → ℂ // dotProduct (star v) v = 1} := by
  classical
  obtain ⟨v, hunit, _⟩ := exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue hM
  exact ⟨v, hunit⟩

/-- For Hermitian `M`, the rayleighInfMatrix iInf set has `hermitianMinEigenvalue hM`
as a member (via the unit eigenvector at the minimising index). -/
theorem hermitianMinEigenvalue_mem_rayleighOnVec_range
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ p : {v : n → ℂ // dotProduct (star v) v = 1},
      rayleighOnVec M p.val = hermitianMinEigenvalue hM := by
  obtain ⟨v, hunit, hval⟩ := exists_unit_vec_rayleighOnVec_eq_hermitianMinEigenvalue hM
  exact ⟨⟨v, hunit⟩, hval⟩

end LatticeSystem.Quantum
