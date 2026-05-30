import LatticeSystem.Quantum.SpinS.RayleighInfMatrixLe
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound

/-!
# Rayleigh-Ritz equality `rayleighInfMatrix M = hermitianMinEigenvalue hM`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Combines the unconditional upper bound `rayleighInfMatrix M ≤ hermitianMinEigenvalue hM`
(PR #3948) with the variational lower bound
`hermitianMinEigenvalue hM ≤ rayleighOnVec M v` for unit `v` (PR #3950) to give the
**Rayleigh-Ritz equality**:
`rayleighInfMatrix M = hermitianMinEigenvalue hM`
for any Hermitian `M`.

This identifies the minimum eigenvalue with the infimum of the Rayleigh quotient over
the matrix-side unit sphere — the central characterisation used by the obligation (2)
deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Variational lower bound at unit vectors: for Hermitian `M` and unit `v`,
`hermitianMinEigenvalue hM ≤ rayleighOnVec M v`. -/
theorem hermitianMinEigenvalue_le_rayleighOnVec_of_unit
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {v : n → ℂ} (hunit : dotProduct (star v) v = 1) :
    hermitianMinEigenvalue hM ≤ rayleighOnVec M v := by
  have h := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hM v
  rw [hunit] at h
  simpa using h

/-- `hermitianMinEigenvalue hM ≤ rayleighInfMatrix M` for Hermitian `M`. -/
theorem hermitianMinEigenvalue_le_rayleighInfMatrix
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    hermitianMinEigenvalue hM ≤ rayleighInfMatrix M := by
  unfold rayleighInfMatrix
  haveI : Nonempty {v : n → ℂ // dotProduct (star v) v = 1} :=
    nonempty_unit_dotProduct_subtype hM
  refine le_ciInf (fun p => ?_)
  exact hermitianMinEigenvalue_le_rayleighOnVec_of_unit hM p.property

/-- **Rayleigh-Ritz equality**: for Hermitian `M`,
`rayleighInfMatrix M = hermitianMinEigenvalue hM`. -/
theorem rayleighInfMatrix_eq_hermitianMinEigenvalue
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    rayleighInfMatrix M = hermitianMinEigenvalue hM :=
  le_antisymm (rayleighInfMatrix_le_hermitianMinEigenvalue hM)
    (hermitianMinEigenvalue_le_rayleighInfMatrix hM)

end LatticeSystem.Quantum
