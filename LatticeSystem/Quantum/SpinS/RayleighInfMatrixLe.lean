import LatticeSystem.Quantum.SpinS.RayleighInfMatrixLeConditional
import LatticeSystem.Quantum.SpinS.RayleighOnVecBddBelow

/-!
# Unconditional upper bound for `rayleighInfMatrix`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Combining the BddBelow brick (`rayleighOnVec_bddBelow_on_unit_sphere`, PR #3947)
with the conditional upper bound (`rayleighInfMatrix_le_hermitianMinEigenvalue_of_bddBelow`,
PR #3946), this file delivers the **unconditional** upper-bound direction of the
Rayleigh-Ritz characterisation:
`rayleighInfMatrix M ≤ hermitianMinEigenvalue hM` for every Hermitian `M`.

The matching `≥` direction (variational lower bound) requires `Matrix.IsHermitian.spectral_theorem`
unfolding + the diagonal lower bound (PR #3944) + unitary similarity (PR #3945); deferred to
a follow-up brick.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Unconditional upper bound of Rayleigh-Ritz**: for Hermitian `M`,
`rayleighInfMatrix M ≤ hermitianMinEigenvalue hM`. Combines `BddBelow`
(PR #3947) with the conditional upper bound (PR #3946). -/
theorem rayleighInfMatrix_le_hermitianMinEigenvalue
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    rayleighInfMatrix M ≤ hermitianMinEigenvalue hM :=
  rayleighInfMatrix_le_hermitianMinEigenvalue_of_bddBelow hM
    (rayleighOnVec_bddBelow_on_unit_sphere M)

/-- **Unconditional upper bound at a unit vector**: for Hermitian `M` and any unit `v`,
`rayleighInfMatrix M ≤ rayleighOnVec M v`. -/
theorem rayleighInfMatrix_le_rayleighOnVec
    (M : Matrix n n ℂ) {v : n → ℂ} (hunit : dotProduct (star v) v = 1) :
    rayleighInfMatrix M ≤ rayleighOnVec M v :=
  rayleighInfMatrix_le_rayleighOnVec_of_bddBelow M
    (rayleighOnVec_bddBelow_on_unit_sphere M) hunit

end LatticeSystem.Quantum
