import LatticeSystem.Quantum.SpinS.RayleighInfMatrixUpper

/-!
# Conditional upper bound for `rayleighInfMatrix`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

The infimum `rayleighInfMatrix M` is bounded above by `rayleighOnVec M v` at any
unit vector `v`, provided the range of the Rayleigh function on the matrix-side
unit sphere is bounded below (`BddBelow`). This is the immediate consequence of
`ciInf_le_of_le` made explicit at the matrix-Rayleigh level.

`BddBelow` itself follows from the variational principle (deferred to a
follow-up brick) or from a direct Cauchy-Schwarz bound. Once `BddBelow` is
established, combined with `hermitianMinEigenvalue_mem_rayleighOnVec_range`
(PR #3943) we obtain `rayleighInfMatrix M ≤ hermitianMinEigenvalue hM`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
/-- Conditional upper bound: `rayleighInfMatrix M ≤ rayleighOnVec M v` for any unit `v`,
provided the function is bounded below over the matrix-side unit sphere. -/
theorem rayleighInfMatrix_le_rayleighOnVec_of_bddBelow
    (M : Matrix n n ℂ)
    (hBdd : BddBelow (Set.range
      (fun p : {v : n → ℂ // dotProduct (star v) v = 1} => rayleighOnVec M p.val)))
    {v : n → ℂ} (hunit : dotProduct (star v) v = 1) :
    rayleighInfMatrix M ≤ rayleighOnVec M v := by
  unfold rayleighInfMatrix
  exact ciInf_le_of_le hBdd ⟨v, hunit⟩ le_rfl

/-- If the Rayleigh range over the matrix-side unit sphere is `BddBelow`, then for any
Hermitian `M`, `rayleighInfMatrix M ≤ hermitianMinEigenvalue hM` (the upper-bound direction
of Rayleigh-Ritz). The matching `≥` direction (variational lower bound) is deferred. -/
theorem rayleighInfMatrix_le_hermitianMinEigenvalue_of_bddBelow
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (hBdd : BddBelow (Set.range
      (fun p : {v : n → ℂ // dotProduct (star v) v = 1} => rayleighOnVec M p.val))) :
    rayleighInfMatrix M ≤ hermitianMinEigenvalue hM := by
  obtain ⟨p, hp⟩ := hermitianMinEigenvalue_mem_rayleighOnVec_range hM
  have := rayleighInfMatrix_le_rayleighOnVec_of_bddBelow M hBdd p.property
  rw [hp] at this
  exact this

end LatticeSystem.Quantum
