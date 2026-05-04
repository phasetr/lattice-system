import LatticeSystem.Fermion.Mode

/-!
# Single-mode fermion trace identities

For the single-mode fermion the matrix traces are

  `tr(c)        = 0`,
  `tr(c†)       = 0`,
  `tr(n)        = 1`,
  `tr(c · c†)   = 1`.

The two ladder operators are off-diagonal, so their traces vanish.
The number operator and the hole projection `c · c† = 1 − n`
each contribute one to the trace, consistent with the
projection-sum identity `n + c · c† = 1` (PR #972) and
`tr(I) = 2`.

These are the simplest building blocks for single-mode partition
functions `Z = tr(e^{−βn}) = 1 + e^{−β}` and for reduced density
matrix entries.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix

/-- `tr(c) = 0` (annihilation operator is strictly off-diagonal). -/
theorem fermionAnnihilation_trace_eq_zero :
    fermionAnnihilation.trace = 0 := by
  unfold fermionAnnihilation
  simp [Matrix.trace, Fin.sum_univ_two]

/-- `tr(c†) = 0` (creation operator is strictly off-diagonal). -/
theorem fermionCreation_trace_eq_zero :
    fermionCreation.trace = 0 := by
  unfold fermionCreation
  simp [Matrix.trace, Fin.sum_univ_two]

/-- `tr(n) = 1` (the number operator has eigenvalues `0` and `1`). -/
theorem fermionNumber_trace_eq_one :
    fermionNumber.trace = 1 := by
  unfold fermionNumber
  simp [Matrix.trace, Fin.sum_univ_two]

/-- `tr(c · c†) = 1` (the hole projection has eigenvalues `1` and
`0`). -/
theorem fermionAnnihilation_mul_fermionCreation_trace_eq_one :
    (fermionAnnihilation * fermionCreation).trace = 1 := by
  unfold fermionAnnihilation fermionCreation
  simp [Matrix.trace, Fin.sum_univ_two]

end LatticeSystem.Fermion
