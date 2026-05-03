import LatticeSystem.Fermion.ProjectionsOrthogonal

/-!
# `n` and `c · c†` commute (both products are zero)

The orthogonality results of PR #976 imply that `n` and `c · c†`
commute trivially: both `n · (c · c†)` and `(c · c†) · n` equal `0`,
so they are equal.

  `Commute n (c · c†)`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `Commute n (c · c†)` (both products are zero, hence equal). -/
theorem fermionNumber_commute_fermionAnnihilation_mul_fermionCreation :
    Commute fermionNumber (fermionAnnihilation * fermionCreation) := by
  unfold Commute SemiconjBy
  rw [fermionNumber_mul_fermionAnnihilation_mul_fermionCreation_eq_zero,
    fermionAnnihilation_mul_fermionCreation_mul_fermionNumber_eq_zero]

end LatticeSystem.Fermion
