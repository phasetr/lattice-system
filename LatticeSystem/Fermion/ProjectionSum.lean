import LatticeSystem.Fermion.AnnihilationCreationIdentity

/-!
# Projection sum: `n + c · c† = 1`

The number operator `n = c† · c` and the hole operator
`c · c† = 1 − n` (PR #963) sum to the identity:

  `n + c · c† = 1`.

This is the resolution of identity in the occupation basis: every
state is either occupied (eigenvalue 1 for `n`) or unoccupied
(eigenvalue 1 for `c · c†`), with the two projections summing to
the identity operator.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `n + c · c† = 1`. -/
theorem fermionNumber_add_fermionAnnihilation_mul_fermionCreation_eq_one :
    fermionNumber + fermionAnnihilation * fermionCreation =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [fermionAnnihilation_mul_fermionCreation_eq_one_sub_number]
  abel

end LatticeSystem.Fermion
