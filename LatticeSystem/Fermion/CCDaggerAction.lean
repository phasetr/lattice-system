import LatticeSystem.Fermion.AnnihilationCreationIdentity

/-!
# Action of `c · c†` on the basis states

For the single-mode fermion:

- `(c · c†).mulVec |0⟩ = |0⟩` (vacuum is the unoccupied eigenstate
  with eigenvalue 1).
- `(c · c†).mulVec |1⟩ = 0` (occupied state is annihilated since
  there is no hole).

Direct from `c · c† = 1 − n` (PR #963) plus
`fermionNumber_mulVec_{vacuum, occupied}` (Mode.lean).

Tracked as part of Tasaki §2.4 / §2.5 / Phase 2 fermion infrastructure
(Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `(c · c†) · |0⟩ = |0⟩` (vacuum is the unoccupied eigenstate). -/
theorem fermionAnnihilation_mul_fermionCreation_mulVec_vacuum :
    (fermionAnnihilation * fermionCreation).mulVec fermionVacuum =
      fermionVacuum := by
  rw [fermionAnnihilation_mul_fermionCreation_eq_one_sub_number]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, fermionNumber_mulVec_vacuum]
  simp

/-- `(c · c†) · |1⟩ = 0` (occupied state has no hole). -/
theorem fermionAnnihilation_mul_fermionCreation_mulVec_occupied :
    (fermionAnnihilation * fermionCreation).mulVec fermionOccupied = 0 := by
  rw [fermionAnnihilation_mul_fermionCreation_eq_one_sub_number]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, fermionNumber_mulVec_occupied]
  simp

end LatticeSystem.Fermion
