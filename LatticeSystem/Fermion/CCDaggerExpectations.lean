import LatticeSystem.Fermion.CCDaggerAction
import LatticeSystem.Fermion.StatesOrthonormal

/-!
# `c · c†` expectation values on basis states

For the single-mode fermion:

- `⟨|0⟩, c · c† |0⟩⟩ = 1` (vacuum is the unoccupied eigenstate).
- `⟨|1⟩, c · c† |1⟩⟩ = 0` (occupied state has no hole).

Direct from PR #966 + PR #968 orthonormality.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `⟨|0⟩, c · c† |0⟩⟩ = 1`. -/
theorem fermionVacuum_expectation_fermionAnnihilation_mul_fermionCreation :
    dotProduct (star fermionVacuum)
      ((fermionAnnihilation * fermionCreation).mulVec fermionVacuum) =
      (1 : ℂ) := by
  rw [fermionAnnihilation_mul_fermionCreation_mulVec_vacuum]
  exact fermionVacuum_inner_self

/-- `⟨|1⟩, c · c† |1⟩⟩ = 0`. -/
theorem fermionOccupied_expectation_fermionAnnihilation_mul_fermionCreation :
    dotProduct (star fermionOccupied)
      ((fermionAnnihilation * fermionCreation).mulVec fermionOccupied) =
      (0 : ℂ) := by
  rw [fermionAnnihilation_mul_fermionCreation_mulVec_occupied]
  simp [dotProduct]

end LatticeSystem.Fermion
