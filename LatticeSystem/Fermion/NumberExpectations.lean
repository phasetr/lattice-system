import LatticeSystem.Fermion.StatesOrthonormal

/-!
# Number operator expectation values on basis states

For the single-mode fermion:

- `⟨|0⟩, n |0⟩⟩ = 0` (vacuum is unoccupied).
- `⟨|1⟩, n |1⟩⟩ = 1` (occupied state has occupation 1).

Direct from `fermionNumber_mulVec_{vacuum, occupied}` (Mode.lean)
combined with the orthonormality of vacuum and occupied
(PR #968).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `⟨|0⟩, n |0⟩⟩ = 0`. -/
theorem fermionVacuum_expectation_fermionNumber :
    dotProduct (star fermionVacuum)
      (fermionNumber.mulVec fermionVacuum) = (0 : ℂ) := by
  rw [fermionNumber_mulVec_vacuum]
  simp [dotProduct]

/-- `⟨|1⟩, n |1⟩⟩ = 1`. -/
theorem fermionOccupied_expectation_fermionNumber :
    dotProduct (star fermionOccupied)
      (fermionNumber.mulVec fermionOccupied) = (1 : ℂ) := by
  rw [fermionNumber_mulVec_occupied]
  exact fermionOccupied_inner_self

end LatticeSystem.Fermion
