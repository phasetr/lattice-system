import LatticeSystem.Fermion.Mode

/-!
# Fermion vacuum and occupied basis states are orthonormal

For the single-mode fermion (`Fin 2 → ℂ`), the basis vectors
`|0⟩ = !![1, 0]` and `|1⟩ = !![0, 1]` form an orthonormal pair:

- `⟨|0⟩, |0⟩⟩ = 1`, `⟨|1⟩, |1⟩⟩ = 1`.
- `⟨|0⟩, |1⟩⟩ = 0`, `⟨|1⟩, |0⟩⟩ = 0`.

Direct entrywise computation.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `⟨|0⟩, |0⟩⟩ = 1`. -/
theorem fermionVacuum_inner_self :
    dotProduct (star fermionVacuum) fermionVacuum = (1 : ℂ) := by
  unfold fermionVacuum dotProduct
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- `⟨|1⟩, |1⟩⟩ = 1`. -/
theorem fermionOccupied_inner_self :
    dotProduct (star fermionOccupied) fermionOccupied = (1 : ℂ) := by
  unfold fermionOccupied dotProduct
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- `⟨|0⟩, |1⟩⟩ = 0`. -/
theorem fermionVacuum_inner_fermionOccupied :
    dotProduct (star fermionVacuum) fermionOccupied = (0 : ℂ) := by
  unfold fermionVacuum fermionOccupied dotProduct
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- `⟨|1⟩, |0⟩⟩ = 0`. -/
theorem fermionOccupied_inner_fermionVacuum :
    dotProduct (star fermionOccupied) fermionVacuum = (0 : ℂ) := by
  unfold fermionVacuum fermionOccupied dotProduct
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end LatticeSystem.Fermion
