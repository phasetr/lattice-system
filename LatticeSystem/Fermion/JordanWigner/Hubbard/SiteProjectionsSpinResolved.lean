import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection

/-!
# Hubbard per-site projection-aggregation identities

Spin-resolved aggregation identities of the per-site Hubbard
projections:

  `p_↑(i) + p_⇈(i) = n_↑(i)`,     (any spin-up presence)
  `p_↓(i) + p_⇈(i) = n_↓(i)`,     (any spin-down presence)
  `p_∅(i) + p_↑(i) = 1 − n_↓(i)`, (spin-down absent)
  `p_∅(i) + p_↓(i) = 1 − n_↑(i)`. (spin-up absent)

Direct algebraic identities via factoring out the common
left/right factor and using `(1 − n_σ) + n_σ = 1`. These show
how the per-site 4-state projections aggregate to the
spin-resolved number operators (and their complements),
complementing the partition-of-identity (PR #1011).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `p_↑(i) + p_⇈(i) = n_↑(i)` (any spin-up presence). -/
theorem fermionUpProjection_add_fermionDoublyProjection_eq_fermionUpNumber
    (N : ℕ) (i : Fin (N + 1)) :
    fermionUpNumber N i * (1 - fermionDownNumber N i) +
        fermionUpNumber N i * fermionDownNumber N i =
      fermionUpNumber N i := by
  rw [show fermionUpNumber N i * (1 - fermionDownNumber N i) +
        fermionUpNumber N i * fermionDownNumber N i =
      fermionUpNumber N i * ((1 - fermionDownNumber N i) +
        fermionDownNumber N i) from by rw [mul_add]]
  rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) -
        fermionDownNumber N i) + fermionDownNumber N i = 1 from by abel]
  rw [Matrix.mul_one]

/-- `p_↓(i) + p_⇈(i) = n_↓(i)` (any spin-down presence). -/
theorem fermionDownProjection_add_fermionDoublyProjection_eq_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionUpNumber N i) * fermionDownNumber N i +
        fermionUpNumber N i * fermionDownNumber N i =
      fermionDownNumber N i := by
  rw [show (1 - fermionUpNumber N i) * fermionDownNumber N i +
        fermionUpNumber N i * fermionDownNumber N i =
      ((1 - fermionUpNumber N i) + fermionUpNumber N i) *
        fermionDownNumber N i from by rw [add_mul]]
  rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) -
        fermionUpNumber N i) + fermionUpNumber N i = 1 from by abel]
  rw [Matrix.one_mul]

/-- `p_∅(i) + p_↑(i) = 1 − n_↓(i)` (spin-down absent). -/
theorem fermionEmptyProjection_add_fermionUpProjection_eq_one_sub_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) +
        fermionUpNumber N i * (1 - fermionDownNumber N i) =
      1 - fermionDownNumber N i := by
  rw [show (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) +
        fermionUpNumber N i * (1 - fermionDownNumber N i) =
      ((1 - fermionUpNumber N i) + fermionUpNumber N i) *
        (1 - fermionDownNumber N i) from by rw [add_mul]]
  rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) -
        fermionUpNumber N i) + fermionUpNumber N i = 1 from by abel]
  rw [Matrix.one_mul]

/-- `p_∅(i) + p_↓(i) = 1 − n_↑(i)` (spin-up absent). -/
theorem fermionEmptyProjection_add_fermionDownProjection_eq_one_sub_fermionUpNumber
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) +
        (1 - fermionUpNumber N i) * fermionDownNumber N i =
      1 - fermionUpNumber N i := by
  rw [show (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) +
        (1 - fermionUpNumber N i) * fermionDownNumber N i =
      (1 - fermionUpNumber N i) * ((1 - fermionDownNumber N i) +
        fermionDownNumber N i) from by rw [mul_add]]
  rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) -
        fermionDownNumber N i) + fermionDownNumber N i = 1 from by abel]
  rw [Matrix.mul_one]

end LatticeSystem.Fermion
