import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection

/-!
# Cross-site Hubbard double-occupancy operators commute

For any two sites `i, j` the double-occupancy operators commute:

  `Commute (n_↑(i) · n_↓(i)) (n_↑(j) · n_↓(j))`.

All four underlying single-species number operators
`n_↑(i), n_↓(i), n_↑(j), n_↓(j)` live at JW positions `2 i`,
`2 i + 1`, `2 j`, `2 j + 1` (possibly with `i = j`); they
pairwise commute by `fermionMultiNumber_commute`. The products
therefore commute by repeated application of
`Commute.mul_left` / `Commute.mul_right`.

Combined with PR #1005 (each summand is a projection), this
shows the on-site Hubbard interaction
`U · ∑_i n_↑(i) · n_↓(i)` is `U` times a sum of pairwise
commuting projections, hence simultaneously diagonalisable.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute (n_↑(i) · n_↓(i)) (n_↑(j) · n_↓(j))`: cross-site
double-occupancy operators commute. -/
theorem fermionUpNumber_mul_fermionDownNumber_commute
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute
      (fermionUpNumber N i * fermionDownNumber N i)
      (fermionUpNumber N j * fermionDownNumber N j) := by
  unfold fermionUpNumber fermionDownNumber
  -- The four underlying number operators pairwise commute.
  have c00 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 0)
  have c01 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 1)
  have c10 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N j 0)
  have c11 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N j 1)
  -- `Commute (n_{2i} * n_{2i+1}) n_{2j}` from c00 and c10.
  have h0 := Commute.mul_left c00 c10
  -- `Commute (n_{2i} * n_{2i+1}) n_{2j+1}` from c01 and c11.
  have h1 := Commute.mul_left c01 c11
  -- Combine to `Commute (n_{2i} * n_{2i+1}) (n_{2j} * n_{2j+1})`.
  exact Commute.mul_right h0 h1

end LatticeSystem.Fermion
