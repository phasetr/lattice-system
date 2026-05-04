import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection

/-!
# Cross-site Hubbard single-occupancy projections commute

For any two sites `i, j` the single-occupancy per-site Hubbard
projections commute:

  `Commute (p_↑(i)) (p_↑(j))` for any `i, j`,
  `Commute (p_↓(i)) (p_↓(j))` for any `i, j`.

Both follow from the same pattern as PRs #1006 (`p_⇈`) and
#1035 (`p_∅`): the four underlying number operators (and their
complements) pairwise commute via `fermionMultiNumber_commute`,
so the products commute via `Commute.mul_left` / `.mul_right`.

Together with PRs #1006 and #1035 this completes the cross-site
diagonal Commute relations for all four per-site occupation
projections.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

private lemma fermionMultiNumber_commute_one_sub_fermionMultiNumber'
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (1 - fermionMultiNumber N j) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute N i j).eq
  rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm]

private lemma one_sub_fermionMultiNumber_commute_fermionMultiNumber'
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (1 - fermionMultiNumber N i) (fermionMultiNumber N j) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute N i j).eq
  rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

private lemma one_sub_one_sub_commute
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (1 - fermionMultiNumber N i) (1 - fermionMultiNumber N j) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute N i j).eq
  rw [show ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i) *
      (1 - fermionMultiNumber N j) =
      1 - fermionMultiNumber N j - fermionMultiNumber N i +
        fermionMultiNumber N i * fermionMultiNumber N j from by
    rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel,
    show ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N j) *
      (1 - fermionMultiNumber N i) =
      1 - fermionMultiNumber N i - fermionMultiNumber N j +
        fermionMultiNumber N j * fermionMultiNumber N i from by
    rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel]
  rw [hcomm]; abel

/-- `Commute (p_↑(i)) (p_↑(j))` for any `i, j`: cross-site
only-up projections commute. -/
theorem fermionUpProjection_commute_of_any
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionUpNumber N i * (1 - fermionDownNumber N i))
      (fermionUpNumber N j * (1 - fermionDownNumber N j)) := by
  unfold fermionUpNumber fermionDownNumber
  have c00 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 0)
  have c01 := fermionMultiNumber_commute_one_sub_fermionMultiNumber'
    (2 * N + 1) (spinfulIndex N i 0) (spinfulIndex N j 1)
  have c10 := one_sub_fermionMultiNumber_commute_fermionMultiNumber'
    (2 * N + 1) (spinfulIndex N i 1) (spinfulIndex N j 0)
  have c11 := one_sub_one_sub_commute (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N j 1)
  exact Commute.mul_right (Commute.mul_left c00 c10)
    (Commute.mul_left c01 c11)

/-- `Commute (p_↓(i)) (p_↓(j))` for any `i, j`: cross-site
only-down projections commute. -/
theorem fermionDownProjection_commute_of_any
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute ((1 - fermionUpNumber N i) * fermionDownNumber N i)
      ((1 - fermionUpNumber N j) * fermionDownNumber N j) := by
  unfold fermionUpNumber fermionDownNumber
  have c00 := one_sub_one_sub_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 0)
  have c01 := one_sub_fermionMultiNumber_commute_fermionMultiNumber'
    (2 * N + 1) (spinfulIndex N i 0) (spinfulIndex N j 1)
  have c10 := fermionMultiNumber_commute_one_sub_fermionMultiNumber'
    (2 * N + 1) (spinfulIndex N i 1) (spinfulIndex N j 0)
  have c11 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N j 1)
  exact Commute.mul_right (Commute.mul_left c00 c10)
    (Commute.mul_left c01 c11)

end LatticeSystem.Fermion
