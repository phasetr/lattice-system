import LatticeSystem.Fermion.JordanWigner.Hubbard.SingleProjectionsCommute

/-!
# Cross-projection commute `Commute (p_↑(i)) (p_↓(j))` for any `i, j`

The only-up projection at site `i` commutes with the only-down
projection at any site `j`:

  `Commute (p_↑(i)) (p_↓(j))` for any `i, j`.

Same proof template as PRs #1006, #1035, #1036. For `i = j`
reduces to PR #1016's orthogonality (both products zero).
For `i ≠ j` it extends the diagonal cross-site commutes to a
non-diagonal projection pair.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

private lemma fermionMultiNumber_commute_one_sub_fermionMultiNumber''
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (1 - fermionMultiNumber N j) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute N i j).eq
  rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm]

private lemma one_sub_fermionMultiNumber_commute_fermionMultiNumber''
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (1 - fermionMultiNumber N i) (fermionMultiNumber N j) := by
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute N i j).eq
  rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

/-- `Commute (p_↑(i)) (p_↓(j))` for any `i, j`: cross-projection
only-up vs only-down commute. -/
theorem fermionUpProjection_commute_fermionDownProjection_of_any
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionUpNumber N i * (1 - fermionDownNumber N i))
      ((1 - fermionUpNumber N j) * fermionDownNumber N j) := by
  unfold fermionUpNumber fermionDownNumber
  -- Pairwise commute among {n_{2i}, 1-n_{2i+1}, 1-n_{2j}, n_{2j+1}}.
  have c00 := fermionMultiNumber_commute_one_sub_fermionMultiNumber''
    (2 * N + 1) (spinfulIndex N i 0) (spinfulIndex N j 0)
  have c01 := fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 1)
  have c10 :
      Commute (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1))
        (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0)) := by
    unfold Commute SemiconjBy
    have hcomm := (fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N i 1) (spinfulIndex N j 0)).eq
    rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) -
        fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1)) *
        (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0)) =
        1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0) -
          fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1) +
          fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1) *
            fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0) from by
      rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel,
      show ((1 : ManyBodyOp (Fin (2 * N + 2))) -
        fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0)) *
        (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1)) =
        1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1) -
          fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0) +
          fermionMultiNumber (2 * N + 1) (spinfulIndex N j 0) *
            fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1) from by
      rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel]
    rw [hcomm]; abel
  have c11 := one_sub_fermionMultiNumber_commute_fermionMultiNumber''
    (2 * N + 1) (spinfulIndex N i 1) (spinfulIndex N j 1)
  exact Commute.mul_right (Commute.mul_left c00 c10)
    (Commute.mul_left c01 c11)

end LatticeSystem.Fermion
