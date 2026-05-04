import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection

/-!
# Cross-site Hubbard empty projection commute

For any two sites `i, j` the empty per-site Hubbard projection
commutes with itself:

  `Commute (p_∅(i)) (p_∅(j))`.

All four underlying single-species number operators
`n_↑(i), n_↓(i), n_↑(j), n_↓(j)` pairwise commute via
`fermionMultiNumber_commute`, and so do the complementary
`(1 − n_σ)` (by ring algebra). The product `(1 − n_↑(i))
(1 − n_↓(i))` of commuting Hermitians at site `i` therefore
commutes with the analogous product at site `j` (via repeated
`Commute.mul_left` / `Commute.mul_right`).

Companion to PR #1006 (`Commute (p_⇈(i)) (p_⇈(j))`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

private lemma one_sub_fermionMultiNumber_commute_one_sub_fermionMultiNumber
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
  rw [hcomm]
  abel

/-- `Commute (p_∅(i)) (p_∅(j))`: cross-site empty projections
commute. -/
theorem fermionEmptyProjection_commute_of_any
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i))
      ((1 - fermionUpNumber N j) * (1 - fermionDownNumber N j)) := by
  unfold fermionUpNumber fermionDownNumber
  -- Pairwise commute among {1 - n_{2i}, 1 - n_{2i+1}, 1 - n_{2j}, 1 - n_{2j+1}}.
  have c00 := one_sub_fermionMultiNumber_commute_one_sub_fermionMultiNumber
    (2 * N + 1) (spinfulIndex N i 0) (spinfulIndex N j 0)
  have c01 := one_sub_fermionMultiNumber_commute_one_sub_fermionMultiNumber
    (2 * N + 1) (spinfulIndex N i 0) (spinfulIndex N j 1)
  have c10 := one_sub_fermionMultiNumber_commute_one_sub_fermionMultiNumber
    (2 * N + 1) (spinfulIndex N i 1) (spinfulIndex N j 0)
  have c11 := one_sub_fermionMultiNumber_commute_one_sub_fermionMultiNumber
    (2 * N + 1) (spinfulIndex N i 1) (spinfulIndex N j 1)
  -- ((1-n_{2i})(1-n_{2i+1})) commutes with (1-n_{2j}) from c00, c10.
  have h0 := Commute.mul_left c00 c10
  -- ... and with (1-n_{2j+1}) from c01, c11.
  have h1 := Commute.mul_left c01 c11
  -- Combine to product-product commute.
  exact Commute.mul_right h0 h1

end LatticeSystem.Fermion
