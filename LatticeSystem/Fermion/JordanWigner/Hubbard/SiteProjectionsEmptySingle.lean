import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsDoublyEmpty
import LatticeSystem.Fermion.JordanWigner.CDaggerCProjection

/-!
# Hubbard per-site empty projection orthogonal to single-occupancy projections

The empty per-site Hubbard projection is orthogonal to both
single-occupancy projections:

  `p_∅(i) · p_↑(i) = ((1-n_↑)(1-n_↓)) · (n_↑(1-n_↓)) = 0`,
  `p_↑(i) · p_∅(i) = (n_↑(1-n_↓)) · ((1-n_↑)(1-n_↓)) = 0`,
  `p_∅(i) · p_↓(i) = ((1-n_↑)(1-n_↓)) · ((1-n_↑)n_↓) = 0`,
  `p_↓(i) · p_∅(i) = ((1-n_↑)n_↓) · ((1-n_↑)(1-n_↓)) = 0`.

Same proof template as PRs #1014 and #1016: swap middle factors
via the same-site `Commute` propagated from `Commute n_↑ n_↓`
(PR #1005), then collapse via
- `(1 − n_σ) · n_σ = 0` for the empty-vs-single direction,
- `n_σ · (1 − n_σ) = 0` for the single-vs-empty direction
(specialised from PR #999 via `c_σ · c_σ† = 1 − n_σ`, PR #996).

Together with PRs #1014 and #1016 this covers four of six pairs
of cross-projection orthogonality for the per-site 4-state
decomposition (PR #1011); the remaining two (`p_↑·p_⇈`,
`p_↓·p_⇈`) follow the same template.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

private lemma fermionMultiNumber_mul_one_sub_self_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * (1 - fermionMultiNumber N i) = 0 := by
  have h := fermionMultiNumber_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero
    N i
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at h
  exact h

private lemma one_sub_fermionMultiNumber_mul_self_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionMultiNumber N i) * fermionMultiNumber N i = 0 := by
  have h := fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiNumber_eq_zero
    N i
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at h
  exact h

/-- `p_∅(i) · p_↑(i) = 0`. -/
theorem fermionEmptyProjection_mul_fermionUpProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) *
        (fermionUpNumber N i * (1 - fermionDownNumber N i)) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : (1 - fermionDownNumber N i) * fermionUpNumber N i =
      fermionUpNumber N i * (1 - fermionDownNumber N i) := by
    rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [one_sub_fermionMultiNumber_mul_self_eq_zero, Matrix.zero_mul]

/-- `p_↑(i) · p_∅(i) = 0`. -/
theorem fermionUpProjection_mul_fermionEmptyProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * (1 - fermionDownNumber N i)) *
        ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : (1 - fermionDownNumber N i) * (1 - fermionUpNumber N i) =
      (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) := by
    rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionDownNumber N i) *
        (1 - fermionUpNumber N i) =
        1 - fermionUpNumber N i - fermionDownNumber N i +
          fermionDownNumber N i * fermionUpNumber N i from by
      rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel,
      show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionUpNumber N i) *
        (1 - fermionDownNumber N i) =
        1 - fermionDownNumber N i - fermionUpNumber N i +
          fermionUpNumber N i * fermionDownNumber N i from by
      rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel]
    rw [hcomm.eq]; abel
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [fermionMultiNumber_mul_one_sub_self_eq_zero, Matrix.zero_mul]

/-- `p_∅(i) · p_↓(i) = 0`. -/
theorem fermionEmptyProjection_mul_fermionDownProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) *
        ((1 - fermionUpNumber N i) * fermionDownNumber N i) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : (1 - fermionDownNumber N i) * (1 - fermionUpNumber N i) =
      (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) := by
    rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionDownNumber N i) *
        (1 - fermionUpNumber N i) =
        1 - fermionUpNumber N i - fermionDownNumber N i +
          fermionDownNumber N i * fermionUpNumber N i from by
      rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel,
      show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionUpNumber N i) *
        (1 - fermionDownNumber N i) =
        1 - fermionDownNumber N i - fermionUpNumber N i +
          fermionUpNumber N i * fermionDownNumber N i from by
      rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel]
    rw [hcomm.eq]; abel
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [show (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) *
      (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) =
      1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) by
    have := fermionMultiAnnihilation_mul_fermionMultiCreation_sq (2 * N + 1)
      (spinfulIndex N i 0)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at this
    exact this]
  rw [one_sub_fermionMultiNumber_mul_self_eq_zero, Matrix.mul_zero]

/-- `p_↓(i) · p_∅(i) = 0`. -/
theorem fermionDownProjection_mul_fermionEmptyProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * fermionDownNumber N i) *
        ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : fermionDownNumber N i * (1 - fermionUpNumber N i) =
      (1 - fermionUpNumber N i) * fermionDownNumber N i := by
    rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [show (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) *
      (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) =
      1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) by
    have := fermionMultiAnnihilation_mul_fermionMultiCreation_sq (2 * N + 1)
      (spinfulIndex N i 0)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at this
    exact this]
  rw [fermionMultiNumber_mul_one_sub_self_eq_zero, Matrix.mul_zero]

end LatticeSystem.Fermion
