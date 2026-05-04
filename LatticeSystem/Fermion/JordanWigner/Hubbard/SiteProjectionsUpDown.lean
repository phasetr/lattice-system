import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsDoublyEmpty

/-!
# Hubbard per-site only-up and only-down projections orthogonal

The only-up and only-down per-site Hubbard occupation projections
are mutually orthogonal:

  `p_↑(i) · p_↓(i) = (n_↑·(1-n_↓)) · ((1-n_↑)·n_↓) = 0`,
  `p_↓(i) · p_↑(i) = ((1-n_↑)·n_↓) · (n_↑·(1-n_↓)) = 0`.

The proofs swap the middle factors using the same-site
`Commute (1 − n_↓) (1 − n_↑)` (and the dual), then collapse via
- `n_σ · (1 − n_σ) = 0`
- `(1 − n_σ) · n_σ = 0`
(specialised from PR #999 via `c_σ · c_σ† = 1 − n_σ`, PR #996).

Together with PR #1014 (`p_⇈ · p_∅ = 0`) this covers two of the
six pairs of cross-projection orthogonality for the per-site
4-state decomposition (PR #1011).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `p_↑(i) · p_↓(i) = 0` (only-up annihilates only-down on
the right). -/
theorem fermionUpProjection_mul_fermionDownProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * (1 - fermionDownNumber N i)) *
        ((1 - fermionUpNumber N i) * fermionDownNumber N i) =
      0 := by
  -- Swap the middle factors via Commute (1-n_↓) (1-n_↑).
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
  -- (n_↑ * (1 - n_↑)) * ((1 - n_↓) * n_↓) = 0 * 0 = 0.
  rw [show fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) *
      (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) = 0 by
    have h := fermionMultiNumber_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero
      (2 * N + 1) (spinfulIndex N i 0)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at h
    exact h, Matrix.zero_mul]

/-- `p_↓(i) · p_↑(i) = 0` (only-down annihilates only-up on
the right). -/
theorem fermionDownProjection_mul_fermionUpProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * fermionDownNumber N i) *
        (fermionUpNumber N i * (1 - fermionDownNumber N i)) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : fermionDownNumber N i * fermionUpNumber N i =
      fermionUpNumber N i * fermionDownNumber N i := hcomm.symm.eq
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  -- ((1 - n_↑) * n_↑) * (n_↓ * (1 - n_↓)) = 0 * 0 = 0.
  rw [show (1 - fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) *
      fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) = 0 by
    have h := fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiNumber_eq_zero
      (2 * N + 1) (spinfulIndex N i 0)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at h
    exact h, Matrix.zero_mul]

end LatticeSystem.Fermion
