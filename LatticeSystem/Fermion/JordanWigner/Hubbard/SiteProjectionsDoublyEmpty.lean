import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection
import LatticeSystem.Fermion.JordanWigner.ProjectionsOrthogonal
import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity

/-!
# Hubbard per-site doubly-occupied and empty projections orthogonal

The doubly-occupied and empty per-site occupation projections
are mutually orthogonal:

  `p_⇈(i) · p_∅(i) = (n_↑·n_↓) · ((1-n_↑)·(1-n_↓)) = 0`,
  `p_∅(i) · p_⇈(i) = ((1-n_↑)·(1-n_↓)) · (n_↑·n_↓) = 0`.

Direct from
- the same-site `Commute n_↑(i) n_↓(i)` (PR #1005), and
- `n_σ · (1 - n_σ) = (1 - n_σ) · n_σ = 0`
  (specialised from PR #999 via `c_σ · c_σ† = 1 − n_σ`, PR #996).

This is the most extreme pair of the per-site 4-state
decomposition (PR #1011): "doubly occupied" cannot share with
"empty".

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

private lemma fermionMultiNumber_mul_one_sub_self_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * (1 - fermionMultiNumber N i) = 0 := by
  have h := fermionMultiNumber_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero
    N i
  -- h : n_i · (c_i · c_i†) = 0; rewrite c_i · c_i† = 1 − n_i.
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at h
  exact h

private lemma one_sub_fermionMultiNumber_mul_self_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (1 - fermionMultiNumber N i) * fermionMultiNumber N i = 0 := by
  have h := fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiNumber_eq_zero
    N i
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at h
  exact h

/-- `p_⇈(i) · p_∅(i) = 0` (doubly occupied annihilates empty
on the right). -/
theorem fermionUpDownNumber_mul_empty_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * fermionDownNumber N i) *
        ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : fermionDownNumber N i * (1 - fermionUpNumber N i) =
      (1 - fermionUpNumber N i) * fermionDownNumber N i := by
    rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  -- (n_↑ n_↓) · ((1-n_↑)(1-n_↓))
  --   = n_↑ · (n_↓ · (1-n_↑)) · (1-n_↓)
  --   = n_↑ · ((1-n_↑) · n_↓) · (1-n_↓)
  --   = (n_↑ · (1-n_↑)) · (n_↓ · (1-n_↓)) = 0 · 0 = 0.
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [fermionMultiNumber_mul_one_sub_self_eq_zero, Matrix.zero_mul]

/-- `p_∅(i) · p_⇈(i) = 0` (empty annihilates doubly occupied
on the right). -/
theorem empty_mul_fermionUpDownNumber_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) *
        (fermionUpNumber N i * fermionDownNumber N i) =
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

end LatticeSystem.Fermion
