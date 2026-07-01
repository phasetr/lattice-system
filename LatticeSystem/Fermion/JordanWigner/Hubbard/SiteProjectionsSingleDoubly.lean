import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsDoublyEmpty

/-!
# Hubbard per-site single-occupancy ⊥ doubly-occupied projections

Final two pairs of cross-projection orthogonality for the
per-site Hubbard 4-state decomposition (PR #1011):

  `p_↑(i) · p_⇈(i) = (n_↑(1−n_↓)) · (n_↑·n_↓) = 0`,
  `p_⇈(i) · p_↑(i) = (n_↑·n_↓) · (n_↑(1−n_↓)) = 0`,
  `p_↓(i) · p_⇈(i) = ((1−n_↑)n_↓) · (n_↑·n_↓) = 0`,
  `p_⇈(i) · p_↓(i) = (n_↑·n_↓) · ((1−n_↑)n_↓) = 0`.

Same proof template as PRs #1014, #1016, #1017: swap middle
factors via the same-site `Commute` propagated from
`Commute n_↑ n_↓` (PR #1005), then collapse via
- `n_σ · n_σ = n_σ` (`fermionMultiNumber_sq`),
- `n_σ · (1 − n_σ) = 0` (specialised from PR #999).

Together with PRs #1014, #1016, #1017 **all 6 pairs of
cross-projection orthogonality are now formalised**,
completing the proof that `{p_∅, p_↑, p_↓, p_⇈}` is a complete
set of mutually orthogonal Hermitian projections summing to the
identity.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `p_↑(i) · p_⇈(i) = 0`. -/
theorem fermionUpProjection_mul_fermionDoublyProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * (1 - fermionDownNumber N i)) *
        (fermionUpNumber N i * fermionDownNumber N i) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : (1 - fermionDownNumber N i) * fermionUpNumber N i =
      fermionUpNumber N i * (1 - fermionDownNumber N i) := by
    rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  -- (n_↑(1-n_↓)) · (n_↑·n_↓) = n_↑ · ((1-n_↓) · n_↑) · n_↓
  --                          = n_↑ · (n_↑(1-n_↓)) · n_↓
  --                          = (n_↑ · n_↑) · ((1-n_↓) · n_↓) = n_↑ · 0 = 0.
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [show fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) *
      fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) =
      fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) from
      fermionMultiNumber_sq _ _,
    one_sub_fermionMultiNumber_mul_self_eq_zero, Matrix.mul_zero]

/-- `p_⇈(i) · p_↑(i) = 0`. -/
theorem fermionDoublyProjection_mul_fermionUpProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * fermionDownNumber N i) *
        (fermionUpNumber N i * (1 - fermionDownNumber N i)) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : fermionDownNumber N i * fermionUpNumber N i =
      fermionUpNumber N i * fermionDownNumber N i := hcomm.symm.eq
  -- (n_↑·n_↓) · (n_↑(1-n_↓)) = n_↑ · (n_↓ · n_↑) · (1-n_↓)
  --                          = n_↑ · (n_↑ · n_↓) · (1-n_↓)
  --                          = (n_↑ · n_↑) · (n_↓ · (1-n_↓)) = n_↑ · 0 = 0.
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [show fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) *
      fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) =
      fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) from
      fermionMultiNumber_sq _ _,
    fermionMultiNumber_mul_one_sub_self_eq_zero, Matrix.mul_zero]

/-- `p_↓(i) · p_⇈(i) = 0`. -/
theorem fermionDownProjection_mul_fermionDoublyProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * fermionDownNumber N i) *
        (fermionUpNumber N i * fermionDownNumber N i) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : fermionDownNumber N i * fermionUpNumber N i =
      fermionUpNumber N i * fermionDownNumber N i := hcomm.symm.eq
  -- ((1-n_↑)n_↓) · (n_↑·n_↓) = (1-n_↑) · (n_↓ · n_↑) · n_↓
  --                          = (1-n_↑) · (n_↑ · n_↓) · n_↓
  --                          = ((1-n_↑) · n_↑) · (n_↓ · n_↓) = 0 · n_↓ = 0.
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [one_sub_fermionMultiNumber_mul_self_eq_zero, Matrix.zero_mul]

/-- `p_⇈(i) · p_↓(i) = 0`. -/
theorem fermionDoublyProjection_mul_fermionDownProjection_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * fermionDownNumber N i) *
        ((1 - fermionUpNumber N i) * fermionDownNumber N i) =
      0 := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : fermionDownNumber N i * (1 - fermionUpNumber N i) =
      (1 - fermionUpNumber N i) * fermionDownNumber N i := by
    rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  -- (n_↑·n_↓) · ((1-n_↑)n_↓) = n_↑ · (n_↓ · (1-n_↑)) · n_↓
  --                          = n_↑ · ((1-n_↑) · n_↓) · n_↓
  --                          = (n_↑ · (1-n_↑)) · (n_↓ · n_↓) = 0 · n_↓ = 0.
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm', Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [fermionMultiNumber_mul_one_sub_self_eq_zero, Matrix.zero_mul]

end LatticeSystem.Fermion
