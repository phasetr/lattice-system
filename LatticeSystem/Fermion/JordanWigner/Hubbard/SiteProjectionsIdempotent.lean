import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection
import LatticeSystem.Fermion.JordanWigner.CDaggerCProjection

/-!
# Hubbard per-site empty/up/down occupation projections are idempotent

Three companion idempotency lemmas to PR #1005 (which proved
`(n_↑·n_↓)² = n_↑·n_↓`):

  `((1 − n_↑(i)) · (1 − n_↓(i)))² = (1 − n_↑(i)) · (1 − n_↓(i))`,
  `(n_↑(i) · (1 − n_↓(i)))²       = n_↑(i) · (1 − n_↓(i))`,
  `((1 − n_↑(i)) · n_↓(i))²       = (1 − n_↑(i)) · n_↓(i)`.

Together with PR #1005 these establish that all four per-site
occupation operators
`p_∅, p_↑, p_↓, p_⇈` (PR #1011) are projections.

Each proof uses the same-site `Commute n_↑(i) n_↓(i)` (PR #1005)
to swap the middle factors, then applies the squared identities
- `fermionMultiNumber_sq` (`n_σ² = n_σ`),
- `fermionMultiAnnihilation_mul_fermionMultiCreation_sq` via the
  `c_σ · c_σ† = 1 − n_σ` rewrite (PRs #996, #997).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `((1 − n_↑(i)) · (1 − n_↓(i)))² = (1 − n_↑(i)) · (1 − n_↓(i))`
(empty per-site projection). -/
theorem one_sub_fermionUpNumber_mul_one_sub_fermionDownNumber_sq
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) *
        ((1 - fermionUpNumber N i) * (1 - fermionDownNumber N i)) =
      (1 - fermionUpNumber N i) * (1 - fermionDownNumber N i) := by
  -- Swap the middle two factors via Commute (1 - n_↑) (1 - n_↓)
  -- (which follows from Commute n_↑ n_↓).
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : Commute (1 - fermionDownNumber N i)
      (1 - fermionUpNumber N i) := by
    unfold Commute SemiconjBy
    rw [show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionDownNumber N i) *
        (1 - fermionUpNumber N i) =
        1 - fermionUpNumber N i - fermionDownNumber N i +
          fermionDownNumber N i * fermionUpNumber N i from by
      rw [sub_mul, mul_sub, mul_sub]
      simp only [one_mul, mul_one]
      abel,
      show ((1 : ManyBodyOp (Fin (2 * N + 2))) - fermionUpNumber N i) *
        (1 - fermionDownNumber N i) =
        1 - fermionDownNumber N i - fermionUpNumber N i +
          fermionUpNumber N i * fermionDownNumber N i from by
      rw [sub_mul, mul_sub, mul_sub]
      simp only [one_mul, mul_one]
      abel]
    rw [hcomm.eq]
    abel
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionDownNumber N i),
    hcomm'.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  -- Now: (1 - n_↑)² * (1 - n_↓)² = (1 - n_↑) * (1 - n_↓).
  -- We need (1 - n_σ)² = (1 - n_σ) for σ = ↑, ↓.
  have h_up_sq : (1 - fermionUpNumber N i) *
      (1 - fermionUpNumber N i) = 1 - fermionUpNumber N i := by
    have := fermionMultiAnnihilation_mul_fermionMultiCreation_sq
      (2 * N + 1) (spinfulIndex N i 0)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at this
    exact this
  have h_down_sq : (1 - fermionDownNumber N i) *
      (1 - fermionDownNumber N i) = 1 - fermionDownNumber N i := by
    have := fermionMultiAnnihilation_mul_fermionMultiCreation_sq
      (2 * N + 1) (spinfulIndex N i 1)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at this
    exact this
  rw [h_up_sq, h_down_sq]

/-- `(n_↑(i) · (1 − n_↓(i)))² = n_↑(i) · (1 − n_↓(i))` (only-up
per-site projection). -/
theorem fermionUpNumber_mul_one_sub_fermionDownNumber_sq
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * (1 - fermionDownNumber N i)) *
        (fermionUpNumber N i * (1 - fermionDownNumber N i)) =
      fermionUpNumber N i * (1 - fermionDownNumber N i) := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : Commute (1 - fermionDownNumber N i)
      (fermionUpNumber N i) := by
    unfold Commute SemiconjBy
    rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionDownNumber N i),
    hcomm'.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionUpNumber N i)]
  have h_up_sq := fermionMultiNumber_sq (2 * N + 1) (spinfulIndex N i 0)
  have h_down_sq : (1 - fermionDownNumber N i) *
      (1 - fermionDownNumber N i) = 1 - fermionDownNumber N i := by
    have := fermionMultiAnnihilation_mul_fermionMultiCreation_sq
      (2 * N + 1) (spinfulIndex N i 1)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at this
    exact this
  unfold fermionUpNumber
  rw [h_up_sq, h_down_sq]

/-- `((1 − n_↑(i)) · n_↓(i))² = (1 − n_↑(i)) · n_↓(i)` (only-down
per-site projection). -/
theorem one_sub_fermionUpNumber_mul_fermionDownNumber_sq
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 - fermionUpNumber N i) * fermionDownNumber N i) *
        ((1 - fermionUpNumber N i) * fermionDownNumber N i) =
      (1 - fermionUpNumber N i) * fermionDownNumber N i := by
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  have hcomm' : Commute (fermionDownNumber N i)
      (1 - fermionUpNumber N i) := by
    unfold Commute SemiconjBy
    rw [mul_sub, sub_mul, Matrix.one_mul, Matrix.mul_one, hcomm.eq]
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (fermionDownNumber N i),
    hcomm'.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - fermionUpNumber N i)]
  have h_up_sq : (1 - fermionUpNumber N i) *
      (1 - fermionUpNumber N i) = 1 - fermionUpNumber N i := by
    have := fermionMultiAnnihilation_mul_fermionMultiCreation_sq
      (2 * N + 1) (spinfulIndex N i 0)
    rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number] at this
    exact this
  have h_down_sq := fermionMultiNumber_sq (2 * N + 1) (spinfulIndex N i 1)
  unfold fermionDownNumber
  rw [h_up_sq, h_down_sq]

end LatticeSystem.Fermion
