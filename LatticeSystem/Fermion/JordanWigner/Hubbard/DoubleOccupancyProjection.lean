import LatticeSystem.Fermion.JordanWigner.Hubbard

/-!
# Hubbard same-site double-occupancy operator: commute and idempotency

For a spinful Hubbard site `i` the up- and down-spin number
operators `n_↑(i)` and `n_↓(i)` live at distinct underlying JW
positions `2 i` and `2 i + 1`, hence

  `Commute (n_↑(i)) (n_↓(i))`,

and their product `n_↑(i) · n_↓(i)` is the on-site
double-occupancy operator. As the product of two commuting
idempotents (each `n_σ(i)² = n_σ(i)` via
`fermionMultiNumber_sq`), it is itself idempotent:

  `(n_↑(i) · n_↓(i))² = n_↑(i) · n_↓(i)`.

The eigenvalue-`1` subspace is the doubly-occupied site state,
so the on-site Hubbard interaction
`U · ∑_i n_↑(i) · n_↓(i)` is `U` times a sum of projections
(each summand is a projection by this PR; cross-site
commutation of summands is not proved here).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute (n_↑(i)) (n_↓(i))`: same-site cross-spin number
operators commute (they live at distinct JW positions
`2 i` and `2 i + 1`). -/
theorem fermionUpNumber_commute_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionUpNumber N i) (fermionDownNumber N i) := by
  unfold fermionUpNumber fermionDownNumber
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)

/-- `(n_↑(i) · n_↓(i))² = n_↑(i) · n_↓(i)`: the on-site
double-occupancy operator is idempotent (product of two
commuting idempotents). -/
theorem fermionUpNumber_mul_fermionDownNumber_sq
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i * fermionDownNumber N i) *
        (fermionUpNumber N i * fermionDownNumber N i) =
      fermionUpNumber N i * fermionDownNumber N i := by
  -- Using Commute n_↑ n_↓: (n_↑ n_↓)(n_↑ n_↓) = n_↑ (n_↓ n_↑) n_↓
  --                                          = n_↑ (n_↑ n_↓) n_↓
  --                                          = n_↑² n_↓² = n_↑ n_↓.
  have hcomm := fermionUpNumber_commute_fermionDownNumber N i
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fermionDownNumber N i),
    ← hcomm.eq, Matrix.mul_assoc, ← Matrix.mul_assoc (fermionUpNumber N i)]
  unfold fermionUpNumber fermionDownNumber
  rw [fermionMultiNumber_sq, fermionMultiNumber_sq]

end LatticeSystem.Fermion
