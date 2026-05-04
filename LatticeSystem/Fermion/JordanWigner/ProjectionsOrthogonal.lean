import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Multi-mode Jordan–Wigner orthogonal projections
`n_i · (c_i · c_i†) = 0` and `(c_i · c_i†) · n_i = 0`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #976. The
two complementary projections at site `i` are orthogonal in
either order:

  `n_i · (c_i · c_i†) = 0`,
  `(c_i · c_i†) · n_i = 0`.

Direct from `c_i² = 0` (`fermionMultiAnnihilation_sq`) and
`(c_i†)² = 0` (`fermionMultiCreation_sq`):

- `n_i · (c_i · c_i†) = (c_i† · c_i) · (c_i · c_i†)
                     = c_i† · (c_i · c_i) · c_i†
                     = c_i† · 0 · c_i† = 0`.
- `(c_i · c_i†) · n_i = (c_i · c_i†) · (c_i† · c_i)
                     = c_i · (c_i† · c_i†) · c_i
                     = c_i · 0 · c_i = 0`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `n_i · (c_i · c_i†) = 0` (multi-mode orthogonal projections). -/
theorem fermionMultiNumber_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i *
        (fermionMultiAnnihilation N i * fermionMultiCreation N i) =
      0 := by
  -- n_i = c_i† · c_i (definitional).
  rw [show fermionMultiNumber N i =
      fermionMultiCreation N i * fermionMultiAnnihilation N i from rfl]
  -- (c_i† · c_i) · (c_i · c_i†) = c_i† · (c_i · c_i) · c_i† = 0.
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fermionMultiAnnihilation N i)
      (fermionMultiAnnihilation N i),
    fermionMultiAnnihilation_sq, Matrix.zero_mul, Matrix.mul_zero]

/-- `(c_i · c_i†) · n_i = 0` (multi-mode orthogonal projections). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiNumber_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i * fermionMultiCreation N i) *
        fermionMultiNumber N i =
      0 := by
  rw [show fermionMultiNumber N i =
      fermionMultiCreation N i * fermionMultiAnnihilation N i from rfl]
  -- (c_i · c_i†) · (c_i† · c_i) = c_i · (c_i† · c_i†) · c_i = 0.
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fermionMultiCreation N i)
      (fermionMultiCreation N i),
    fermionMultiCreation_sq, Matrix.zero_mul, Matrix.mul_zero]

end LatticeSystem.Fermion
