import LatticeSystem.Fermion.JordanWigner.AnnihilationNumberIdentities

/-!
# Multi-mode Jordan–Wigner number-creation identities
`c_i† · n_i = 0` and `n_i · c_i† = c_i†`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #984;
companion to PR #1001. Same-site number-creation identities

  `c_i† · n_i = 0`,
  `n_i · c_i† = c_i†`.

Proofs:
- `c_i† · n_i = c_i† · (c_i† · c_i) = (c_i†)² · c_i
              = 0 · c_i = 0`
  via `fermionMultiCreation_sq`.
- `n_i · c_i† = (c_i† · c_i) · c_i† = c_i† · (c_i · c_i†)
              = c_i† · (1 − n_i) = c_i† − c_i† · n_i = c_i†`
  via `c_i · c_i† = 1 − n_i` (PR #996) and the previous.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `c_i† · n_i = 0` (multi-mode same-site creation-number
identity). -/
theorem fermionMultiCreation_mul_fermionMultiNumber_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiCreation N i * fermionMultiNumber N i = 0 := by
  -- n_i = c_i† · c_i (definitional).
  rw [show fermionMultiNumber N i =
      fermionMultiCreation N i * fermionMultiAnnihilation N i from rfl,
    ← Matrix.mul_assoc, fermionMultiCreation_sq, Matrix.zero_mul]

/-- `n_i · c_i† = c_i†` (multi-mode same-site number-creation
identity). -/
theorem fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiCreation N i =
      fermionMultiCreation N i := by
  -- n_i · c_i† = (c_i† · c_i) · c_i† = c_i† · (c_i · c_i†)
  --           = c_i† · (1 − n_i) = c_i† − c_i† · n_i = c_i†.
  rw [show fermionMultiNumber N i =
      fermionMultiCreation N i * fermionMultiAnnihilation N i from rfl,
    Matrix.mul_assoc,
    fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number,
    mul_sub, Matrix.mul_one,
    fermionMultiCreation_mul_fermionMultiNumber_eq_zero, sub_zero]

end LatticeSystem.Fermion
