import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity

/-!
# Multi-mode Jordan–Wigner number-annihilation identities
`n_i · c_i = 0` and `c_i · n_i = c_i`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #982. The
two same-site identities

  `n_i · c_i = 0`,
  `c_i · n_i = c_i`.

Proofs:
- `n_i · c_i = (c_i† · c_i) · c_i = c_i† · (c_i · c_i) = c_i† · 0 = 0`
  via `fermionMultiAnnihilation_sq`.
- `c_i · n_i = c_i · (c_i† · c_i) = (c_i · c_i†) · c_i
            = (1 − n_i) · c_i = c_i − n_i · c_i = c_i`
  via `c_i · c_i† = 1 − n_i` (PR #996) and the previous identity.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `n_i · c_i = 0` (multi-mode same-site number-annihilation
identity). -/
theorem fermionMultiNumber_mul_fermionMultiAnnihilation_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiAnnihilation N i = 0 := by
  -- n_i = c_i† · c_i (definitional).
  rw [show fermionMultiNumber N i =
      fermionMultiCreation N i * fermionMultiAnnihilation N i from rfl,
    Matrix.mul_assoc, fermionMultiAnnihilation_sq, Matrix.mul_zero]

/-- `c_i · n_i = c_i` (multi-mode same-site annihilation-number
identity). -/
theorem fermionMultiAnnihilation_mul_fermionMultiNumber_eq_fermionMultiAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiNumber N i =
      fermionMultiAnnihilation N i := by
  -- c_i · n_i = c_i · (c_i† · c_i) = (c_i · c_i†) · c_i
  --          = (1 − n_i) · c_i = c_i − n_i · c_i = c_i.
  rw [show fermionMultiNumber N i =
      fermionMultiCreation N i * fermionMultiAnnihilation N i from rfl,
    ← Matrix.mul_assoc,
    fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number,
    sub_mul, Matrix.one_mul,
    fermionMultiNumber_mul_fermionMultiAnnihilation_eq_zero, sub_zero]

end LatticeSystem.Fermion
