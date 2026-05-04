import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity

/-!
# Multi-mode Jordan–Wigner hole-projection idempotency and powers

Multi-mode (Jordan–Wigner) mirror of single-mode PRs #974 and
(the second half of) #992: the same-site hole projection
`c_i · c_i† = 1 − n_i` is idempotent, and all positive powers
collapse to it.

  `(c_i · c_i†)² = c_i · c_i†`,
  `(c_i · c_i†)^(k+1) = c_i · c_i†`  for every `k : ℕ`.

The squared identity uses
- `c_i · c_i† = 1 − n_i` (PR #996), and
- `n_i² = n_i` (`fermionMultiNumber_sq`,
  `Fermion/JordanWigner/Operators.lean`),
giving `(1 − n_i)² = 1 − 2 n_i + n_i² = 1 − n_i`.
The power identity is then a direct induction in `k` from the
squared case.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `(c_i · c_i†)² = c_i · c_i†` (multi-mode hole projection is
idempotent). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_sq
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i * fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i * fermionMultiCreation N i) =
      fermionMultiAnnihilation N i * fermionMultiCreation N i := by
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
  -- Goal: (1 - n_i) * (1 - n_i) = 1 - n_i.
  have hn_sq := fermionMultiNumber_sq N i
  rw [show ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i) *
      ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i) =
      1 - fermionMultiNumber N i - fermionMultiNumber N i +
        fermionMultiNumber N i * fermionMultiNumber N i from by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel]
  rw [hn_sq]
  abel

/-- `(c_i · c_i†)^(k+1) = c_i · c_i†` for every `k : ℕ`
(multi-mode hole projection power identity). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_pow_succ
    (N : ℕ) (i : Fin (N + 1)) (k : ℕ) :
    (fermionMultiAnnihilation N i * fermionMultiCreation N i) ^ (k + 1) =
      fermionMultiAnnihilation N i * fermionMultiCreation N i := by
  induction k with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, fermionMultiAnnihilation_mul_fermionMultiCreation_sq]

end LatticeSystem.Fermion
