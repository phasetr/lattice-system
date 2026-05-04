import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Multi-mode Jordan–Wigner `(1 − 2 · n_i)² = 1` (σ_z analog involution)

Multi-mode mirror of single-mode PR #1028:

  `(1 − 2 · n_i)² = 1`.

Direct from `n_i² = n_i` (`fermionMultiNumber_sq`):
`(1 − 2n_i)² = 1 − 4n_i + 4n_i² = 1`.

Together with PR #1022 (`(c_i + c_i†)² = 1`) and PR #1024
(`(c_i − c_i†)² = -1`) this completes the multi-mode Pauli-trio
`σ_α² = ±1` involution identities.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `(1 − 2 · n_i)² = 1` (multi-mode JW `σ_z` analog
involution). -/
theorem one_sub_two_smul_fermionMultiNumber_sq
    (N : ℕ) (i : Fin (N + 1)) :
    ((1 : ManyBodyOp (Fin (N + 1))) - (2 : ℂ) • fermionMultiNumber N i) *
        (1 - (2 : ℂ) • fermionMultiNumber N i) =
      1 := by
  rw [show (2 : ℂ) • fermionMultiNumber N i =
      fermionMultiNumber N i + fermionMultiNumber N i from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  rw [show (1 - (fermionMultiNumber N i + fermionMultiNumber N i)) =
      (1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i -
        fermionMultiNumber N i from by abel]
  rw [show ((1 : ManyBodyOp (Fin (N + 1))) - fermionMultiNumber N i -
        fermionMultiNumber N i) *
        (1 - fermionMultiNumber N i - fermionMultiNumber N i) =
      1 - fermionMultiNumber N i - fermionMultiNumber N i -
        fermionMultiNumber N i - fermionMultiNumber N i +
        (fermionMultiNumber N i * fermionMultiNumber N i +
          fermionMultiNumber N i * fermionMultiNumber N i +
          (fermionMultiNumber N i * fermionMultiNumber N i +
            fermionMultiNumber N i * fermionMultiNumber N i)) from by
    rw [sub_mul, sub_mul, mul_sub, mul_sub, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel]
  rw [fermionMultiNumber_sq]
  abel

end LatticeSystem.Fermion
