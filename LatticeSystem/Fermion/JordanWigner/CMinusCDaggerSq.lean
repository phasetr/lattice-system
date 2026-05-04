import LatticeSystem.Fermion.JordanWigner.CAR.SameSite

/-!
# Multi-mode Jordan–Wigner `(c_i - c_i†)² = -1`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #1023:

  `(c_i − c_i†)² = −1`.

Direct expansion `(c_i − c_i†)² = c_i² − c_i·c_i† − c_i†·c_i +
(c_i†)² = −(c_i·c_i† + c_i†·c_i) = −1` via
- `c_i² = 0` (`fermionMultiAnnihilation_sq`),
- `(c_i†)² = 0` (`fermionMultiCreation_sq`),
- `c_i·c_i† + c_i†·c_i = 1` (`fermionMultiAnticomm_self`).

Companion to PR #1022 (`(c_i + c_i†)² = 1`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `(c_i - c_i†)² = -1`: multi-mode JW antisymmetric
anti-Hermitian combination squares to `-1`. -/
theorem fermionMultiAnnihilation_sub_fermionMultiCreation_sq
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i - fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i - fermionMultiCreation N i) =
      -(1 : ManyBodyOp (Fin (N + 1))) := by
  have hac := fermionMultiAnticomm_self N i
  rw [sub_mul, mul_sub, mul_sub, fermionMultiAnnihilation_sq,
    fermionMultiCreation_sq]
  rw [show (0 : ManyBodyOp (Fin (N + 1))) -
        fermionMultiAnnihilation N i * fermionMultiCreation N i -
        (fermionMultiCreation N i * fermionMultiAnnihilation N i - 0) =
      -(fermionMultiAnnihilation N i * fermionMultiCreation N i +
        fermionMultiCreation N i * fermionMultiAnnihilation N i) from by abel]
  rw [hac]

end LatticeSystem.Fermion
