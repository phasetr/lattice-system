import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Multi-mode Jordan–Wigner ladder-on-hole-projection vanishing
`c_i · (c_i · c_i†) = 0` and `(c_i · c_i†) · c_i† = 0`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #1009. The
two same-site identities

  `c_i · (c_i · c_i†)  = 0`,
  `(c_i · c_i†) · c_i† = 0`.

Direct from `c_i² = 0` (`fermionMultiAnnihilation_sq`) and
`(c_i†)² = 0` (`fermionMultiCreation_sq`):

- `c_i · (c_i · c_i†)  = (c_i · c_i) · c_i† = 0 · c_i† = 0`.
- `(c_i · c_i†) · c_i† = c_i · (c_i† · c_i†) = c_i · 0 = 0`.

Together with `(c_i · c_i†) · c_i = c_i` (PR #1001) and
`c_i† · (c_i · c_i†) = c_i†` (PR #1002) this is the full
four-way breakdown of left/right multiplication of the
multi-mode hole projection by the same-site ladder operators.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `c_i · (c_i · c_i†) = 0` (multi-mode annihilation kills the
hole projection on the left). -/
theorem fermionMultiAnnihilation_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i *
        (fermionMultiAnnihilation N i * fermionMultiCreation N i) =
      0 := by
  rw [← Matrix.mul_assoc, fermionMultiAnnihilation_sq, Matrix.zero_mul]

/-- `(c_i · c_i†) · c_i† = 0` (multi-mode creation kills the
hole projection on the right). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiCreation_eq_zero
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i * fermionMultiCreation N i) *
        fermionMultiCreation N i =
      0 := by
  rw [Matrix.mul_assoc, fermionMultiCreation_sq, Matrix.mul_zero]

end LatticeSystem.Fermion
