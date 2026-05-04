import LatticeSystem.Fermion.JordanWigner.CAR.SameSite

/-!
# Multi-mode Jordan–Wigner hole-occupation identity
`c_i · c_i† = 1 − n_i` and `n_i + c_i · c_i† = 1`

Multi-mode (Jordan–Wigner) mirror of single-mode PRs #963 and
#972: the same-site hole-occupation identity and the
projection-sum / resolution of identity.

  `c_i · c_i† = 1 − n_i`,
  `n_i + c_i · c_i† = 1`.

Both follow from
- the same-site CAR `c_i · c_i† + c_i† · c_i = 1`
  (`fermionMultiAnticomm_self`,
  `Fermion/JordanWigner/CAR/SameSite.lean`), and
- the definitional `n_i = c_i† · c_i` (`fermionMultiNumber`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- `c_i · c_i† = 1 − n_i` (multi-mode hole-occupation identity). -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiCreation N i =
      1 - fermionMultiNumber N i := by
  have hac := fermionMultiAnticomm_self N i
  -- hac : c_i · c_i† + c_i† · c_i = 1.
  -- And n_i = c_i† · c_i (definitional).
  rw [show fermionMultiCreation N i * fermionMultiAnnihilation N i =
      fermionMultiNumber N i from rfl] at hac
  exact eq_sub_of_add_eq hac

/-- `n_i + c_i · c_i† = 1` (multi-mode resolution of identity in
the occupation basis). -/
theorem fermionMultiNumber_add_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i +
        fermionMultiAnnihilation N i * fermionMultiCreation N i =
      (1 : ManyBodyOp (Fin (N + 1))) := by
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
  abel

end LatticeSystem.Fermion
