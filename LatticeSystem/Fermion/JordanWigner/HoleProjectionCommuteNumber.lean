import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity
import LatticeSystem.Fermion.JordanWigner.CAR.SameSite

/-!
# Multi-mode Jordan–Wigner hole projection commutes with number operator
`Commute (c_i · c_i†) n_j` and `Commute n_i (c_j · c_j†)`

Mixed-form siblings of PR #1004
(`Commute (c_i · c_i†) (c_j · c_j†)`):

  `Commute (c_i · c_i†) n_j`  for any `i, j`,
  `Commute n_i (c_j · c_j†)`  for any `i, j`.

Direct from `c_i · c_i† = 1 − n_i` (PR #996) and
`Commute n_i n_j` (`fermionMultiNumber_commute`,
`Fermion/JordanWigner/CAR/SameSite.lean`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute (c_i · c_i†) n_j` for any `i, j`. -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiNumber
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute
      (fermionMultiAnnihilation N i * fermionMultiCreation N i)
      (fermionMultiNumber N j) := by
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
  unfold Commute SemiconjBy
  -- (1 - n_i) * n_j = n_j * (1 - n_i): expand both sides.
  have hcomm := (fermionMultiNumber_commute N i j).eq
  rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

/-- `Commute n_i (c_j · c_j†)` for any `i, j` (symmetric form of
the above). -/
theorem fermionMultiNumber_commute_fermionMultiAnnihilation_mul_fermionMultiCreation_any
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute
      (fermionMultiNumber N i)
      (fermionMultiAnnihilation N j * fermionMultiCreation N j) :=
  (fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiNumber N j i).symm

end LatticeSystem.Fermion
