import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity
import LatticeSystem.Fermion.JordanWigner.Number

/-!
# Cross-site multi-mode hole projection commutes with ladder operators
`Commute (c_i · c_i†) c_j` and `Commute (c_i · c_i†) c_j†` for `i ≠ j`

For distinct sites `i ≠ j` the multi-mode hole projection
`c_i · c_i† = 1 − n_i` commutes with the ladder operators at
site `j`:

  `Commute (c_i · c_i†) c_j`  for `i ≠ j`,
  `Commute (c_i · c_i†) c_j†` for `i ≠ j`.

Both reduce, via `c_i · c_i† = 1 − n_i` (PR #996), to the
existing
- `fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne`,
- `fermionMultiNumber_commute_fermionMultiCreation_of_ne`
(`Fermion/JordanWigner/Number.lean`).

These complete the cross-site commutation picture for hole
projections versus the four ladder building blocks.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- For `i ≠ j`, `Commute (c_i · c_i†) c_j`. -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiAnnihilation_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute
      (fermionMultiAnnihilation N i * fermionMultiCreation N i)
      (fermionMultiAnnihilation N j) := by
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hij).eq
  -- Goal: (1 - n_i) * c_j = c_j * (1 - n_i)
  rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

/-- For `i ≠ j`, `Commute (c_i · c_i†) c_j†`. -/
theorem fermionMultiAnnihilation_mul_fermionMultiCreation_commute_fermionMultiCreation_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute
      (fermionMultiAnnihilation N i * fermionMultiCreation N i)
      (fermionMultiCreation N j) := by
  rw [fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
  unfold Commute SemiconjBy
  have hcomm := (fermionMultiNumber_commute_fermionMultiCreation_of_ne hij).eq
  rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]

end LatticeSystem.Fermion
