import LatticeSystem.Fermion.JordanWigner.Number

/-!
# Cross-site `Commute n_i (c_j ± c_j†)` for `i ≠ j`

For distinct sites the per-site number operator commutes with
the cross-site Pauli-X/iY-analog operators:

  `Commute (n_i) (c_j + c_j†)`  for `i ≠ j`,
  `Commute (n_i) (c_j − c_j†)`  for `i ≠ j`.

Direct from
- `Commute n_i c_j`
  (`fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne`), and
- `Commute n_i c_j†`
  (`fermionMultiNumber_commute_fermionMultiCreation_of_ne`).

The combination commutes via `Commute.add_right` / `.sub_right`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute (n_i) (c_j + c_j†)` for `i ≠ j`. -/
theorem fermionMultiNumber_commute_fermionMultiPlus_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i)
      (fermionMultiAnnihilation N j + fermionMultiCreation N j) :=
  (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hij).add_right
    (fermionMultiNumber_commute_fermionMultiCreation_of_ne hij)

/-- `Commute (n_i) (c_j − c_j†)` for `i ≠ j`. -/
theorem fermionMultiNumber_commute_fermionMultiMinus_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i)
      (fermionMultiAnnihilation N j - fermionMultiCreation N j) :=
  (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hij).sub_right
    (fermionMultiNumber_commute_fermionMultiCreation_of_ne hij)

end LatticeSystem.Fermion
