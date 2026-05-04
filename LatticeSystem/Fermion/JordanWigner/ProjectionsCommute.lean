import LatticeSystem.Fermion.JordanWigner.ProjectionsOrthogonal

/-!
# Multi-mode Jordan–Wigner projections commute
`Commute n_i (c_i · c_i†)`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #978. The
orthogonality results of PR #999 imply that `n_i` and
`c_i · c_i†` commute trivially: both `n_i · (c_i · c_i†)` and
`(c_i · c_i†) · n_i` equal `0`.

  `Commute n_i (c_i · c_i†)`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- `Commute n_i (c_i · c_i†)` (both products are zero, hence
equal). -/
theorem fermionMultiNumber_commute_fermionMultiAnnihilation_mul_fermionMultiCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionMultiNumber N i)
      (fermionMultiAnnihilation N i * fermionMultiCreation N i) := by
  unfold Commute SemiconjBy
  rw [fermionMultiNumber_mul_fermionMultiAnnihilation_mul_fermionMultiCreation_eq_zero,
    fermionMultiAnnihilation_mul_fermionMultiCreation_mul_fermionMultiNumber_eq_zero]

end LatticeSystem.Fermion
