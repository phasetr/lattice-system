import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Cross-site multi-mode hopping bilinears commute with ladder operators
`Commute (c_i† · c_j) c_k` and `Commute (c_i† · c_j) c_k†` for `i ≠ k`, `j ≠ k`

A hopping bilinear `c_i† c_j` is an **even** element of the fermion algebra, so it commutes —
with no residual sign — with any ladder operator at a mode distinct from both `i` and `j`:

  `Commute (c_i† · c_j) c_k†` for `i ≠ k`, `j ≠ k`,
  `Commute (c_i† · c_j) c_k`  for `i ≠ k`, `j ≠ k`.

Each follows by anticommuting the ladder operator past the two factors in turn (the cross-site
`_of_ne` relations of `CAR/CrossSiteOfNe.lean`); the two sign flips cancel.  This is the
even-operator companion of `HoleProjectionCommuteLadder.lean`, which records the same phenomenon
for the hole projection `c_i c_i†`.

The identities are the algebraic content behind "a spin-`σ` hopping term passes through a
spin-`τ` creation operator untouched" once the two spin species sit at distinct Jordan–Wigner
modes, and they hold for arbitrary distinct single-species modes.
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum

/-- For `i ≠ k` and `j ≠ k`, the hopping bilinear `c_i† c_j` commutes with `c_k†`. -/
theorem fermionMultiHopping_commute_fermionMultiCreation_of_ne
    {N : ℕ} {i j k : Fin (N + 1)} (hik : i ≠ k) (hjk : j ≠ k) :
    Commute (fermionMultiCreation N i * fermionMultiAnnihilation N j)
      (fermionMultiCreation N k) := by
  have h1 : fermionMultiAnnihilation N j * fermionMultiCreation N k
      = -(fermionMultiCreation N k * fermionMultiAnnihilation N j) :=
    eq_neg_of_add_eq_zero_left (fermionMultiAnnihilation_creation_anticomm_of_ne hjk)
  have h2 : fermionMultiCreation N i * fermionMultiCreation N k
      = -(fermionMultiCreation N k * fermionMultiCreation N i) :=
    eq_neg_of_add_eq_zero_left (fermionMultiCreation_anticomm_of_ne hik)
  unfold Commute SemiconjBy
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul,
    Matrix.mul_assoc]
  -- `rw [neg_neg]` does not fire on `ManyBodyOp`-valued double negations.
  exact neg_neg _

/-- For `i ≠ k` and `j ≠ k`, the hopping bilinear `c_i† c_j` commutes with `c_k`. -/
theorem fermionMultiHopping_commute_fermionMultiAnnihilation_of_ne
    {N : ℕ} {i j k : Fin (N + 1)} (hik : i ≠ k) (hjk : j ≠ k) :
    Commute (fermionMultiCreation N i * fermionMultiAnnihilation N j)
      (fermionMultiAnnihilation N k) := by
  have h1 : fermionMultiAnnihilation N j * fermionMultiAnnihilation N k
      = -(fermionMultiAnnihilation N k * fermionMultiAnnihilation N j) :=
    eq_neg_of_add_eq_zero_left (fermionMultiAnnihilation_anticomm_of_ne hjk)
  have h2 : fermionMultiCreation N i * fermionMultiAnnihilation N k
      = -(fermionMultiAnnihilation N k * fermionMultiCreation N i) :=
    eq_neg_of_add_eq_zero_left (fermionMultiCreation_annihilation_anticomm_of_ne hik)
  unfold Commute SemiconjBy
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul,
    Matrix.mul_assoc]
  exact neg_neg _

end LatticeSystem.Fermion
