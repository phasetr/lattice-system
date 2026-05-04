import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity

/-!
# Multi-mode Jordan–Wigner `(c_i ± c_i†)` Pauli-analog structure

Multi-mode mirrors of single-mode PRs #1025 and #1026:

  `(c_i + c_i†)(c_i − c_i†) = 2 · n_i − 1`,
  `(c_i − c_i†)(c_i + c_i†) = 1 − 2 · n_i`,
  `(c_i + c_i†).IsHermitian`,
  `(c_i − c_i†)ᴴ = −(c_i − c_i†)`,
  `(c_i + c_i†)(c_i − c_i†) + (c_i − c_i†)(c_i + c_i†) = 0`.

Direct expansion using `c_i² = (c_i†)² = 0`,
`c_i · c_i† = 1 − n_i` (PR #996), `c_i† · c_i = n_i`
(definitional), and `Matrix.conjTranspose_add` / `_sub` with the
existing `fermionMultiAnnihilation_conjTranspose` and
`fermionMultiCreation_conjTranspose`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- `(c_i + c_i†)(c_i − c_i†) = 2 · n_i − 1`. -/
theorem fermionMultiPlus_mul_fermionMultiMinus
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i + fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i - fermionMultiCreation N i) =
      (2 : ℂ) • fermionMultiNumber N i - 1 := by
  have hcc := fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number N i
  rw [add_mul, mul_sub, mul_sub, fermionMultiAnnihilation_sq,
    fermionMultiCreation_sq, hcc,
    show fermionMultiCreation N i * fermionMultiAnnihilation N i =
      fermionMultiNumber N i from rfl]
  rw [show (2 : ℂ) • fermionMultiNumber N i =
      fermionMultiNumber N i + fermionMultiNumber N i from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  abel

/-- `(c_i − c_i†)(c_i + c_i†) = 1 − 2 · n_i`. -/
theorem fermionMultiMinus_mul_fermionMultiPlus
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i - fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i + fermionMultiCreation N i) =
      1 - (2 : ℂ) • fermionMultiNumber N i := by
  have hcc := fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number N i
  rw [sub_mul, mul_add, mul_add, fermionMultiAnnihilation_sq,
    fermionMultiCreation_sq, hcc,
    show fermionMultiCreation N i * fermionMultiAnnihilation N i =
      fermionMultiNumber N i from rfl]
  rw [show (2 : ℂ) • fermionMultiNumber N i =
      fermionMultiNumber N i + fermionMultiNumber N i from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  abel

/-- `(c_i + c_i†).IsHermitian`. -/
theorem fermionMultiAnnihilation_add_fermionMultiCreation_isHermitian
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i + fermionMultiCreation N i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose]
  abel

/-- `(c_i − c_i†)ᴴ = −(c_i − c_i†)`. -/
theorem fermionMultiAnnihilation_sub_fermionMultiCreation_conjTranspose
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i - fermionMultiCreation N i)ᴴ =
      -(fermionMultiAnnihilation N i - fermionMultiCreation N i) := by
  rw [Matrix.conjTranspose_sub, fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose]
  abel

/-- `{c_i + c_i†, c_i − c_i†} = 0`. -/
theorem fermionMultiPlus_anticomm_fermionMultiMinus
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i + fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i - fermionMultiCreation N i) +
      (fermionMultiAnnihilation N i - fermionMultiCreation N i) *
        (fermionMultiAnnihilation N i + fermionMultiCreation N i) =
      0 := by
  rw [fermionMultiPlus_mul_fermionMultiMinus,
    fermionMultiMinus_mul_fermionMultiPlus]
  abel

end LatticeSystem.Fermion
