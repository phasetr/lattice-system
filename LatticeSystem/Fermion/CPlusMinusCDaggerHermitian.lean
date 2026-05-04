import LatticeSystem.Fermion.CPlusCDaggerMulCMinusCDagger

/-!
# Single-mode `(c + c†)` Hermitian, `(c − c†)` anti-Hermitian, anticommute

Hermiticity / anti-Hermiticity / anticommutation structure of
the symmetric and antisymmetric Pauli-analog combinations:

  `(c + c†).IsHermitian`,
  `(c − c†)ᴴ = −(c − c†)`  (anti-Hermitian),
  `(c + c†)(c − c†) + (c − c†)(c + c†) = 0`.

The first two follow from `cᴴ = c†`
(`fermionAnnihilation_conjTranspose`) and `(c†)ᴴ = c`
(`fermionCreation_conjTranspose`) via
`Matrix.conjTranspose_add`/`_sub`.

The anticommutator follows from PR #1025
(`(c + c†)(c − c†) = 2n − 1` and `(c − c†)(c + c†) = 1 − 2n`):
`(2n − 1) + (1 − 2n) = 0`.

Physics identification: `c + c† = σ_x` (Hermitian),
`c − c† = i σ_y` (anti-Hermitian), and `{σ_x, σ_y} = 0`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix

/-- `(c + c†).IsHermitian`: the symmetric combination is
Hermitian (single-mode `σ_x` analog). -/
theorem fermionAnnihilation_add_fermionCreation_isHermitian :
    (fermionAnnihilation + fermionCreation).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, fermionAnnihilation_conjTranspose,
    fermionCreation_conjTranspose, add_comm]

/-- `(c − c†)ᴴ = −(c − c†)`: the antisymmetric combination is
anti-Hermitian (single-mode `i σ_y` analog). -/
theorem fermionAnnihilation_sub_fermionCreation_conjTranspose :
    (fermionAnnihilation - fermionCreation)ᴴ =
      -(fermionAnnihilation - fermionCreation) := by
  rw [Matrix.conjTranspose_sub, fermionAnnihilation_conjTranspose,
    fermionCreation_conjTranspose]
  abel

/-- `{c + c†, c − c†} = 0`: the symmetric and antisymmetric
Pauli-analog combinations anticommute. -/
theorem fermionAnnihilation_add_fermionCreation_anticomm_fermionAnnihilation_sub_fermionCreation :
    (fermionAnnihilation + fermionCreation) *
        (fermionAnnihilation - fermionCreation) +
      (fermionAnnihilation - fermionCreation) *
        (fermionAnnihilation + fermionCreation) =
      0 := by
  rw [fermionAnnihilation_add_fermionCreation_mul_fermionAnnihilation_sub_fermionCreation,
    fermionAnnihilation_sub_fermionCreation_mul_fermionAnnihilation_add_fermionCreation]
  abel

end LatticeSystem.Fermion
