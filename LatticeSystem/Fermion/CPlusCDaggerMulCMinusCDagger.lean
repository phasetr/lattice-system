import LatticeSystem.Fermion.AnnihilationCreationIdentity

/-!
# Single-mode `(c + c†)(c − c†) = 2n − 1` and `(c − c†)(c + c†) = 1 − 2n`

For the single-mode fermion the Pauli-X-analog times the
iY-analog yields the negative-σ_z-analog (and the reverse the
positive-σ_z-analog):

  `(c + c†) · (c − c†) = 2 · n − 1`,
  `(c − c†) · (c + c†) = 1 − 2 · n`.

Direct expansion using `c² = (c†)² = 0`, `c·c† = 1 − n`
(PR #963), and `c†·c = n`:

  `(c + c†)(c − c†) = c² − c·c† + c†·c − (c†)²
                    = −(c·c† − c†·c)
                    = −((1 − n) − n)
                    = 2n − 1`.

Physics identification: `c + c† = σ_x` and `c − c† = i σ_y`,
so `(c + c†)(c − c†) = σ_x · i σ_y = i σ_x σ_y = i · iσ_z =
−σ_z`. In our convention `n = (I − σ_z)/2`, hence
`−σ_z = 2n − 1`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `(c + c†)(c − c†) = 2 · n − 1`. -/
theorem fermionAnnihilation_add_fermionCreation_mul_fermionAnnihilation_sub_fermionCreation :
    (fermionAnnihilation + fermionCreation) *
        (fermionAnnihilation - fermionCreation) =
      (2 : ℂ) • fermionNumber - 1 := by
  -- (c + c†)(c − c†) = c² − c·c† + c†·c − (c†)² = −(c·c† − c†·c).
  have hcc := fermionAnnihilation_mul_fermionCreation_eq_one_sub_number
  -- hcc : c · c† = 1 − n.
  have hn : fermionCreation * fermionAnnihilation =
      fermionNumber := fermionNumber_eq_creation_mul_annihilation.symm
  rw [add_mul, mul_sub, mul_sub, fermionAnnihilation_sq,
    fermionCreation_sq, hcc, hn]
  -- Goal: (0 - (1 - n)) + (n - 0) = 2 • n - 1.
  rw [show (2 : ℂ) • fermionNumber = fermionNumber + fermionNumber from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  abel

/-- `(c − c†)(c + c†) = 1 − 2 · n`. -/
theorem fermionAnnihilation_sub_fermionCreation_mul_fermionAnnihilation_add_fermionCreation :
    (fermionAnnihilation - fermionCreation) *
        (fermionAnnihilation + fermionCreation) =
      1 - (2 : ℂ) • fermionNumber := by
  have hcc := fermionAnnihilation_mul_fermionCreation_eq_one_sub_number
  have hn : fermionCreation * fermionAnnihilation =
      fermionNumber := fermionNumber_eq_creation_mul_annihilation.symm
  rw [sub_mul, mul_add, mul_add, fermionAnnihilation_sq,
    fermionCreation_sq, hcc, hn]
  rw [show (2 : ℂ) • fermionNumber = fermionNumber + fermionNumber from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  abel

end LatticeSystem.Fermion
