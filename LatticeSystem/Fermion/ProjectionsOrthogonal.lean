import LatticeSystem.Fermion.Mode

/-!
# `n` and `c · c†` are orthogonal projections

The number operator `n = c† · c` and the hole operator `c · c†`
are orthogonal projections:

  `n · (c · c†) = 0`,
  `(c · c†) · n = 0`.

Direct from `c² = 0` (`fermionAnnihilation_sq`) and
`(c†)² = 0` (`fermionCreation_sq`):
- `n · (c · c†) = (c† · c) · (c · c†) = c† · c² · c† = c† · 0 · c† = 0`.
- `(c · c†) · n = (c · c†) · (c† · c) = c · (c†)² · c = c · 0 · c = 0`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `n · (c · c†) = 0`. -/
theorem fermionNumber_mul_fermionAnnihilation_mul_fermionCreation_eq_zero :
    fermionNumber * (fermionAnnihilation * fermionCreation) = 0 := by
  rw [fermionNumber_eq_creation_mul_annihilation]
  -- (c† · c) · (c · c†) = c† · ((c · c) · c†)
  --                     = c† · (0 · c†) = c† · 0 = 0.
  rw [mul_assoc fermionCreation fermionAnnihilation
        (fermionAnnihilation * fermionCreation),
    ← mul_assoc fermionAnnihilation fermionAnnihilation fermionCreation,
    fermionAnnihilation_sq, Matrix.zero_mul, Matrix.mul_zero]

/-- `(c · c†) · n = 0`. -/
theorem fermionAnnihilation_mul_fermionCreation_mul_fermionNumber_eq_zero :
    (fermionAnnihilation * fermionCreation) * fermionNumber = 0 := by
  rw [fermionNumber_eq_creation_mul_annihilation]
  -- (c · c†) · (c† · c) = c · ((c† · c†) · c)
  --                     = c · (0 · c) = c · 0 = 0.
  rw [mul_assoc fermionAnnihilation fermionCreation
        (fermionCreation * fermionAnnihilation),
    ← mul_assoc fermionCreation fermionCreation fermionAnnihilation,
    fermionCreation_sq, Matrix.zero_mul, Matrix.mul_zero]

end LatticeSystem.Fermion
