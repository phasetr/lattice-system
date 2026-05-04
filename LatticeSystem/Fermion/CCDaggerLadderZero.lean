import LatticeSystem.Fermion.Mode

/-!
# Single-mode fermion ladder-on-hole-projection vanishing
`c · (c · c†) = 0` and `(c · c†) · c† = 0`

For the single-mode fermion the products

  `c · (c · c†) = 0`,
  `(c · c†) · c† = 0`.

Direct from `c² = 0` (`fermionAnnihilation_sq`) and
`(c†)² = 0` (`fermionCreation_sq`):

- `c · (c · c†)  = (c · c) · c† = 0 · c† = 0`.
- `(c · c†) · c† = c · (c† · c†) = c · 0 = 0`.

These complete the four-way breakdown of left/right
multiplication of the hole projection `c · c†` by the ladder
operators; the non-zero pair are
`(c · c†) · c = c` (PR #982) and `c† · (c · c†) = c†` (PR #984).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `c · (c · c†) = 0` (annihilation kills the hole projection
on the left). -/
theorem fermionAnnihilation_mul_fermionAnnihilation_mul_fermionCreation_eq_zero :
    fermionAnnihilation * (fermionAnnihilation * fermionCreation) = 0 := by
  rw [← Matrix.mul_assoc, fermionAnnihilation_sq, Matrix.zero_mul]

/-- `(c · c†) · c† = 0` (creation kills the hole projection on
the right). -/
theorem fermionAnnihilation_mul_fermionCreation_mul_fermionCreation_eq_zero :
    (fermionAnnihilation * fermionCreation) * fermionCreation = 0 := by
  rw [Matrix.mul_assoc, fermionCreation_sq, Matrix.mul_zero]

end LatticeSystem.Fermion
