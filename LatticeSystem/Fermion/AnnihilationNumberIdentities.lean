import LatticeSystem.Fermion.Mode

/-!
# Fermion `c · n` and `n · c` identities

For the single-mode fermion:

- `n · c = 0` (annihilation kills the occupied component).
- `c · n = c` (annihilation followed by number = annihilation).

Proofs use `c² = 0` (`fermionAnnihilation_sq`) and the
anticommutation `c · c† + c† · c = 1` (`fermionAnticomm_self`):

- `n · c = (c† · c) · c = c† · (c · c) = c† · 0 = 0`.
- `c · n = c · (c† · c) = (c · c†) · c = (1 − n) · c = c − n · c = c`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `n · c = 0`. -/
theorem fermionNumber_mul_fermionAnnihilation_eq_zero :
    fermionNumber * fermionAnnihilation = 0 := by
  rw [fermionNumber_eq_creation_mul_annihilation,
    mul_assoc, fermionAnnihilation_sq, Matrix.mul_zero]

/-- `c · n = c`. -/
theorem fermionAnnihilation_mul_fermionNumber_eq_fermionAnnihilation :
    fermionAnnihilation * fermionNumber = fermionAnnihilation := by
  rw [fermionNumber_eq_creation_mul_annihilation, ← mul_assoc]
  -- Goal: (c · c†) · c = c.
  -- From anticomm: c · c† + c† · c = 1, so c · c† = 1 - c† · c = 1 - n.
  -- (c · c†) · c = (1 - n) · c = c - n · c = c - 0 = c.
  have hac := fermionAnticomm_self
  have hcc : fermionAnnihilation * fermionCreation =
      1 - fermionCreation * fermionAnnihilation := eq_sub_of_add_eq hac
  rw [hcc, sub_mul, one_mul]
  rw [show fermionCreation * fermionAnnihilation * fermionAnnihilation =
      fermionCreation * (fermionAnnihilation * fermionAnnihilation) from by
    rw [mul_assoc]]
  rw [fermionAnnihilation_sq, Matrix.mul_zero, sub_zero]

end LatticeSystem.Fermion
