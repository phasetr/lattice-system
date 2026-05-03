import LatticeSystem.Fermion.AnnihilationNumberIdentities

/-!
# Fermion `c† · n` and `n · c†` identities

Companion to `AnnihilationNumberIdentities.lean`.

For the single-mode fermion:

- `c† · n = 0` (creation kills the vacuum component).
- `n · c† = c†` (number after creation = creation).

Proofs:

- `c† · n = c† · (c† · c) = (c†)² · c = 0 · c = 0`
  via `fermionCreation_sq`.
- `n · c† = (c† · c) · c† = c† · (c · c†) = c† · (1 − n)
       = c† − c† · n = c†`
  via `fermionAnticomm_self` (so `c · c† = 1 − n`)
  and the previous identity.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `c† · n = 0`. -/
theorem fermionCreation_mul_fermionNumber_eq_zero :
    fermionCreation * fermionNumber = 0 := by
  rw [fermionNumber_eq_creation_mul_annihilation,
    ← mul_assoc, fermionCreation_sq, Matrix.zero_mul]

/-- `n · c† = c†`. -/
theorem fermionNumber_mul_fermionCreation_eq_fermionCreation :
    fermionNumber * fermionCreation = fermionCreation := by
  rw [fermionNumber_eq_creation_mul_annihilation, mul_assoc]
  -- Goal: c† · (c · c†) = c†.
  -- From anticomm: c · c† = 1 - n.
  -- c† · (c · c†) = c† · (1 - n) = c† - c† · n = c† - 0 = c†.
  have hac := fermionAnticomm_self
  have hcc : fermionAnnihilation * fermionCreation =
      1 - fermionCreation * fermionAnnihilation := eq_sub_of_add_eq hac
  rw [hcc, mul_sub, mul_one]
  rw [show fermionCreation * (fermionCreation * fermionAnnihilation) =
      (fermionCreation * fermionCreation) * fermionAnnihilation from by
    rw [mul_assoc]]
  rw [fermionCreation_sq, Matrix.zero_mul, sub_zero]

end LatticeSystem.Fermion
