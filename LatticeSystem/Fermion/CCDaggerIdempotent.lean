import LatticeSystem.Fermion.AnnihilationCreationIdentity

/-!
# `c · c†` is idempotent

The hole occupation operator `c · c† = 1 − n` is idempotent:

  `(c · c†)² = c · c†`.

Direct from `c · c† = 1 − n` (PR #963) and `n² = n`
(`fermionNumber_sq`):
`(1 − n)² = 1 − 2n + n² = 1 − 2n + n = 1 − n`.

The two complementary projections `n` and `c · c†` together form
the resolution of identity (PR #972): `n + c · c† = 1`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `(c · c†)² = c · c†` (idempotent projection). -/
theorem fermionAnnihilation_mul_fermionCreation_sq :
    (fermionAnnihilation * fermionCreation) *
        (fermionAnnihilation * fermionCreation) =
      fermionAnnihilation * fermionCreation := by
  rw [fermionAnnihilation_mul_fermionCreation_eq_one_sub_number]
  -- Goal: (1 - n) * (1 - n) = 1 - n.
  have hn_sq := fermionNumber_sq
  -- hn_sq : fermionNumber * fermionNumber = fermionNumber.
  rw [show ((1 : Matrix (Fin 2) (Fin 2) ℂ) - fermionNumber) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - fermionNumber) =
      1 - fermionNumber - fermionNumber + fermionNumber * fermionNumber from by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    abel]
  rw [hn_sq]
  abel

end LatticeSystem.Fermion
