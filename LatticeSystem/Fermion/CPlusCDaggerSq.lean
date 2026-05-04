import LatticeSystem.Fermion.Mode

/-!
# Single-mode fermion `(c + c†)² = 1` (X-Pauli analog)

For the single-mode fermion the symmetric Hermitian combination
satisfies the involution identity

  `(c + c†)² = 1`.

Direct expansion:

  `(c + c†)² = c² + c·c† + c†·c + (c†)² = 0 + 1 + 0 = 1`

via `c² = 0` (`fermionAnnihilation_sq`), `(c†)² = 0`
(`fermionCreation_sq`), and `c·c† + c†·c = 1`
(`fermionAnticomm_self`).

Physics identification: `c = σ⁺` and `c† = σ⁻`, so
`c + c† = σ_x` (Pauli x-matrix) and `σ_x² = I`. Useful for
quench dynamics and Majorana decompositions.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `(c + c†)² = 1`: the symmetric Hermitian fermion combination
is an involution (single-mode `σ_x` analog). -/
theorem fermionAnnihilation_add_fermionCreation_sq :
    (fermionAnnihilation + fermionCreation) *
        (fermionAnnihilation + fermionCreation) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- Expand: (c + c†) * (c + c†) = c² + c·c† + c†·c + (c†)².
  rw [add_mul, mul_add, mul_add, fermionAnnihilation_sq,
    fermionCreation_sq, zero_add, add_zero]
  -- Goal: c·c† + c†·c = 1.
  exact fermionAnticomm_self

end LatticeSystem.Fermion
