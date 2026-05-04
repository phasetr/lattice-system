import LatticeSystem.Fermion.Mode

/-!
# Single-mode fermion `(c - c†)² = -1` (iY-Pauli analog)

For the single-mode fermion the antisymmetric anti-Hermitian
combination satisfies

  `(c - c†)² = -1`.

Direct expansion:

  `(c - c†)² = c² - c·c† - c†·c + (c†)²
            = 0 - (c·c† + c†·c) + 0
            = -1`

via `c² = (c†)² = 0` (`fermionAnnihilation_sq`,
`fermionCreation_sq`) and `c·c† + c†·c = 1`
(`fermionAnticomm_self`).

Physics identification: `c - c† = σ⁺ - σ⁻ = i σ_y`, and
`(i σ_y)² = -σ_y² = -I`. Companion to PR #1021's
`(c + c†)² = 1`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `(c - c†)² = -1`: the antisymmetric anti-Hermitian fermion
combination squares to `-1` (single-mode `i σ_y` analog). -/
theorem fermionAnnihilation_sub_fermionCreation_sq :
    (fermionAnnihilation - fermionCreation) *
        (fermionAnnihilation - fermionCreation) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hac := fermionAnticomm_self
  -- (c - c†)² = c² - c·c† - c†·c + (c†)² = -(c·c† + c†·c) = -1.
  rw [sub_mul, mul_sub, mul_sub, fermionAnnihilation_sq,
    fermionCreation_sq]
  rw [show (0 : Matrix (Fin 2) (Fin 2) ℂ) -
        fermionAnnihilation * fermionCreation -
        (fermionCreation * fermionAnnihilation - 0) =
      -(fermionAnnihilation * fermionCreation +
        fermionCreation * fermionAnnihilation) from by abel]
  rw [hac]

end LatticeSystem.Fermion
