import LatticeSystem.Fermion.Mode

/-!
# `c · c†` is Hermitian

The hole-occupation operator `c · c†` is Hermitian:

  `(c · c†)ᴴ = c · c†`.

Direct from `cᴴ = c†` (`fermionAnnihilation_conjTranspose`) and
`(c†)ᴴ = c` (`fermionCreation_conjTranspose`):
`(c · c†)ᴴ = (c†)ᴴ · cᴴ = c · c†`.

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix

/-- `c · c†` is Hermitian. -/
theorem fermionAnnihilation_mul_fermionCreation_isHermitian :
    (fermionAnnihilation * fermionCreation).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul,
    fermionAnnihilation_conjTranspose,
    fermionCreation_conjTranspose]

end LatticeSystem.Fermion
