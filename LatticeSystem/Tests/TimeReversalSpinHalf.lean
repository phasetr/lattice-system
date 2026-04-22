/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TimeReversalSpinHalf

/-!
# Test coverage for the single-spin time-reversal map (Tasaki §2.3)
-/

namespace LatticeSystem.Tests.TimeReversalSpinHalf

open LatticeSystem.Quantum Complex

/-! ## Action on basis states -/

example : timeReversalSpinHalf spinHalfUp = spinHalfDown :=
  timeReversalSpinHalf_spinHalfUp

example : timeReversalSpinHalf spinHalfDown = -spinHalfUp :=
  timeReversalSpinHalf_spinHalfDown

/-! ## Antilinearity -/

example (v w : Fin 2 → ℂ) :
    timeReversalSpinHalf (v + w) =
      timeReversalSpinHalf v + timeReversalSpinHalf w :=
  timeReversalSpinHalf_add v w

example (c : ℂ) (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (c • v) =
      (starRingEnd ℂ c) • timeReversalSpinHalf v :=
  timeReversalSpinHalf_smul c v

/-! ## Kramers degeneracy `Θ̂² = -1̂` -/

example (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (timeReversalSpinHalf v) = -v :=
  timeReversalSpinHalf_sq v

/-- Concrete instance of Kramers on `|↑⟩`: `Θ̂²|↑⟩ = -|↑⟩`. -/
example :
    timeReversalSpinHalf (timeReversalSpinHalf spinHalfUp) = -spinHalfUp :=
  timeReversalSpinHalf_sq spinHalfUp

/-! ## `Θ̂` flips the spin: `Θ̂ Ŝ^(α) Θ̂⁻¹ = -Ŝ^(α)` (equivariance form) -/

example (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (spinHalfOp1.mulVec v) =
      (-spinHalfOp1).mulVec (timeReversalSpinHalf v) :=
  timeReversalSpinHalf_spinHalfOp1_mulVec v

example (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (spinHalfOp2.mulVec v) =
      (-spinHalfOp2).mulVec (timeReversalSpinHalf v) :=
  timeReversalSpinHalf_spinHalfOp2_mulVec v

example (v : Fin 2 → ℂ) :
    timeReversalSpinHalf (spinHalfOp3.mulVec v) =
      (-spinHalfOp3).mulVec (timeReversalSpinHalf v) :=
  timeReversalSpinHalf_spinHalfOp3_mulVec v

end LatticeSystem.Tests.TimeReversalSpinHalf
