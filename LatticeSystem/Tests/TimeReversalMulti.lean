/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TimeReversalMulti

/-!
# Test coverage for the multi-spin time-reversal map (Tasaki §2.3)
-/

namespace LatticeSystem.Tests.TimeReversalMulti

open LatticeSystem.Quantum

/-! ## `flipConfig` -/

example (σ : Fin 3 → Fin 2) (x : Fin 3) :
    flipConfig σ x = 1 - σ x := rfl

example (σ : Fin 3 → Fin 2) :
    flipConfig (flipConfig σ) = σ :=
  flipConfig_involutive σ

/-! ## `timeReversalSign` -/

example : timeReversalSign (0 : Fin 2) = 1 := timeReversalSign_zero
example : timeReversalSign (1 : Fin 2) = -1 := timeReversalSign_one

example (s : Fin 2) :
    timeReversalSign s * timeReversalSign (1 - s) = -1 :=
  timeReversalSign_mul_flip s

/-! ## Multi-spin Kramers degeneracy `Θ̂_tot² = (-1)^|Λ| · 1̂` -/

example (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) =
      ((-1 : ℂ) ^ (Fintype.card (Fin 3))) • v :=
  timeReversalSpinHalfMulti_sq v

example (v : (Fin 4 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) =
      ((-1 : ℂ) ^ (Fintype.card (Fin 4))) • v :=
  timeReversalSpinHalfMulti_sq v

/-- Specialisation: at `|Λ| = 3` (odd), `Θ̂_tot² = -1̂`. -/
example (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) = -v := by
  rw [timeReversalSpinHalfMulti_sq]
  simp [Fintype.card_fin, show ((-1 : ℂ) ^ 3) = -1 from by norm_num]

/-- Specialisation: at `|Λ| = 4` (even), `Θ̂_tot² = +1̂`. -/
example (v : (Fin 4 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) = v := by
  rw [timeReversalSpinHalfMulti_sq]
  simp [Fintype.card_fin, show ((-1 : ℂ) ^ 4) = 1 from by norm_num]

/-! ## `Θ̂_tot` action on basis states -/

example (σ : Fin 3 → Fin 2) :
    timeReversalSpinHalfMulti (basisVec σ) =
      (∏ x : Fin 3, timeReversalSign (flipConfig σ x)) •
        basisVec (flipConfig σ) :=
  timeReversalSpinHalfMulti_basisVec σ

/-! ## Multi-site σ^z sign-flip equivariance -/

example (x : Fin 3) (v : (Fin 3 → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliZ).mulVec v) =
      (-(onSite x pauliZ)).mulVec (timeReversalSpinHalfMulti v) :=
  timeReversalSpinHalfMulti_onSite_pauliZ_mulVec x v

end LatticeSystem.Tests.TimeReversalMulti
