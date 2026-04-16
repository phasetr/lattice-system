/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.ManyBody
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Trig-integral helpers for Tasaki §2.2 Problem 2.2.c

Concrete trig-integral evaluations needed for the SU(2)-averaged-state
computation (Tasaki §2.2, Problem 2.2.c, eq. (2.2.15)). These are
proved using mathlib's `intervalIntegral` and
`SpecialFunctions.Integrals`. Each is a thin wrapper around mathlib's
`integral_sin`, `integral_cos`, or `integral_sin_sq`/`integral_cos_sq`.

The full integral statement (Problem 2.2.c itself) will be assembled
from these helpers in a follow-up work item (B-3c).
-/

namespace LatticeSystem.Quantum

open MeasureTheory Real

/-! ## Standard trig integrals over one full period or half period -/

/-- `∫ φ in 0..2π, cos φ = 0`. -/
theorem integral_cos_zero_two_pi :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ = 0 := by
  rw [integral_cos]
  simp [Real.sin_two_pi, Real.sin_zero]

/-- `∫ φ in 0..2π, sin φ = 0`. -/
theorem integral_sin_zero_two_pi :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ = 0 := by
  rw [integral_sin]
  simp [Real.cos_two_pi, Real.cos_zero]

/-- `∫ θ in 0..π, sin θ = 2`. -/
theorem integral_sin_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 := by
  rw [integral_sin]
  simp [Real.cos_pi, Real.cos_zero]; ring

end LatticeSystem.Quantum
