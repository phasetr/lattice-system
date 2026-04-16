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

/-! ## Combined 2D integral: SU(2) volume in Euler angles -/

/-- `∫ φ in 0..2π, ∫ θ in 0..π, sin θ = 4π`. This is the total volume
of the SU(2) parameter space in Euler-angle coordinates. -/
theorem integral_sin_two_pi_pi :
    ∫ _φ in (0 : ℝ)..(2 * Real.pi),
      ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 4 * Real.pi := by
  simp only [integral_sin_zero_pi]
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]; ring

/-! ## Half-angle integrals for the θ component of Problem 2.2.c

`sin θ cos²(θ/2) = (sin θ + sin θ cos θ) / 2 = (sin θ) / 2 + (sin 2θ) / 4`
and similarly for `sin²(θ/2)`. Integrated over `[0, π]`, the `sin 2θ`
term vanishes and the `sin θ` term gives 1 for each. -/

/-- `∫ θ in 0..π, sin θ · cos θ = 0`. Antiderivative: `sin²(θ)/2`. -/
theorem integral_sin_mul_cos_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.cos θ = 0 := by
  have key : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun x => (Real.sin x) ^ 2 / 2) (Real.sin x * Real.cos x) x := by
    intros x _
    have h := (Real.hasDerivAt_sin x).pow 2
    convert h.div_const 2 using 1
    ring
  have hint : IntervalIntegrable (fun x => Real.sin x * Real.cos x)
      MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key hint]
  simp [Real.sin_pi, Real.sin_zero]

/-- `∫ θ in 0..π, sin θ · cos²(θ/2) = 1`. Uses the half-angle identity
`cos²(θ/2) = (1 + cos θ) / 2` and the vanishing of `∫ sin θ cos θ`. -/
theorem integral_sin_mul_cos_sq_half_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ * Real.cos (θ / 2) ^ 2 = 1 := by
  have hid : ∀ θ : ℝ, Real.sin θ * Real.cos (θ / 2) ^ 2 =
      (1 / 2) * Real.sin θ + (1 / 2) * (Real.sin θ * Real.cos θ) := by
    intro θ
    have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (θ / 2)
      rwa [show 2 * (θ / 2) = θ from by ring] at h
    linear_combination -(1 / 2) * Real.sin θ * hcos
  conv_lhs => arg 1; ext θ; rw [hid θ]
  have h1 : IntervalIntegrable (fun θ => (1/2 : ℝ) * Real.sin θ) MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.const_mul _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => (1/2 : ℝ) * (Real.sin θ * Real.cos θ))
      MeasureTheory.volume 0 Real.pi :=
    ((Real.continuous_sin.mul Real.continuous_cos).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sin_zero_pi, integral_sin_mul_cos_zero_pi]
  ring

/-- `∫ θ in 0..π, sin θ · sin²(θ/2) = 1`. Uses the half-angle identity
`sin²(θ/2) = (1 - cos θ) / 2`. -/
theorem integral_sin_mul_sin_sq_half_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ * Real.sin (θ / 2) ^ 2 = 1 := by
  have hid : ∀ θ : ℝ, Real.sin θ * Real.sin (θ / 2) ^ 2 =
      (1 / 2) * Real.sin θ - (1 / 2) * (Real.sin θ * Real.cos θ) := by
    intro θ
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h := Real.cos_two_mul' (θ / 2)
      rw [show 2 * (θ / 2) = θ from by ring] at h
      linear_combination h + Real.sin_sq_add_cos_sq (θ / 2)
    linear_combination (1 / 2) * Real.sin θ * hcos
  conv_lhs => arg 1; ext θ; rw [hid θ]
  have h1 : IntervalIntegrable (fun θ => (1/2 : ℝ) * Real.sin θ) MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.const_mul _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => (1/2 : ℝ) * (Real.sin θ * Real.cos θ))
      MeasureTheory.volume 0 Real.pi :=
    ((Real.continuous_sin.mul Real.continuous_cos).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sin_zero_pi, integral_sin_mul_cos_zero_pi]
  ring

end LatticeSystem.Quantum
