/-
Pinch coefficient match for the sphere-moment / multinomial identity.

This file proves the scalar arithmetic identity that reconciles the doubled-count multinomial
multiplicity and the odd double-factorial sphere moment with the plain multinomial coefficient, up
to the universal factor `4π / (2M+1)` (with `M = ∑ i, h i`):

`multinomial(2h) · (4π · ∏(2hᵢ-1)‼ / (2M+1)‼) = (4π / (2M+1)) · multinomial(h)`.

It is the arithmetic capstone (§2.4) of the Prop 4.10 (Tasaki §4.2.2, p. 108) pinch estimate.  The
natural-number division hidden inside `Nat.multinomial` is avoided by clearing denominators with
`Nat.multinomial_spec` (product form) and `two_mul_factorial_eq`; the powers of two on the two sides
cancel, reducing the whole statement to a single natural-number equation cast into `ℝ`.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §4.2.2, p. 108.
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LatticeSystem.Math.DoubleFactorial

namespace LatticeSystem.Math

open Finset
open scoped Nat

/-- **Pinch coefficient match** (Tasaki §4.2.2, p. 108, eqs. (4.2.58)/(4.2.59)):
for a `Fin 3` count vector `h`, with `M = ∑ i, h i`,
`multinomial(2h) · (4π · ∏(2hᵢ-1)‼ / (2M+1)‼) = (4π / (2M+1)) · multinomial(h)`.

The doubled-count multinomial multiplicity times the odd double-factorial sphere moment equals the
plain multinomial coefficient up to the universal `4π / (2M+1)` factor.  The proof establishes the
underlying natural-number identity
`multinomial(2h) · ∏(2hᵢ-1)‼ · (2M+1) = multinomial(h) · (2M+1)‼`
by multiplying both sides by `2^M · ∏ hᵢ!` (positive) and recognising each side as `(2M+1)!`
via `Nat.multinomial_spec`, `two_mul_factorial_eq`, `Nat.doubleFactorial_two_mul` and
`Nat.factorial_eq_mul_doubleFactorial`; the real identity then follows by clearing the two
positive denominators. -/
theorem pinch_coeff_match (h : Fin 3 → ℕ) :
    (Nat.multinomial Finset.univ (fun i => 2 * h i) : ℝ)
        * (4 * Real.pi * ((∏ i, ((2 * h i - 1)‼ : ℕ)) : ℝ) / (((2 * (∑ i, h i)) + 1)‼ : ℝ))
      = (4 * Real.pi / ((2 * (∑ i, h i)) + 1)) * (Nat.multinomial Finset.univ h : ℝ) := by
  set M := ∑ i, h i with hM
  -- Positivity of the two multipliers used to cancel the natural-number division.
  have hPh_pos : 0 < ∏ i, (h i)! := Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have hpow_pos : 0 < 2 ^ M := pow_pos (by norm_num) M
  have hmul_pos : 0 < 2 ^ M * ∏ i, (h i)! := Nat.mul_pos hpow_pos hPh_pos
  -- Product form of the doubled even factorials:
  -- `∏ (2hᵢ)! = 2^M · ∏ hᵢ! · ∏ (2hᵢ-1)‼`.
  have hP2 : (∏ i, (2 * h i)!) = 2 ^ M * (∏ i, (h i)!) * (∏ i, (2 * h i - 1)‼) := by
    calc (∏ i, (2 * h i)!)
        = ∏ i, (2 ^ (h i) * (h i)! * (2 * h i - 1)‼) :=
          Finset.prod_congr rfl (fun i _ => two_mul_factorial_eq (h i))
      _ = (∏ i, 2 ^ (h i)) * (∏ i, (h i)!) * (∏ i, (2 * h i - 1)‼) := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      _ = 2 ^ M * (∏ i, (h i)!) * (∏ i, (2 * h i - 1)‼) := by
          rw [Finset.prod_pow_eq_pow_sum, ← hM]
  -- The `multinomial_spec` product identities at the doubled and plain counts.
  have hsum2 : (∑ i, 2 * h i) = 2 * M := by rw [← Finset.mul_sum, ← hM]
  have specA := Nat.multinomial_spec (univ : Finset (Fin 3)) (fun i => 2 * h i)
  have specB := Nat.multinomial_spec (univ : Finset (Fin 3)) h
  rw [hsum2] at specA
  rw [← hM] at specB
  -- Both sides of the natural-number identity, scaled by `2^M · ∏ hᵢ!`, equal `(2M+1)!`.
  have hL : (2 ^ M * (∏ i, (h i)!)) * (Nat.multinomial univ (fun i => 2 * h i)
        * (∏ i, (2 * h i - 1)‼) * (2 * M + 1)) = (2 * M + 1)! := by
    have : (2 ^ M * (∏ i, (h i)!)) * (Nat.multinomial univ (fun i => 2 * h i)
          * (∏ i, (2 * h i - 1)‼) * (2 * M + 1))
        = ((∏ i, (2 * h i)!) * Nat.multinomial univ (fun i => 2 * h i)) * (2 * M + 1) := by
      rw [hP2]; ring
    rw [this, specA, Nat.factorial_succ]; ring
  have hR : (2 ^ M * (∏ i, (h i)!)) * (Nat.multinomial univ h * ((2 * M + 1)‼))
      = (2 * M + 1)! := by
    have e1 : (2 ^ M * (∏ i, (h i)!)) * (Nat.multinomial univ h * ((2 * M + 1)‼))
        = (2 * M + 1)‼ * (2 ^ M * ((∏ i, (h i)!) * Nat.multinomial univ h)) := by ring
    rw [e1, specB, ← Nat.doubleFactorial_two_mul M,
      ← Nat.factorial_eq_mul_doubleFactorial (2 * M)]
  -- Cancel the positive multiplier to obtain the key natural-number identity.
  have key : Nat.multinomial univ (fun i => 2 * h i) * (∏ i, (2 * h i - 1)‼) * (2 * M + 1)
      = Nat.multinomial univ h * ((2 * M + 1)‼) :=
    Nat.eq_of_mul_eq_mul_left hmul_pos (hL.trans hR.symm)
  -- Transport to `ℝ`; the per-letter double factorials are cast pointwise.
  have keyReal : (Nat.multinomial univ (fun i => 2 * h i) : ℝ)
        * (∏ i, ((2 * h i - 1)‼ : ℝ)) * (2 * (M : ℝ) + 1)
      = (Nat.multinomial univ h : ℝ) * (((2 * M + 1)‼ : ℕ) : ℝ) := by
    exact_mod_cast key
  have hDFne : (((2 * M + 1)‼ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * M + 1)).ne'
  have hEne : (2 * (M : ℝ) + 1) ≠ 0 := by positivity
  -- Clear the two positive denominators and close with the real identity.
  field_simp
  linear_combination keyReal

end LatticeSystem.Math
